//! Generate closed theorem statements and ask a pinned Lean release to check them.

use anyhow::{Context, Result, bail, ensure};
use std::{
    collections::BTreeSet,
    env,
    fs::{self, File},
    path::{Path, PathBuf},
    process::{Child, Command, Stdio},
    thread,
    time::{Duration, Instant},
};

#[cfg(unix)]
use std::os::unix::process::CommandExt;

mod upstream;
pub(crate) use upstream::{
    JumpPlan, MemoryPlan, PathLeafKind, RegionKind, SpanNode, SpanPlan, TerminalKind,
    check_jump_output, check_region_output, verify_region,
};

const LEAN_VERSION: &str = "4.34.0";
// Every generated certificate must check within this wall-clock budget.
const PROOF_TIMEOUT: Duration = Duration::from_secs(60);
// Expose shifts to ring reasoning without changing the claim or bytecode model.
// This width-general lemma includes the zero-width and wrapping cases.
pub(crate) const NORMALIZATION: &str = r#"namespace GolfProof
 theorem shift_one (x : BitVec w) : x <<< 1 = x * 2 := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp
 theorem shift_power (x : BitVec w) (n : Nat) :
     x <<< n = x * BitVec.ofNat w (2 ^ n) := by
   rw [BitVec.shiftLeft_eq_mul_twoPow]
   congr 1
   apply BitVec.eq_of_toNat_eq
   simp
end GolfProof
"#;

/// Check generated Lean source with the pinned toolchain inside the overall
/// proof budget, then require reports for exactly the expected theorems with
/// foundational axioms only.
pub(crate) fn verify_named(path: &Path, expected: &[String]) -> Result<String> {
    let local = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(".tools/lean/bin/lean");
    let lean = env::var_os("LEAN").map(PathBuf::from).unwrap_or_else(|| {
        if local.exists() {
            local
        } else {
            PathBuf::from("lean")
        }
    });
    let version = Command::new(&lean)
        .arg("--version")
        .output()
        .context("Lean not found; run scripts/setup-lean.sh or set LEAN")?;
    let version = String::from_utf8_lossy(&version.stdout).trim().to_owned();
    ensure!(
        version.contains(&format!("version {LEAN_VERSION},")),
        "expected Lean {LEAN_VERSION}, got: {version}"
    );
    let source = fs::read_to_string(path)?;
    let attempted = format!("-- Verification strategy: original.\n{source}");
    let attempt_path = path.with_extension("original.lean");
    let attempt_log = path.with_extension("original.log");
    fs::write(&attempt_path, &attempted)?;
    let result = run_attempt(
        &lean,
        &attempt_path,
        &attempt_log,
        Instant::now() + PROOF_TIMEOUT,
    );
    let output = fs::read_to_string(&attempt_log).unwrap_or_default();
    match result.and_then(|()| audit_axioms(&output, expected)) {
        Ok(()) => {
            fs::write(path, attempted)?;
            fs::write(path.with_extension("log"), output)?;
            Ok(version)
        }
        Err(error) => {
            fs::write(
                path.with_extension("log"),
                format!("original: {error}\n{output}"),
            )?;
            bail!(
                "Lean rejected the proof within the {}-second overall budget; see {}\noriginal: {error}",
                PROOF_TIMEOUT.as_secs(),
                path.with_extension("log").display()
            )
        }
    }
}

fn run_attempt(lean: &Path, path: &Path, log_path: &Path, deadline: Instant) -> Result<()> {
    let mut command = Command::new(lean);
    command.arg(path.canonicalize()?);
    run_command(&mut command, log_path, deadline)
}

fn run_command(command: &mut Command, log_path: &Path, deadline: Instant) -> Result<()> {
    let log = File::create(log_path)?;
    command
        .stdout(Stdio::from(log.try_clone()?))
        .stderr(Stdio::from(log));
    // SAT subprocesses inherit this group, so timeout cleanup includes them on Unix.
    #[cfg(unix)]
    command.process_group(0);
    let mut child = command.spawn()?;
    loop {
        if let Some(status) = child.try_wait()? {
            ensure!(status.success(), "Lean exited with {status}");
            return Ok(());
        }
        if Instant::now() >= deadline {
            stop_attempt(&mut child)?;
            bail!("attempt exceeded its remaining wall-clock budget");
        }
        thread::sleep(Duration::from_millis(20));
    }
}

fn stop_attempt(child: &mut Child) -> Result<()> {
    #[cfg(unix)]
    {
        // Only target the group created by run_attempt, never the caller's group.
        let _ = Command::new("/bin/kill")
            .args(["-KILL", "--", &format!("-{}", child.id())])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();
    }
    let _ = child.kill();
    child.wait()?;
    Ok(())
}

fn audit_axioms(output: &str, expected: &[String]) -> Result<()> {
    ensure!(
        !output.contains("sorryAx")
            && !output.contains("declaration uses 'sorry'")
            && !output.contains("error:"),
        "Lean reported an error or incomplete proof"
    );
    let mut missing = expected.iter().map(String::as_str).collect::<BTreeSet<_>>();
    let mut lines = output.lines();
    while let Some(line) = lines.next() {
        let Some((quoted, dependencies)) = line.split_once(" depends on axioms: ") else {
            if let Some(quoted) = line.strip_suffix(" does not depend on any axioms") {
                let name = quoted
                    .strip_prefix('\'')
                    .and_then(|s| s.strip_suffix('\''))
                    .context("malformed theorem axiom report")?;
                ensure!(
                    missing.remove(name),
                    "unexpected or duplicate theorem report: {name}"
                );
            }
            continue;
        };
        let name = quoted
            .strip_prefix('\'')
            .and_then(|s| s.strip_suffix('\''))
            .context("malformed theorem axiom report")?;
        ensure!(
            missing.remove(name),
            "unexpected or duplicate theorem report: {name}"
        );
        let mut dependencies = dependencies.to_owned();
        while !dependencies.ends_with(']') {
            dependencies.push_str(
                lines
                    .next()
                    .context("unterminated theorem axiom report")?
                    .trim(),
            );
        }
        let dependencies = dependencies
            .strip_prefix('[')
            .and_then(|s| s.strip_suffix(']'))
            .context("malformed axiom dependency list")?;
        for dependency in dependencies
            .split(',')
            .map(str::trim)
            .filter(|s| !s.is_empty())
        {
            ensure!(
                matches!(dependency, "propext" | "Classical.choice" | "Quot.sound"),
                "unexpected axiom dependency: {dependency}"
            );
        }
    }
    ensure!(
        missing.is_empty(),
        "missing theorem axiom reports: {missing:?}"
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::audit_axioms;

    #[test]
    fn axiom_audit_requires_all_reports_and_foundational_axioms() {
        let expected = ["layout_artifact", "runtime_rewrite_0"].map(str::to_owned);
        let valid = "'layout_artifact' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'runtime_rewrite_0' does not depend on any axioms\n";
        audit_axioms(valid, &expected).unwrap();
        for bad in [
            valid.replace("'runtime_rewrite_0' does not depend on any axioms\n", ""),
            format!("{valid}'runtime_rewrite_0' depends on axioms: []\n"),
            valid.replace("Quot.sound", "Custom.assumption"),
            valid.replace("Quot.sound", "Lean.ofReduceBool"),
            valid.replace("Quot.sound", "runtime_rewrite_0._native.bv_decide.ax_1"),
            valid.replace("Quot.sound", "sorryAx"),
            format!("{valid}x.lean:1:1: error: failed\n"),
        ] {
            assert!(audit_axioms(&bad, &expected).is_err(), "accepted {bad}");
        }
    }

    #[test]
    #[cfg(unix)]
    fn timeout_stops_attempt_and_its_descendant_process() {
        use std::{
            fs,
            path::Path,
            process::Command,
            time::{Duration, Instant},
        };
        let dir = tempfile::tempdir().unwrap();
        let script = dir.path().join("descendant.sh");
        let pid_path = dir.path().join("pid");
        fs::write(
            &script,
            format!("sleep 30 &\necho $! > '{}'\nwait\n", pid_path.display()),
        )
        .unwrap();
        let result = super::run_attempt(
            Path::new("/bin/sh"),
            &script,
            &dir.path().join("log"),
            Instant::now() + Duration::from_millis(300),
        );
        assert!(
            result
                .unwrap_err()
                .to_string()
                .contains("wall-clock budget")
        );
        let pid = fs::read_to_string(pid_path).unwrap();
        let deadline = Instant::now() + Duration::from_secs(2);
        loop {
            let alive = Command::new("/bin/kill")
                .args(["-0", pid.trim()])
                .output()
                .unwrap()
                .status
                .success();
            if !alive {
                break;
            }
            assert!(
                Instant::now() < deadline,
                "descendant survived timeout: {pid}"
            );
            std::thread::sleep(Duration::from_millis(20));
        }
    }
}
