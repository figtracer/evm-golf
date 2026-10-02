//! Generate closed theorem statements and ask a pinned Lean release to check them.

use anyhow::{Context, Result, bail, ensure};
use egg::RecExpr;
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

use crate::{
    evm::Program,
    expr::{self, Expr, RULES},
};

const MODEL: &str = include_str!("../lean/Model.lean");
const LEAN_VERSION: &str = "4.34.0";
// Generated proofs have uniform binders/tactics, so unused names are expected.
const OPTIONS: &str = "set_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\nset_option pp.fullNames true\n";
// Keep a difficult bit-blasting problem from monopolizing a local experiment.
const PROOF_TIMEOUT: Duration = Duration::from_secs(60);
// Local structural trials used 15-second caps; reserve the rest for bitvector fallback.
const ALGEBRA_TIMEOUT: Duration = Duration::from_secs(15);
// Mixed rule suites need a bounded algebra attempt per theorem before SAT fallback.
// This is one tenth of Lean's default heartbeat allowance; wall time remains bounded.
const FALLBACK_HEARTBEATS: u64 = 20_000;
const BITVECTOR_TACTIC: &str = "(try simp [BitVec.mul_comm]) <;> bv_decide";
const ALGEBRA_TACTIC: &str =
    "first | (solve | simp [BitVec.mul_comm]) | ((try simp only [GolfProof.shift_one]) <;> grind)";
// Expose shifts to ring reasoning without changing the claim or bytecode model.
// This width-general lemma includes the zero-width and wrapping cases.
pub(crate) const NORMALIZATION: &str = r#"namespace GolfProof
 theorem shift_one (x : BitVec w) : x <<< 1 = x * 2 := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp
end GolfProof
"#;

/// Certify the expressions and their corresponding `Program::compile` bodies.
pub fn candidate(
    original: &RecExpr<Expr>,
    candidate: &RecExpr<Expr>,
    baseline: &Program,
    optimized: &Program,
) -> String {
    let left = expr::lean(original);
    let right = expr::lean(candidate);
    // A straight-line program is reduced through one recursive step per byte.
    let mut source = format!("{MODEL}\n{NORMALIZATION}\n{OPTIONS}set_option maxRecDepth 4096\n\n");
    source.push_str(&format!("theorem expression_equivalent (x y : Golf.Word) : {left} = {right} := by\n  {BITVECTOR_TACTIC}\n\n"));
    for (name, program) in [
        ("baseline_correct", baseline),
        ("candidate_correct", optimized),
    ] {
        let bytes = program
            .body()
            .iter()
            .map(u8::to_string)
            .collect::<Vec<_>>()
            .join(", ");
        // Reduce the exact bytes, then reuse the expression theorem as a whole.
        // Rewriting occurrences would also expand nested terms for reverse claims.
        let proof = if name == "baseline_correct" {
            "rfl".to_owned()
        } else {
            format!(
                "change some [{right}] = some [{left}]\n  exact congrArg (fun value : Golf.Word => some [value]) (expression_equivalent x y).symm"
            )
        };
        source.push_str(&format!("theorem {name} (x y : Golf.Word) :\n    Golf.run {} [{bytes}] [] x y = some [{left}] := by\n  {proof}\n\n", program.body().len() + 1));
    }
    source.push_str("#print axioms expression_equivalent\n#print axioms baseline_correct\n#print axioms candidate_correct\n");
    source
}

pub fn rules() -> Result<String> {
    let mut source = format!("{MODEL}\n{NORMALIZATION}\n{OPTIONS}\nnamespace GolfRules\n\n");
    for &(name, left, right) in RULES {
        let left = expr::lean(&expr::parse(&left.replace('?', ""))?);
        let right = expr::lean(&expr::parse(&right.replace('?', ""))?);
        let name = name.replace('-', "_");
        source.push_str(&format!("theorem {name} (x y : Golf.Word) : {left} = {right} := by\n  {BITVECTOR_TACTIC}\n#print axioms {name}\n\n"));
    }
    source.push_str("end GolfRules\n");
    Ok(source)
}

/// Runtime certificates require foundational axioms only; the expression
/// portfolio retains its documented theorem-local bv_decide dependencies.
#[derive(Clone, Copy)]
pub(crate) enum AxiomPolicy {
    Foundational,
    Bitvector,
}

pub fn verify(path: &Path) -> Result<String> {
    let source = fs::read_to_string(path)?;
    verify_named(path, &expected_theorems(&source), AxiomPolicy::Bitvector)
}

pub(crate) fn verify_named(
    path: &Path,
    expected: &[String],
    policy: AxiomPolicy,
) -> Result<String> {
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
    let deadline = Instant::now() + PROOF_TIMEOUT;
    let portfolio = source.contains(BITVECTOR_TACTIC);
    let strategies = if portfolio {
        &["algebra", "bitvector"][..]
    } else {
        &["original"][..]
    };
    let mut failures = Vec::new();
    for &strategy in strategies {
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            break;
        }
        let budget = if strategy == "algebra" {
            remaining.min(ALGEBRA_TIMEOUT)
        } else {
            remaining
        };
        let tactic = match strategy {
            "algebra" => ALGEBRA_TACTIC.to_owned(),
            "bitvector" => format!(
                "first | (solve | simp [BitVec.mul_comm]) | (set_option maxHeartbeats {FALLBACK_HEARTBEATS} in solve | ((try simp only [GolfProof.shift_one]) <;> grind)) | bv_decide (config := {{ timeout := {} }})",
                budget.as_secs().max(1)
            ),
            _ => String::new(),
        };
        let attempted = if portfolio {
            source.replace(BITVECTOR_TACTIC, &tactic)
        } else {
            source.clone()
        };
        let attempted = format!("-- Verification strategy: {strategy}.\n{attempted}");
        let attempt_path = path.with_extension(format!("{strategy}.lean"));
        let attempt_log = path.with_extension(format!("{strategy}.log"));
        fs::write(&attempt_path, &attempted)?;
        let result = run_attempt(
            &lean,
            &attempt_path,
            &attempt_log,
            (Instant::now() + budget).min(deadline),
        );
        let output = fs::read_to_string(&attempt_log).unwrap_or_default();
        let result = result.and_then(|()| audit_axioms(&output, expected, policy));
        match result {
            Ok(()) => {
                fs::write(path, attempted)?;
                fs::write(path.with_extension("log"), output)?;
                return Ok(version);
            }
            Err(error) => failures.push(format!("{strategy}: {error}\n{output}")),
        }
    }
    let output = failures.join("\n");
    fs::write(path.with_extension("log"), &output)?;
    let summary = failures
        .iter()
        .filter_map(|failure| failure.lines().next())
        .collect::<Vec<_>>()
        .join("; ");
    bail!(
        "Lean rejected the proof within the {}-second overall budget; see {}\n{summary}",
        PROOF_TIMEOUT.as_secs(),
        path.with_extension("log").display()
    )
}

fn run_attempt(lean: &Path, path: &Path, log_path: &Path, deadline: Instant) -> Result<()> {
    let log = File::create(log_path)?;
    let mut command = Command::new(lean);
    command
        .arg(path.canonicalize()?)
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

fn expected_theorems(source: &str) -> Vec<String> {
    if source.contains("\nnamespace GolfRules\n") {
        RULES
            .iter()
            .map(|(name, _, _)| format!("GolfRules.{}", name.replace('-', "_")))
            .collect()
    } else {
        [
            "expression_equivalent",
            "baseline_correct",
            "candidate_correct",
        ]
        .map(str::to_owned)
        .to_vec()
    }
}

fn audit_axioms(output: &str, expected: &[String], policy: AxiomPolicy) -> Result<()> {
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
            let foundational = matches!(dependency, "propext" | "Classical.choice" | "Quot.sound");
            // Preserve bv_decide's existing policy, restricted to generated proof-local names.
            let bitvector = expected.iter().any(|name| {
                dependency
                    .strip_prefix(&format!("{name}._native.bv_decide.ax_"))
                    .is_some_and(|suffix| {
                        suffix.split('_').all(|part| {
                            !part.is_empty() && part.bytes().all(|b| b.is_ascii_digit())
                        })
                    })
            });
            ensure!(
                foundational || (matches!(policy, AxiomPolicy::Bitvector) && bitvector),
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
    use super::{AxiomPolicy, audit_axioms};

    #[test]
    fn axiom_audit_requires_all_reports_and_checks_wrapped_dependencies() {
        let expected = [
            "expression_equivalent",
            "baseline_correct",
            "candidate_correct",
        ]
        .map(str::to_owned);
        let valid = "'expression_equivalent' depends on axioms: [propext,\n Classical.choice,\n expression_equivalent._native.bv_decide.ax_1_5]\n'baseline_correct' depends on axioms: [propext, Quot.sound]\n'candidate_correct' depends on axioms: [propext, expression_equivalent._native.bv_decide.ax_1_5]\n";
        audit_axioms(valid, &expected, AxiomPolicy::Bitvector).unwrap();
        assert!(audit_axioms(valid, &expected, AxiomPolicy::Foundational).is_err());
        let foundational = valid.replace(
            "expression_equivalent._native.bv_decide.ax_1_5",
            "Quot.sound",
        );
        audit_axioms(&foundational, &expected, AxiomPolicy::Foundational).unwrap();
        let runtime = ["runtime_rewrite_0".to_owned(), "layout_artifact".to_owned()];
        let native = "'runtime_rewrite_0' depends on axioms: [runtime_rewrite_0._native.bv_decide.ax_1]\n'layout_artifact' depends on axioms: [runtime_rewrite_0._native.bv_decide.ax_1]\n";
        audit_axioms(native, &runtime, AxiomPolicy::Bitvector).unwrap();
        assert!(audit_axioms(native, &runtime, AxiomPolicy::Foundational).is_err());
        for bad in [
            valid.replace(
                "'baseline_correct' depends on axioms: [propext, Quot.sound]\n",
                "",
            ),
            format!("{valid}'baseline_correct' depends on axioms: []\n"),
            valid.replace(
                "expression_equivalent._native.bv_decide.ax_1_5",
                "Custom.assumption",
            ),
            valid.replace(
                "expression_equivalent._native.bv_decide.ax_1_5",
                "Lean.ofReduceBool",
            ),
            valid.replace(
                "expression_equivalent._native.bv_decide.ax_1_5",
                "other._native.bv_decide.ax_1_5",
            ),
            valid.replace("expression_equivalent._native.bv_decide.ax_1_5", "sorryAx"),
        ] {
            assert!(
                audit_axioms(&bad, &expected, AxiomPolicy::Bitvector).is_err(),
                "accepted {bad}"
            );
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
