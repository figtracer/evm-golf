//! Generate closed theorem statements and ask a pinned Lean release to check them.

use anyhow::{Context, Result, bail, ensure};
use egg::RecExpr;
use std::{
    env,
    fs::{self, File},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    thread,
    time::{Duration, Instant},
};

use crate::{
    evm::Program,
    expr::{self, Expr, RULES},
};

const MODEL: &str = include_str!("../lean/Model.lean");
const LEAN_VERSION: &str = "4.34.0";
// Generated proofs have uniform binders/tactics, so unused names are expected.
const OPTIONS: &str =
    "set_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\n";
// Keep a difficult bit-blasting problem from monopolizing a local experiment.
const PROOF_TIMEOUT: Duration = Duration::from_secs(60);

pub fn candidate(
    original: &RecExpr<Expr>,
    candidate: &RecExpr<Expr>,
    baseline: &Program,
    optimized: &Program,
) -> String {
    let left = expr::lean(original);
    let right = expr::lean(candidate);
    // A straight-line program is reduced through one recursive step per byte.
    let mut source = format!("{MODEL}\n{OPTIONS}set_option maxRecDepth 4096\n\n");
    source.push_str(&format!("theorem expression_equivalent (x y : Golf.Word) : {left} = {right} := by\n  (try simp [BitVec.mul_comm]) <;> bv_decide\n\n"));
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
        source.push_str(&format!("theorem {name} (x y : Golf.Word) :\n    Golf.run {} [{bytes}] [] x y = some [{left}] := by\n  (try simp [Golf.run, Golf.immediate, BitVec.mul_comm]) <;> bv_decide\n\n", program.body().len() + 1));
    }
    source.push_str("#print axioms expression_equivalent\n#print axioms baseline_correct\n#print axioms candidate_correct\n");
    source
}

pub fn rules() -> Result<String> {
    let mut source = format!("{MODEL}\n{OPTIONS}\nnamespace GolfRules\n\n");
    for &(name, left, right) in RULES {
        let left = expr::lean(&expr::parse(&left.replace('?', ""))?);
        let right = expr::lean(&expr::parse(&right.replace('?', ""))?);
        let name = name.replace('-', "_");
        source.push_str(&format!("theorem {name} (x y : Golf.Word) : {left} = {right} := by\n  (try simp [BitVec.mul_comm]) <;> bv_decide\n#print axioms {name}\n\n"));
    }
    source.push_str("end GolfRules\n");
    Ok(source)
}

pub fn verify(path: &Path) -> Result<String> {
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
    let log_path = path.with_extension("log");
    let log = File::create(&log_path)?;
    let mut child = Command::new(lean)
        .arg(path.canonicalize()?)
        .stdout(Stdio::from(log.try_clone()?))
        .stderr(Stdio::from(log))
        .spawn()?;
    let start = Instant::now();
    loop {
        if let Some(status) = child.try_wait()? {
            let output = fs::read_to_string(&log_path)?;
            ensure!(
                status.success()
                    && !output.contains("sorryAx")
                    && !output.contains("declaration uses 'sorry'"),
                "Lean rejected the proof; see {}\n{output}",
                log_path.display()
            );
            return Ok(version);
        }
        if start.elapsed() >= PROOF_TIMEOUT {
            child.kill()?;
            child.wait()?;
            bail!(
                "Lean exceeded {} seconds; no verified result. See {}",
                PROOF_TIMEOUT.as_secs(),
                log_path.display()
            );
        }
        thread::sleep(Duration::from_millis(20));
    }
}
