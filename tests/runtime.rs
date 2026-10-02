use serde_json::Value;
use std::{fs, process::Command};
use tempfile::tempdir;

#[test]
fn cli_analyzes_hex_files_and_rejects_unsupported_control_flow() {
    let dir = tempdir().unwrap();
    let input = dir.path().join("runtime.hex");
    fs::write(&input, "0x60026003015f5260205ff3\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_evm-golf"))
        .args(["analyze-runtime", "--bytecode"])
        .arg(&input)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["max_stack"], 2);
    fs::write(&input, "5f3556").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_evm-golf"))
        .args(["analyze-runtime", "--bytecode"])
        .arg(&input)
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("dynamic jump"));
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn cli_saves_only_checked_candidates_and_keeps_failure_evidence() {
    let dir = tempdir().unwrap();
    let input = dir.path().join("runtime.hex");
    let cases = dir.path().join("cases.json");
    fs::write(&input, "600060000100").unwrap();
    fs::write(&cases, r#"[{"calldata":"0x","gas_limit":100000}]"#).unwrap();
    let run = |out: &str| {
        Command::new(env!("CARGO_BIN_EXE_evm-golf"))
            .args(["optimize-runtime", "--bytecode"])
            .arg(&input)
            .arg("--cases")
            .arg(&cases)
            .arg("--out")
            .arg(dir.path().join(out))
            .output()
            .unwrap()
    };
    let output = run("accepted");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("local gas-erased stack rewrites only")
    );
    assert!(dir.path().join("accepted/Rewrites.log").exists());
    assert!(dir.path().join("accepted/result.json").exists());
    assert!(!run("accepted").status.success());
    fs::write(&cases, r#"[{"calldata":"0x","gas_limit":21002}]"#).unwrap();
    assert!(!run("rejected").status.success());
    for name in ["original.hex", "cases.json", "rewrites.json", "failure.log"] {
        assert!(dir.path().join("rejected").join(name).exists(), "{name}");
    }
    assert!(!dir.path().join("rejected/result.json").exists());
    assert!(!dir.path().join("rejected/candidate.hex").exists());
}

#[test]
fn cli_replays_sequences_and_retains_step_failure_evidence() {
    let dir = tempdir().unwrap();
    let input = dir.path().join("runtime.hex");
    let sequences = dir.path().join("sequences.json");
    // Increment slot zero and return the previous value. No rewrite needed.
    fs::write(&input, "5f54805f526001015f5560205ff3").unwrap();
    let run = |out: &str, extra: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_evm-golf"))
            .args(["optimize-runtime", "--bytecode"])
            .arg(&input)
            .arg("--sequences")
            .arg(&sequences)
            .arg("--out")
            .arg(dir.path().join(out))
            .args(extra)
            .output()
            .unwrap()
    };
    fs::write(
        &sequences,
        r#"[
      {"transactions":[{"calldata":"","gas_limit":100000},{"calldata":"","gas_limit":100000}]},
      {"transactions":[{"calldata":"","gas_limit":100000}]}
    ]"#,
    )
    .unwrap();
    let output = run("accepted", &[]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: Value =
        serde_json::from_str(&fs::read_to_string(dir.path().join("accepted/result.json")).unwrap())
            .unwrap();
    let cases = report["cases"].as_array().unwrap();
    assert_eq!(cases.len(), 3);
    assert!(
        cases[0]["baseline_gas"].as_u64().unwrap() > cases[1]["baseline_gas"].as_u64().unwrap()
    );
    assert_eq!(cases[0], cases[2]); // Each sequence starts fresh.
    assert!(
        report["verification"]
            .as_str()
            .unwrap()
            .contains("transaction sequences")
    );
    assert!(dir.path().join("accepted/sequences.json").exists());
    assert!(!dir.path().join("accepted/cases.json").exists());
    assert!(
        !run("conflict", &["--cases", "unused.json"])
            .status
            .success()
    );
    for (name, json) in [
        ("empty", "[]"),
        ("empty-steps", r#"[{"transactions":[]}]"#),
        (
            "step-storage",
            r#"[{"transactions":[{"calldata":"","gas_limit":100000,"storage":{"0":"1"}}]}]"#,
        ),
    ] {
        fs::write(&sequences, json).unwrap();
        assert!(!run(name, &[]).status.success());
        assert!(!dir.path().join(name).exists());
    }
    fs::write(&sequences, r#"[{"transactions":[{"calldata":"","gas_limit":100000},{"calldata":"","gas_limit":21000}]}]"#).unwrap();
    assert!(!run("rejected", &[]).status.success());
    let failure = fs::read_to_string(dir.path().join("rejected/failure.log")).unwrap();
    assert!(failure.contains("sequence 0: transaction 1"), "{failure}");
    for name in ["candidate.hex", "result.json"] {
        assert!(!dir.path().join("rejected").join(name).exists());
    }
}
