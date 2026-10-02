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
