use evm_golf::runtime::{self, project::Proposals};
use revm::primitives::keccak256;
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};
use tempfile::tempdir;

// Two discoverable swap windows after literal pushes, then STOP.
const CODE: &str = "600160026003600490925090506122705000";

fn project(dir: &Path, manifest: Value) -> PathBuf {
    fs::create_dir_all(dir.join("fixtures")).unwrap();
    fs::write(dir.join("fixtures/token.hex"), CODE).unwrap();
    fs::write(
        dir.join("fixtures/token.scenarios.json"),
        serde_json::to_vec(&json!([{
            "caller":"0x1111111111111111111111111111111111111111",
            "target":"0x2222222222222222222222222222222222222222",
            "accounts":{
                "0x1111111111111111111111111111111111111111":{"balance":"1000000"},
                "0x2222222222222222222222222222222222222222":{"nonce":1}
            },
            "transactions":[{"calldata":"","gas_limit":100000}]
        }]))
        .unwrap(),
    )
    .unwrap();
    let path = dir.join("project.json");
    fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    path
}

fn manifest() -> Value {
    json!({"version":1,"contracts":[{
        "id":"token",
        "runtime":"fixtures/token.hex",
        "scenarios":"fixtures/token.scenarios.json"
    }]})
}

fn run(args: &[&std::ffi::OsStr]) -> Output {
    // Run from an unrelated directory: manifest paths are manifest-relative.
    Command::new(env!("CARGO_BIN_EXE_evm-golf"))
        .current_dir(std::env::temp_dir())
        .args(args)
        .output()
        .unwrap()
}

fn ok(output: &Output) {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn inspect_prints_unverified_proposals_bound_to_each_runtime() {
    let dir = tempdir().unwrap();
    let path = project(dir.path(), manifest());
    let output = run(&["inspect".as_ref(), path.as_os_str()]);
    ok(&output);
    assert!(String::from_utf8_lossy(&output.stderr).contains("unverified"));
    let proposals: Proposals = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(proposals.contracts[0].id, "token");
    assert_eq!(
        proposals.contracts[0].original_keccak256,
        keccak256(runtime::from_hex(CODE).unwrap()).to_string()
    );
    assert!(!proposals.contracts[0].sites.is_empty());
    // Deterministic output.
    assert_eq!(
        output.stdout,
        run(&["inspect".as_ref(), path.as_os_str()]).stdout
    );
}

#[test]
fn manifests_and_flags_are_validated() {
    let dir = tempdir().unwrap();
    let mut duplicate = manifest();
    let entry = duplicate["contracts"][0].clone();
    duplicate["contracts"].as_array_mut().unwrap().push(entry);
    let mut version = manifest();
    version["version"] = 2.into();
    let mut unknown = manifest();
    unknown["contracts"][0]["proof"] = "by sorry".into();
    let mut bad_id = manifest();
    bad_id["contracts"][0]["id"] = "../token".into();
    let mut missing = manifest();
    missing["contracts"][0]["runtime"] = "fixtures/missing.hex".into();
    for (index, invalid) in [duplicate, version, unknown, bad_id, missing]
        .into_iter()
        .enumerate()
    {
        let path = project(&dir.path().join(index.to_string()), invalid);
        assert!(
            !run(&["inspect".as_ref(), path.as_os_str()])
                .status
                .success(),
            "{index}"
        );
    }
    let path = project(&dir.path().join("valid"), manifest());
    let unknown = run(&[
        "inspect".as_ref(),
        path.as_os_str(),
        "--contract".as_ref(),
        "other".as_ref(),
    ]);
    assert!(!unknown.status.success());
    let out = dir.path().join("zero");
    let zero = run(&[
        "optimize".as_ref(),
        path.as_os_str(),
        "--rounds".as_ref(),
        "0".as_ref(),
        "--out".as_ref(),
        out.as_os_str(),
    ]);
    assert!(!zero.status.success());
    assert!(!out.exists());
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn optimize_inspect_and_verify_form_one_workflow() {
    let dir = tempdir().unwrap();
    let path = project(dir.path(), manifest());
    // optimize: verified savings plus a next-baseline project.
    let out = dir.path().join("optimized");
    let output = run(&[
        "optimize".as_ref(),
        path.as_os_str(),
        "--out".as_ref(),
        out.as_os_str(),
    ]);
    ok(&output);
    let result: Value = serde_json::from_slice(&output.stdout).unwrap();
    let token = &result["contracts"][0];
    assert_eq!(token["accepted"], true);
    assert!(token["candidate_gas"].as_u64() < token["baseline_gas"].as_u64());
    assert!(
        result["scope"]
            .as_str()
            .unwrap()
            .contains("not a whole-contract")
    );
    let summary = fs::read_to_string(out.join("summary.txt")).unwrap();
    assert!(String::from_utf8_lossy(&output.stderr).contains(&summary));
    assert!(summary.contains("local Lean proofs and guarded replay passed"));
    assert!(summary.contains("Supplied transactions: passed (1)"));
    assert!(summary.contains("Contract-wide proof: not run by this command"));
    assert!(!summary.contains("Contract-wide proof: passed"));
    let baseline = out.join("baseline/project.json");
    let again = dir.path().join("again");
    let output = run(&[
        "optimize".as_ref(),
        baseline.as_os_str(),
        "--out".as_ref(),
        again.as_os_str(),
    ]);
    ok(&output);
    let result: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(result["contracts"][0]["rewrites"], 0);
    // inspect then verify: the printed proposals are accepted as submitted.
    let proposals = dir.path().join("proposals.json");
    let inspected = run(&["inspect".as_ref(), path.as_os_str()]);
    ok(&inspected);
    fs::write(&proposals, &inspected.stdout).unwrap();
    let verified = dir.path().join("verified");
    let output = run(&[
        "verify".as_ref(),
        path.as_os_str(),
        "--proposals".as_ref(),
        proposals.as_os_str(),
        "--out".as_ref(),
        verified.as_os_str(),
    ]);
    ok(&output);
    let result: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(result["contracts"][0]["accepted"], true);
    assert!(verified.join("baseline/token.hex").exists());
    // The output directory must be new.
    let reused = run(&[
        "verify".as_ref(),
        path.as_os_str(),
        "--proposals".as_ref(),
        proposals.as_os_str(),
        "--out".as_ref(),
        verified.as_os_str(),
    ]);
    assert!(!reused.status.success());
}

#[test]
fn rejected_contract_report_does_not_claim_verified_savings() {
    let dir = tempdir().unwrap();
    let path = project(dir.path(), manifest());
    // A stale hash rejects the contract unchanged and exits with an error.
    let proposals = dir.path().join("proposals.json");
    let inspected = run(&["inspect".as_ref(), path.as_os_str()]);
    ok(&inspected);
    let mut stale: Value = serde_json::from_slice(&inspected.stdout).unwrap();
    stale["contracts"][0]["original_keccak256"] = format!("0x{}", "00".repeat(32)).into();
    fs::write(&proposals, serde_json::to_vec(&stale).unwrap()).unwrap();
    let rejected = dir.path().join("rejected");
    let output = run(&[
        "verify".as_ref(),
        path.as_os_str(),
        "--proposals".as_ref(),
        proposals.as_os_str(),
        "--out".as_ref(),
        rejected.as_os_str(),
    ]);
    assert!(!output.status.success());
    let result: Value =
        serde_json::from_slice(&fs::read(rejected.join("result.json")).unwrap()).unwrap();
    assert_eq!(result["contracts"][0]["accepted"], false);
    assert_eq!(
        fs::read_to_string(rejected.join("baseline/token.hex"))
            .unwrap()
            .trim(),
        CODE
    );
    let stdout: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(stdout, result);
    let summary = fs::read_to_string(rejected.join("summary.txt")).unwrap();
    assert!(String::from_utf8_lossy(&output.stderr).contains(&summary));
    assert!(summary.contains("Accepted changes: none; contract rejected"));
    assert!(summary.contains("Gas saved per operation: unavailable"));
    assert!(summary.contains("Supplied transactions: not established"));
    assert!(summary.contains("Contract-wide proof: not run by this command"));
    assert!(!summary.contains("passed"));
}

#[test]
fn guarded_replay_reports_dependencies_without_claiming_a_proof() {
    let dir = tempdir().unwrap();
    project(dir.path(), manifest());
    let code = dir.path().join("fixtures/token.hex");
    let scenarios = dir.path().join("fixtures/token.scenarios.json");
    let out = dir.path().join("guarded");
    let output = run(&[
        "check-runtime".as_ref(),
        "--guard-calls".as_ref(),
        "--original".as_ref(),
        code.as_os_str(),
        "--candidate".as_ref(),
        code.as_os_str(),
        "--scenarios".as_ref(),
        scenarios.as_os_str(),
        "--out".as_ref(),
        out.as_os_str(),
    ]);
    ok(&output);
    let dependencies: Value = serde_json::from_str(
        &fs::read_to_string(out.join("scenario-0-calls/transaction-0.dependencies.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(dependencies["formal_status"], "not_proved");
    assert_eq!(dependencies["calls"][0]["obligation"], "target_entry");
    assert_eq!(
        dependencies["calls"][0]["original_code_keccak256"],
        keccak256(runtime::from_hex(CODE).unwrap()).to_string()
    );
    assert!(out.join("result.json").exists());
}
