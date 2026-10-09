use evm_golf::runtime::{self, SearchStopReason, scenario::Scenario};
use revm::primitives::keccak256;
use serde_json::{Value, json};
use std::fs;
use tempfile::tempdir;

fn scenarios() -> Vec<Scenario> {
    serde_json::from_value(json!([{
        "caller":"0x1111111111111111111111111111111111111111",
        "target":"0x2222222222222222222222222222222222222222",
        "accounts":{
            "0x1111111111111111111111111111111111111111":{"balance":"1000000"},
            "0x2222222222222222222222222222222222222222":{"nonce":1}
        },
        "transactions":[{"calldata":"","gas_limit":100000}]
    }]))
    .unwrap()
}

#[test]
fn search_rejects_zero_rounds_existing_output_and_invalid_inputs() {
    let dir = tempdir().unwrap();
    let out = dir.path().join("zero");
    assert!(runtime::search_scenarios(&[0], &scenarios(), 0, &out).is_err());
    assert!(!out.exists());
    fs::write(dir.path().join("sentinel"), "unchanged").unwrap();
    assert!(runtime::search_scenarios(&[0], &scenarios(), 1, dir.path()).is_err());
    assert_eq!(
        fs::read_to_string(dir.path().join("sentinel")).unwrap(),
        "unchanged"
    );
    assert!(!dir.path().join("failure.log").exists());
    let mut empty_transactions = scenarios();
    empty_transactions[0].transactions.clear();
    for (i, code, fixtures) in [
        (0, vec![0], vec![]),
        (1, vec![0], empty_transactions),
        (2, vec![0xff], scenarios()),
    ] {
        let out = dir.path().join(format!("invalid-{i}"));
        assert!(runtime::search_scenarios(&code, &fixtures, 1, &out).is_err());
        assert!(out.join("failure.log").exists());
        assert!(out.join("original.hex").exists());
        assert!(!out.join("candidate.hex").exists());
        assert!(!out.join("result.json").exists());
    }
}

#[test]
#[ignore = "requires Lean"]
fn search_checks_proposal_chain_round_limit_and_final_replay() {
    let dir = tempdir().unwrap();
    let code = runtime::from_hex("600160026003600490925090506122705000").unwrap();
    let fixtures = scenarios();
    let limited = dir.path().join("limited");
    let report = runtime::search_scenarios(&code, &fixtures, 1, &limited).unwrap();
    assert_eq!(report.stop_reason, SearchStopReason::RoundsLimit);
    assert_eq!(report.rounds_completed, 1);
    assert_eq!(report.stages.len(), 2);
    assert!(report.stages[1].rewrites > 0);
    assert!(limited.join("round-1-proposals/proposals.json").exists());
    assert_eq!(report.cases.len(), 1);
    assert!(report.cases[0].baseline_gas > report.cases[0].candidate_gas);
    assert!(
        limited
            .join("final-scenario-0-calls/transaction-0.trace")
            .exists()
    );
    let mut hash = keccak256(&code).to_string();
    for stage in &report.stages {
        assert_eq!(stage.input_keccak256, hash);
        hash = stage.output_keccak256.clone();
        assert!(stage.lean_version.is_some());
        assert!(limited.join(&stage.directory).join("result.json").exists());
    }
    assert_eq!(report.candidate_keccak256, hash);
    assert_eq!(
        report.scenarios_keccak256,
        keccak256(fs::read(limited.join("scenarios.json")).unwrap()).to_string()
    );
    let accepted =
        runtime::from_hex(&fs::read_to_string(limited.join("candidate.hex")).unwrap()).unwrap();
    assert_eq!(keccak256(&accepted).to_string(), hash);
    let converged =
        runtime::search_scenarios(&accepted, &fixtures, 4, &dir.path().join("converged")).unwrap();
    assert_eq!(converged.stop_reason, SearchStopReason::Converged);
    assert!(converged.rounds_completed <= 4);
    assert_eq!(converged.stages[converged.stages.len() - 1].rewrites, 0);
    assert_eq!(converged.stages[converged.stages.len() - 2].rewrites, 0);
}

#[test]
#[ignore = "requires Lean"]
fn identity_search_checks_both_stages_and_failure_is_not_accepted() {
    let dir = tempdir().unwrap();
    let out = dir.path().join("identity");
    let report = runtime::search_scenarios(&[0], &scenarios(), 1, &out).unwrap();
    assert_eq!(report.stop_reason, SearchStopReason::Converged);
    assert_eq!(report.rounds_completed, 1);
    assert!(
        report
            .stages
            .iter()
            .all(|stage| stage.rewrites == 0 && stage.lean_version.is_some())
    );
    assert_eq!(report.cases.len(), 1);
    let result: Value =
        serde_json::from_slice(&fs::read(out.join("result.json")).unwrap()).unwrap();
    assert_eq!(result["stop_reason"], "converged");
    let mut invalid = scenarios();
    invalid[0].caller = "not-an-address".into();
    let failed = dir.path().join("failed-replay");
    assert!(runtime::search_scenarios(&[0], &invalid, 1, &failed).is_err());
    assert!(failed.join("failure.log").exists());
    assert!(failed.join("round-1-builtins/Rewrites.lean").exists());
    assert!(failed.join("round-1-builtins/failure.log").exists());
    assert!(!failed.join("candidate.hex").exists());
    assert!(!failed.join("result.json").exists());
}

#[test]
#[ignore = "requires Lean"]
fn builtin_retries_cannot_bypass_call_guards() {
    let dir = tempdir().unwrap();
    let child = format!("0x{}", "33".repeat(20));
    // One rewrite before the call and one after it. The guard rejects a GAS
    // observation in the child even when the selected patch follows the call.
    let code = runtime::from_hex(&format!(
        "60026002025060205f5f5f5f73{}5af15060036002025060205ff3",
        &child[2..]
    ))
    .unwrap();
    let mut fixture = serde_json::to_value(scenarios()).unwrap();
    fixture[0]["accounts"][&child] = json!({"code":"5a5f5260205ff3"});
    let fixtures: Vec<Scenario> = serde_json::from_value(fixture).unwrap();
    let out = dir.path().join("guarded-retry");
    let error = runtime::search_scenarios(&code, &fixtures, 1, &out).unwrap_err();
    assert!(format!("{error:#}").contains("external-call guard"));
    for (name, count) in [
        ("round-1-builtins", 2),
        ("round-1-builtins-retry-1", 1),
        ("round-1-builtins-retry-2", 1),
        ("round-1-builtins-retry-3", 0),
    ] {
        let stage = out.join(name);
        let rewrites: Value =
            serde_json::from_slice(&fs::read(stage.join("rewrites.json")).unwrap()).unwrap();
        assert_eq!(rewrites.as_array().unwrap().len(), count);
        assert!(
            fs::read_to_string(stage.join("failure.log"))
                .unwrap()
                .contains("external-call guard")
        );
        assert!(stage.join("Rewrites.log").exists());
        assert!(!stage.join("candidate.hex").exists());
        assert!(!stage.join("result.json").exists());
    }
    assert!(!out.join("candidate.hex").exists());
    assert!(!out.join("result.json").exists());
}
