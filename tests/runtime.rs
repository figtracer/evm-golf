use evm_golf::runtime::{self, Transaction, scenario::Scenario};
use serde_json::{Value, json};
use std::{fs, path::Path};
use tempfile::tempdir;

const CALLER: &str = "0x1111111111111111111111111111111111111111";
const TARGET: &str = "0x2222222222222222222222222222222222222222";

fn scenarios(transactions: Value) -> Vec<Scenario> {
    serde_json::from_value(json!([{
        "caller": CALLER,
        "target": TARGET,
        "accounts": {CALLER: {"balance":"1000000"}, TARGET: {"nonce":1}},
        "transactions": transactions
    }]))
    .unwrap()
}

fn optimize(code: &str, fixtures: &[Scenario], out: &Path) -> anyhow::Result<Value> {
    runtime::optimize_scenarios(&runtime::from_hex(code).unwrap(), fixtures, out)?;
    Ok(serde_json::from_slice(&fs::read(out.join("result.json")).unwrap()).unwrap())
}

fn saved(report: &Value, case: usize) -> u64 {
    report["cases"][case]["baseline_gas"].as_u64().unwrap()
        - report["cases"][case]["candidate_gas"].as_u64().unwrap()
}

fn assert_rejected(out: &Path, needle: &str) {
    let failure = fs::read_to_string(out.join("failure.log")).unwrap();
    assert!(failure.contains(needle), "{failure}");
    assert!(!out.join("candidate.hex").exists());
    assert!(!out.join("result.json").exists());
}

#[test]
fn scenario_check_replays_without_claiming_a_proof() {
    let dir = tempdir().unwrap();
    let fixtures: Vec<Scenario> = serde_json::from_value(json!([{
        "caller": CALLER, "target": TARGET,
        "accounts": {TARGET: {}, CALLER: {"balance":"100"}},
        "transactions": [{"calldata":"","gas_limit":100000,"value":"7"}]
    }]))
    .unwrap();
    let out = dir.path().join("checked");
    let report = runtime::scenario::check(
        &runtime::from_hex("60005000").unwrap(),
        &runtime::from_hex("00").unwrap(),
        &fixtures,
        &out,
    )
    .unwrap();
    assert!(report.verification.contains("No Lean"));
    assert_eq!(report.cases[0].outcome, "success");
    assert!(out.join("candidate.hex").exists());
    assert!(!out.join("Rewrites.lean").exists());
}

#[test]
fn library_entry_points_bound_work_before_creating_evidence() {
    let dir = tempdir().unwrap();
    let fixtures = [Scenario {
        target: String::new(),
        caller: String::new(),
        accounts: Default::default(),
        environment: Default::default(),
        transactions: vec![Transaction {
            to: None,
            calldata: String::new(),
            gas_limit: 30_000_001,
            value: String::new(),
        }],
    }];
    let out = dir.path().join("check");
    let error = runtime::scenario::check(&[0], &[0], &fixtures, &out).unwrap_err();
    assert!(error.to_string().contains("gas limit exceeds"));
    assert!(!out.exists());
    let out = dir.path().join("optimize");
    let error = runtime::optimize_scenarios(&[0], &fixtures, &out).unwrap_err();
    assert!(error.to_string().contains("gas limit exceeds"));
    assert!(!out.exists());
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn builtins_are_proved_and_replay_still_rejects_gas_outcome_changes() {
    let dir = tempdir().unwrap();
    let code = "60076002026004025f5260205ff3";
    let report = optimize(
        code,
        &scenarios(json!([{"calldata":"","gas_limit":100000}])),
        &dir.path().join("accepted"),
    )
    .unwrap();
    assert_eq!(report["rewrites"].as_array().unwrap().len(), 2);
    assert!(report["lean_version"].is_string());
    assert!(dir.path().join("accepted/Rewrites.log").exists());
    // Less gas makes the candidate succeed while its baseline runs out. A
    // local proof must not bypass the concrete acceptance check.
    let out = dir.path().join("rejected");
    assert!(
        optimize(
            code,
            &scenarios(json!([{"calldata":"","gas_limit":21030}])),
            &out
        )
        .is_err()
    );
    assert!(out.join("Rewrites.log").exists());
    assert_rejected(&out, "");
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn computed_jumps_keep_offsets() {
    let dir = tempdir().unwrap();
    let code = "60035f35565b6002025f5260205ff3";
    let calldata = format!("{:064x}", 5);
    let out = dir.path().join("layout");
    let report = optimize(
        code,
        &scenarios(json!([{"calldata":calldata,"gas_limit":100000}])),
        &out,
    )
    .unwrap();
    assert_eq!(report["baseline_bytes"], report["candidate_bytes"]);
    assert_eq!(report["rewrites"].as_array().unwrap().len(), 1);
    assert_eq!(saved(&report, 0), 2);
    let candidate = fs::read_to_string(out.join("candidate.hex")).unwrap();
    assert_eq!(&candidate.trim()[..12], &code[..12]);
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn account_fixtures_are_used_and_validated() {
    let dir = tempdir().unwrap();
    let caller = "44".repeat(20);
    let target = "55".repeat(20);
    // Require the supplied caller, target, initialized slot and transferred value.
    // Revert if a default account or state silently replaces the fixture.
    let mut code = format!("3373{caller}143073{target}14165f54600714163460031416");
    let destination = code.len() / 2 + 6;
    code.push_str(&format!(
        "60{destination:02x}575f5ffd5b5f546002025f5260205ff3"
    ));
    let mut fixture = json!([{
        "caller": format!("0x{caller}"), "target": format!("0x{target}"),
        "accounts": {
            format!("0x{caller}"): {"balance":"10", "nonce":3},
            format!("0x{target}"): {"balance":"5", "nonce":1,"storage":{"0":"7"}}
        },
        "transactions": [
            {"calldata":"", "gas_limit":100000,"value":"3"},
            {"calldata":"", "gas_limit":100000,"value":"0"}
        ]
    }]);
    let out = dir.path().join("accepted");
    let report = optimize(
        &code,
        &serde_json::from_value::<Vec<Scenario>>(fixture.clone()).unwrap(),
        &out,
    )
    .unwrap();
    assert_eq!(report["cases"][0]["outcome"], "success");
    assert_eq!(report["cases"][1]["outcome"], "revert");
    assert!(saved(&report, 0) > 0);
    assert_eq!(report["baseline_bytes"], report["candidate_bytes"]);
    let kept: Value =
        serde_json::from_slice(&fs::read(out.join("scenarios.json")).unwrap()).unwrap();
    assert_eq!(
        kept[0]["accounts"][format!("0x{target}")]["storage"]["0"],
        "7"
    );
    fixture[0]["accounts"][format!("0x{caller}")]["balance"] = "0".into();
    let out = dir.path().join("unfunded");
    assert!(
        optimize(
            &code,
            &serde_json::from_value::<Vec<Scenario>>(fixture.clone()).unwrap(),
            &out
        )
        .is_err()
    );
    assert_rejected(&out, "");
    // GAS observations are rejected before any evidence is written.
    let out = dir.path().join("sensitive");
    assert!(
        optimize(
            "5a00",
            &scenarios(json!([{"calldata":"","gas_limit":100000}])),
            &out
        )
        .is_err()
    );
    assert!(!out.exists());
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn ecrecover_calls_must_succeed_in_both_programs() {
    let dir = tempdir().unwrap();
    // A real MUL rewrite before an empty-input ECRECOVER call. Empty input is
    // an invalid signature, which succeeds with empty returndata when funded.
    let code = "6002600202505f5f5f5f60015afa5000";
    for (name, gas) in [("funded", 200_000), ("underfunded", 24_000)] {
        let out = dir.path().join(name);
        let result = optimize(
            code,
            &scenarios(json!([{"calldata":"","gas_limit":gas}])),
            &out,
        );
        if name == "funded" {
            let report = result.unwrap();
            assert!(!report["rewrites"].as_array().unwrap().is_empty());
            assert_eq!(report["cases"][0]["outcome"], "success");
        } else {
            assert!(result.is_err());
            assert_rejected(&out, "ECRECOVER");
        }
    }
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn unknown_halt_branches_are_kept_but_halted_cases_rejected() {
    let dir = tempdir().unwrap();
    // The unknown byte halts before GAS on the zero-input path. Nonzero input
    // jumps past it and exercises an actual multiplication rewrite.
    let code = "5f356007574d5a5b60026002025000";
    for input in [1, 0] {
        let out = dir.path().join(input.to_string());
        let calldata = format!("{input:064x}");
        let result = optimize(
            code,
            &scenarios(json!([{"calldata":calldata,"gas_limit":100000}])),
            &out,
        );
        if input == 1 {
            let report = result.unwrap();
            assert!(!report["rewrites"].as_array().unwrap().is_empty());
            let candidate = fs::read_to_string(out.join("candidate.hex")).unwrap();
            assert_eq!(&candidate[10..14], "4d5a");
        } else {
            assert!(result.is_err());
            assert_rejected(&out, "OpcodeNotFound");
        }
    }
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn external_calls_are_guarded() {
    let dir = tempdir().unwrap();
    let child = format!("0x{}", "33".repeat(20));
    let code = format!("60026002025060205f5f5f5f73{}5af15060205ff3", &child[2..]);
    let mut fixture = json!([{
        "caller":CALLER, "target":TARGET,
        "accounts":{
            CALLER:{"balance":"1000000"}, TARGET:{},
            &child:{"code":"60075f5560015f5260205ff3"}
        },
        "transactions":[{"calldata":"","gas_limit":200000},{"calldata":"","gas_limit":200000}]
    }]);
    let out = dir.path().join("guarded");
    let report = optimize(
        &code,
        &serde_json::from_value::<Vec<Scenario>>(fixture.clone()).unwrap(),
        &out,
    )
    .unwrap();
    assert_eq!(report["rewrites"].as_array().unwrap().len(), 1);
    assert!(
        report["verification"]
            .as_str()
            .unwrap()
            .contains("guarded nested calls")
    );
    for case in 0..2 {
        assert_eq!(report["cases"][case]["outcome"], "success");
        assert_eq!(saved(&report, case), 2);
    }
    assert!(out.join("scenario-0-calls/transaction-1.trace").exists());
    fixture[0]["accounts"][&child]["code"] = "5a5f5260205ff3".into();
    let out = dir.path().join("sensitive-child");
    let error = optimize(
        &code,
        &serde_json::from_value::<Vec<Scenario>>(fixture).unwrap(),
        &out,
    )
    .unwrap_err();
    assert!(format!("{error:#}").contains("external-call guard"));
    assert_rejected(&out, "");
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn constant_code_reads_are_certified() {
    let dir = tempdir().unwrap();
    let fixture = scenarios(json!([{"calldata":"","gas_limit":100000}]));
    for (name, code, count) in [
        ("disjoint", "600760020250600360105f3960035ff300abcdef", 1),
        ("observed", "600760020250600360025f3960035ff300abcdef", 0),
    ] {
        let out = dir.path().join(name);
        let report = optimize(code, &fixture, &out).unwrap();
        assert_eq!(report["rewrites"].as_array().unwrap().len(), count);
        assert_eq!(saved(&report, 0), (count * 2) as u64);
        let proof = fs::read_to_string(out.join("Rewrites.lean")).unwrap();
        assert!(proof.contains("codecopy_artifact"));
    }
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn literal_folds_need_no_input_stack() {
    let dir = tempdir().unwrap();
    let out = dir.path().join("folded");
    let report = optimize(
        "60076003165f5260205ff3",
        &scenarios(json!([{"calldata":"","gas_limit":100000}])),
        &out,
    )
    .unwrap();
    assert_eq!(report["rewrites"][0]["required_stack"], 0);
    assert_eq!(saved(&report, 0), 1);
    assert_eq!(
        fs::read_to_string(out.join("candidate.hex"))
            .unwrap()
            .trim(),
        "60036000505f5260205ff3"
    );
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn jumps_are_threaded_past_trampolines() {
    let dir = tempdir().unwrap();
    // CALLDATALOAD(0) selects the JUMPI; X = 8 is `JUMPDEST; PUSH1 13; JUMP`.
    let code = "5f356008570000005b600d56005b00";
    let taken = format!("{:064x}", 1);
    let out = dir.path().join("threaded");
    runtime::optimize_scenarios_threads(
        &runtime::from_hex(code).unwrap(),
        &scenarios(json!([
            {"calldata":taken,"gas_limit":100000},
            {"calldata":"","gas_limit":100000}
        ])),
        &out,
    )
    .unwrap();
    let report: Value =
        serde_json::from_slice(&fs::read(out.join("result.json")).unwrap()).unwrap();
    assert_eq!(report["rewrites"].as_array().unwrap().len(), 1);
    assert_eq!(saved(&report, 0), 12);
    assert_eq!(saved(&report, 1), 0);
    assert_eq!(
        fs::read_to_string(out.join("candidate.hex"))
            .unwrap()
            .trim(),
        "5f35600d570000005b600d56005b00"
    );
    assert!(
        fs::read_to_string(out.join("Rewrites.log"))
            .unwrap()
            .contains("thread_0")
    );
    // No trampoline: the stage refuses to run rather than accept a no-op.
    let out = dir.path().join("none");
    assert!(
        runtime::optimize_scenarios_threads(
            &runtime::from_hex("00").unwrap(),
            &scenarios(json!([{"calldata":"","gas_limit":100000}])),
            &out,
        )
        .is_err()
    );
    assert!(!out.join("result.json").exists());
}
