use evm_golf::runtime::{self, RewriteProposal, scenario::Scenario};
use revm::primitives::keccak256;
use serde_json::{Value, json};
use std::{fs, process::Command};
use tempfile::tempdir;

const DEAD_PUSH: &str = "6003565b60015060025000";
const DEAD_CANDIDATE: &str = "6003565b63000000005000";

fn proposal(code: &str, pc: usize, before: &str, after: &str) -> RewriteProposal {
    RewriteProposal {
        original_keccak256: keccak256(runtime::from_hex(code).unwrap()).to_string(),
        original_pc: pc,
        before: before.into(),
        after: after.into(),
    }
}

fn scenarios(calldata: &str, gas_limit: u64) -> Vec<Scenario> {
    serde_json::from_value(json!([{
        "caller": "0x1111111111111111111111111111111111111111",
        "target": "0x2222222222222222222222222222222222222222",
        "accounts": {
            "0x1111111111111111111111111111111111111111": {"balance":"1000000"},
            "0x2222222222222222222222222222222222222222": {"nonce":1}
        },
        "transactions": [{"calldata":calldata, "gas_limit":gas_limit}]
    }]))
    .unwrap()
}

#[test]
fn proposal_schema_rejects_unknown_missing_duplicate_and_mistyped_fields() {
    let valid = json!({
        "original_keccak256": keccak256(runtime::from_hex(DEAD_PUSH).unwrap()).to_string(),
        "original_pc": 4, "before":"600150600250", "after":"630000000050"
    });
    assert!(serde_json::from_value::<RewriteProposal>(valid.clone()).is_ok());
    for field in ["original_keccak256", "original_pc", "before", "after"] {
        let mut missing = valid.clone();
        missing.as_object_mut().unwrap().remove(field);
        assert!(serde_json::from_value::<RewriteProposal>(missing).is_err());
    }
    let mut unknown = valid.clone();
    unknown["proof"] = "by sorry".into();
    assert!(serde_json::from_value::<RewriteProposal>(unknown).is_err());
    let mut negative = valid.clone();
    negative["original_pc"] = (-1).into();
    assert!(serde_json::from_value::<RewriteProposal>(negative).is_err());
    let mut bytes = valid.clone();
    bytes["after"] = json!([99, 0, 0, 0, 0, 80]);
    assert!(serde_json::from_value::<RewriteProposal>(bytes).is_err());
    let duplicate = format!("{{\"original_pc\":4,{}", &valid.to_string()[1..]);
    assert!(serde_json::from_str::<RewriteProposal>(&duplicate).is_err());
}

#[test]
fn proposal_cli_requires_layout_scenarios_and_excludes_plans() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("runtime.hex");
    let fixture = directory.path().join("scenarios.json");
    let proposed = directory.path().join("proposal.json");
    let plan = directory.path().join("plan.json");
    fs::write(&input, DEAD_PUSH).unwrap();
    fs::write(
        &fixture,
        serde_json::to_vec(&scenarios("", 100000)).unwrap(),
    )
    .unwrap();
    fs::write(
        &proposed,
        serde_json::to_vec(&proposal(DEAD_PUSH, 4, "600150600250", "630000000050")).unwrap(),
    )
    .unwrap();
    fs::write(&plan, "{}").unwrap();
    for (index, flags) in [
        vec!["--scenarios"],
        vec!["--preserve-layout"],
        vec!["--preserve-layout", "--cases"],
        vec!["--preserve-layout", "--sequences"],
        vec!["--preserve-layout", "--scenarios", "--plan"],
    ]
    .into_iter()
    .enumerate()
    {
        let out = directory.path().join(format!("invalid-{index}"));
        let mut command = Command::new(env!("CARGO_BIN_EXE_evm-golf"));
        command
            .args(["optimize-runtime", "--bytecode"])
            .arg(&input)
            .arg("--proposal")
            .arg(&proposed)
            .arg("--out")
            .arg(&out);
        for flag in flags {
            command.arg(flag);
            if flag == "--plan" {
                command.arg(&plan);
            } else if flag != "--preserve-layout" {
                command.arg(&fixture);
            }
        }
        let result = command.output().unwrap();
        assert!(!result.status.success(), "invalid combination {index}");
        assert!(!out.join("candidate.hex").exists());
        assert!(!out.join("result.json").exists());
    }
}

#[test]
fn proposal_rejects_stale_sites_push_data_copies_and_changed_stack_profiles() {
    let directory = tempdir().unwrap();
    let mut wrong_hash = proposal(DEAD_PUSH, 4, "600150600250", "630000000050");
    wrong_hash.original_keccak256 = format!("0x{}", "00".repeat(32));
    let protected = "600660065f3960015060025000";
    let push_data = "67600150600250000000";
    let mask = "5f356005565b6001166001165f5260205ff3";
    for (index, (code, proposed)) in [
        (DEAD_PUSH, wrong_hash),
        (
            DEAD_PUSH,
            proposal(DEAD_PUSH, 5, "600150600250", "630000000050"),
        ),
        (
            DEAD_PUSH,
            proposal(DEAD_PUSH, 4, "600350600250", "630000000050"),
        ),
        (
            DEAD_PUSH,
            proposal(DEAD_PUSH, 4, "600150600250", "600150600250"),
        ),
        (DEAD_PUSH, proposal(DEAD_PUSH, 4, "600150600250", "600050")),
        (
            push_data,
            proposal(push_data, 1, "600150600250", "630000000050"),
        ),
        (
            protected,
            proposal(protected, 6, "600150600250", "630000000050"),
        ),
        (mask, proposal(mask, 6, "600116600116", "630000000050")),
    ]
    .into_iter()
    .enumerate()
    {
        let out = directory.path().join(format!("rejected-{index}"));
        assert!(
            runtime::optimize_scenarios_with_proposal(
                &runtime::from_hex(code).unwrap(),
                &scenarios("", 100000),
                &out,
                &proposed,
            )
            .is_err(),
            "invalid proposal {index}"
        );
        assert!(!out.join("candidate.hex").exists());
        assert!(!out.join("result.json").exists());
    }
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn proposal_cli_checks_complete_runtime_and_emits_only_the_proposed_candidate() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("runtime.hex");
    let fixture = directory.path().join("scenarios.json");
    let proposed = directory.path().join("proposal.json");
    let out = directory.path().join("verified");
    fs::write(&input, DEAD_PUSH).unwrap();
    fs::write(
        &fixture,
        serde_json::to_vec(&scenarios("", 100000)).unwrap(),
    )
    .unwrap();
    fs::write(
        &proposed,
        serde_json::to_vec(&proposal(DEAD_PUSH, 4, "600150600250", "630000000050")).unwrap(),
    )
    .unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_evm-golf"))
        .args(["optimize-runtime", "--preserve-layout", "--bytecode"])
        .arg(&input)
        .arg("--scenarios")
        .arg(&fixture)
        .arg("--proposal")
        .arg(&proposed)
        .arg("--out")
        .arg(&out)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert_eq!(
        fs::read_to_string(out.join("candidate.hex"))
            .unwrap()
            .trim(),
        DEAD_CANDIDATE
    );
    let report: Value =
        serde_json::from_slice(&fs::read(out.join("result.json")).unwrap()).unwrap();
    assert_eq!(report["rewrites"].as_array().unwrap().len(), 1);
    assert!(report["lean_version"].is_string());
    assert!(out.join("Rewrites.log").exists());
    assert_eq!(fs::read_to_string(input).unwrap(), DEAD_PUSH);
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn proposal_cannot_hide_false_outputs_or_a_transaction_gas_boundary() {
    let directory = tempdir().unwrap();
    let mask = "5f356005565b6001166001165f5260205ff3";
    // Empty calldata returns zero for both snippets. A finite passing replay must
    // not admit a rewrite that incorrectly clears odd symbolic inputs.
    let false_output = proposal(mask, 6, "600116600116", "610000165f50");
    let dead = proposal(DEAD_PUSH, 4, "600150600250", "630000000050");
    for (name, code, proposed, gas) in [
        ("false-output", mask, false_output, 100000),
        // 17 gas executes the candidate; the original needs22 after intrinsic gas.
        ("gas-boundary", DEAD_PUSH, dead, 21017),
    ] {
        let out = directory.path().join(name);
        assert!(
            runtime::optimize_scenarios_with_proposal(
                &runtime::from_hex(code).unwrap(),
                &scenarios("", gas),
                &out,
                &proposed,
            )
            .is_err()
        );
        assert!(!out.join("candidate.hex").exists());
        assert!(!out.join("result.json").exists());
    }
}
