use evm_golf::runtime::{self, RewriteProposalBatch, scenario::Scenario};
use revm::primitives::keccak256;
use serde_json::{Value, json};
use std::fs;
use tempfile::tempdir;

const BEFORE: &str = "600150600250";
const AFTER: &str = "630000000050";

fn batch(code: &str, sites: Value) -> RewriteProposalBatch {
    serde_json::from_value(json!({
        "original_keccak256": keccak256(runtime::from_hex(code).unwrap()).to_string(),
        "sites": sites,
    }))
    .unwrap()
}

fn sites(count: usize) -> Value {
    json!(
        (0..count)
            .map(|i| json!({"original_pc":i*6,"before":BEFORE,"after":AFTER}))
            .collect::<Vec<_>>()
    )
}

fn scenarios(gas_limit: u64) -> Vec<Scenario> {
    serde_json::from_value(json!([{
        "caller":"0x1111111111111111111111111111111111111111",
        "target":"0x2222222222222222222222222222222222222222",
        "accounts":{
            "0x1111111111111111111111111111111111111111":{"balance":"1000000"},
            "0x2222222222222222222222222222222222222222":{"nonce":1}
        },
        "transactions":[{"calldata":"","gas_limit":gas_limit}]
    }]))
    .unwrap()
}

#[test]
fn batch_rejects_ambiguous_schema_and_invalid_original_intervals() {
    let code = format!("{}00", BEFORE.repeat(2));
    let valid = serde_json::to_value(batch(&code, sites(2))).unwrap();
    for field in ["original_keccak256", "sites"] {
        let mut value = valid.clone();
        value.as_object_mut().unwrap().remove(field);
        assert!(serde_json::from_value::<RewriteProposalBatch>(value).is_err());
    }
    let mut unknown = valid.clone();
    unknown["sites"][0]["proof"] = "by sorry".into();
    assert!(serde_json::from_value::<RewriteProposalBatch>(unknown).is_err());
    let duplicate = format!("{{\"sites\":[],{}", &valid.to_string()[1..]);
    assert!(serde_json::from_str::<RewriteProposalBatch>(&duplicate).is_err());
    let directory = tempdir().unwrap();
    let mut duplicate = sites(2);
    duplicate[1]["original_pc"] = 0.into();
    let mut overlap = sites(2);
    overlap[1]["original_pc"] = 3.into();
    let mut stale = sites(2);
    stale[1]["before"] = AFTER.into();
    let mut wrong_hash = batch(&code, sites(2));
    wrong_hash.original_keccak256 = format!("0x{}", "00".repeat(32));
    for (i, proposal) in [
        batch(&code, json!([])),
        batch(&code, sites(33)),
        batch(&code, duplicate),
        batch(&code, overlap),
        batch(&code, stale),
        wrong_hash,
        batch(
            &code,
            json!([{"original_pc":usize::MAX,"before":BEFORE,"after":AFTER}]),
        ),
    ]
    .iter()
    .enumerate()
    {
        let out = directory.path().join(format!("invalid-{i}"));
        assert!(
            runtime::optimize_scenarios_with_proposals(
                &runtime::from_hex(&code).unwrap(),
                &scenarios(100000),
                &out,
                proposal
            )
            .is_err()
        );
        assert!(!out.join("candidate.hex").exists());
        assert!(!out.join("result.json").exists());
    }
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn batch_checks_adjacent_sites_limit_and_deterministic_order() {
    let directory = tempdir().unwrap();
    for count in [1, 32] {
        let code = format!("{}00", BEFORE.repeat(count));
        let mut proposals = batch(&code, sites(count));
        let mut first_source = None;
        for order in 0..2 {
            let out = directory.path().join(format!("batch-{count}-{order}"));
            let report = runtime::optimize_scenarios_with_proposals(
                &runtime::from_hex(&code).unwrap(),
                &scenarios(100000),
                &out,
                &proposals,
            )
            .unwrap();
            assert_eq!(report.rewrites.len(), count);
            assert_eq!(
                report.cases[0].baseline_gas - report.cases[0].candidate_gas,
                count as u64 * 5
            );
            assert_eq!(
                fs::read_to_string(out.join("candidate.hex"))
                    .unwrap()
                    .trim(),
                format!("{}00", AFTER.repeat(count))
            );
            let source = fs::read_to_string(out.join("Rewrites.lean")).unwrap();
            assert_eq!(source.matches("#print axioms").count(), 13);
            if let Some(previous) = first_source {
                assert_eq!(source, previous);
            }
            first_source = Some(source);
            proposals.sites.reverse();
        }
    }
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn batch_binds_heterogeneous_local_proofs() {
    let directory = tempdir().unwrap();
    let code = format!("{BEFORE}600160081b5000");
    let proposals = batch(
        &code,
        json!([
            {"original_pc":6,"before":"600160081b","after":"6101005f50"},
            {"original_pc":0,"before":BEFORE,"after":AFTER}
        ]),
    );
    let out = directory.path().join("accepted");
    runtime::optimize_scenarios_with_proposals(
        &runtime::from_hex(&code).unwrap(),
        &scenarios(100000),
        &out,
        &proposals,
    )
    .unwrap();
    assert_eq!(
        fs::read_to_string(out.join("candidate.hex"))
            .unwrap()
            .trim(),
        format!("{AFTER}6101005f505000")
    );
    assert_eq!(
        fs::read_to_string(out.join("Rewrites.lean"))
            .unwrap()
            .matches("#print axioms")
            .count(),
        25
    );
    let report: Value =
        serde_json::from_slice(&fs::read(out.join("result.json")).unwrap()).unwrap();
    assert_eq!(report["rewrites"][0]["original_pc"], 0);
    assert_eq!(report["rewrites"][1]["original_pc"], 6);
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn batch_cannot_bypass_the_exceptional_halt_guard() {
    let directory = tempdir().unwrap();
    let code = format!("{}00", BEFORE.repeat(2));
    let bytes = runtime::from_hex(&code).unwrap();
    // The combined candidate fits ten execution gas; the original does not.
    // Even matching exceptional halts are outside guarded replay admission.
    let out = directory.path().join("combined");
    let error = runtime::optimize_scenarios_with_proposals(
        &bytes,
        &scenarios(21010),
        &out,
        &batch(&code, sites(2)),
    )
    .unwrap_err();
    assert!(format!("{error:#}").contains("exceptional call halt: OutOfGas"));
    assert!(out.join("Rewrites.log").exists());
    assert!(out.join("failure.log").exists());
    assert!(!out.join("candidate.hex").exists());
    assert!(!out.join("result.json").exists());
}

const DEAD_PUSH: &str = "6003565b60015060025000";

fn single(code: &str, pc: usize, before: &str, after: &str) -> RewriteProposalBatch {
    batch(
        code,
        json!([{"original_pc":pc,"before":before,"after":after}]),
    )
}

#[test]
fn single_sites_reject_stale_bytes_push_data_copies_and_changed_profiles() {
    let directory = tempdir().unwrap();
    let mut wrong_hash = single(DEAD_PUSH, 4, BEFORE, AFTER);
    wrong_hash.original_keccak256 = format!("0x{}", "00".repeat(32));
    let protected = "600660065f3960015060025000";
    let push_data = "67600150600250000000";
    let mask = "5f356005565b6001166001165f5260205ff3";
    for (index, (code, proposed)) in [
        (DEAD_PUSH, wrong_hash),
        (DEAD_PUSH, single(DEAD_PUSH, 5, BEFORE, AFTER)),
        (DEAD_PUSH, single(DEAD_PUSH, 4, "600350600250", AFTER)),
        (DEAD_PUSH, single(DEAD_PUSH, 4, BEFORE, BEFORE)),
        (DEAD_PUSH, single(DEAD_PUSH, 4, BEFORE, "600050")),
        (push_data, single(push_data, 1, BEFORE, AFTER)),
        (protected, single(protected, 6, BEFORE, AFTER)),
        (mask, single(mask, 6, "600116600116", AFTER)),
    ]
    .into_iter()
    .enumerate()
    {
        let out = directory.path().join(format!("rejected-{index}"));
        assert!(
            runtime::optimize_scenarios_with_proposals(
                &runtime::from_hex(code).unwrap(),
                &scenarios(100000),
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
fn single_site_cannot_hide_false_outputs_or_a_transaction_gas_boundary() {
    let directory = tempdir().unwrap();
    let mask = "5f356005565b6001166001165f5260205ff3";
    // Empty calldata returns zero for both snippets. A finite passing replay must
    // not admit a rewrite that incorrectly clears odd symbolic inputs.
    for (name, code, proposed, gas) in [
        (
            "false-output",
            mask,
            single(mask, 6, "600116600116", "610000165f50"),
            100000,
        ),
        // 17 gas executes the candidate; the original needs 22 after intrinsic gas.
        (
            "gas-boundary",
            DEAD_PUSH,
            single(DEAD_PUSH, 4, BEFORE, AFTER),
            21017,
        ),
    ] {
        let out = directory.path().join(name);
        assert!(
            runtime::optimize_scenarios_with_proposals(
                &runtime::from_hex(code).unwrap(),
                &scenarios(gas),
                &out,
                &proposed,
            )
            .is_err()
        );
        assert!(!out.join("candidate.hex").exists());
        assert!(!out.join("result.json").exists());
    }
}
