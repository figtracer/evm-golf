use evm_golf::runtime::{self, RewriteProposalBatch, scenario::Scenario};
use revm::primitives::keccak256;
use serde_json::{Value, json};
use std::{fs, process::Command};
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
fn batch_cli_requires_scenarios_layout_and_excludes_other_selections() {
    let directory = tempdir().unwrap();
    for flags in [
        vec![],
        vec!["--preserve-layout"],
        vec!["--scenarios", "fixture.json"],
        vec![
            "--preserve-layout",
            "--scenarios",
            "fixture.json",
            "--proposal",
            "single.json",
        ],
        vec![
            "--preserve-layout",
            "--scenarios",
            "fixture.json",
            "--plan",
            "plan.json",
        ],
    ] {
        let result = Command::new(env!("CARGO_BIN_EXE_evm-golf"))
            .args([
                "optimize-runtime",
                "--bytecode",
                "input.hex",
                "--proposals",
                "batch.json",
                "--out",
            ])
            .arg(directory.path().join("invalid"))
            .args(flags)
            .output()
            .unwrap();
        assert_eq!(result.status.code(), Some(2));
        assert!(!directory.path().join("invalid").exists());
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
            assert_eq!(source.matches("#print axioms").count(), 11);
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
fn batch_binds_heterogeneous_local_proofs_through_the_cli() {
    let directory = tempdir().unwrap();
    let code = format!("{BEFORE}600160081b5000");
    let proposals = batch(
        &code,
        json!([
            {"original_pc":6,"before":"600160081b","after":"6101005f50"},
            {"original_pc":0,"before":BEFORE,"after":AFTER}
        ]),
    );
    let input = directory.path().join("input.hex");
    let proposed = directory.path().join("proposals.json");
    let fixture = directory.path().join("scenarios.json");
    let out = directory.path().join("accepted");
    fs::write(&input, &code).unwrap();
    fs::write(&proposed, serde_json::to_vec(&proposals).unwrap()).unwrap();
    fs::write(&fixture, serde_json::to_vec(&scenarios(100000)).unwrap()).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_evm-golf"))
        .args(["optimize-runtime", "--preserve-layout", "--bytecode"])
        .arg(&input)
        .arg("--proposals")
        .arg(&proposed)
        .arg("--scenarios")
        .arg(&fixture)
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
        format!("{AFTER}6101005f505000")
    );
    assert_eq!(
        fs::read_to_string(out.join("Rewrites.lean"))
            .unwrap()
            .matches("#print axioms")
            .count(),
        21
    );
    let report: Value =
        serde_json::from_slice(&fs::read(out.join("result.json")).unwrap()).unwrap();
    assert_eq!(report["rewrites"][0]["original_pc"], 0);
    assert_eq!(report["rewrites"][1]["original_pc"], 6);
    assert_eq!(fs::read_to_string(input).unwrap(), code);
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
