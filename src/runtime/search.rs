//! Bounded deterministic search. Stage results are evidence for their own inputs;
//! only the root result marks successful final guarded replay.

use super::{
    CaseResult, ReplayPolicy, RewritePlan, RewriteSelection, RuntimeMode, discover_proposals,
    optimize_scenarios_selected, scenario,
};
use anyhow::{Context as _, Result, ensure};
use revm::primitives::{hex, keccak256};
use serde::Serialize;
use std::{fs, path::Path};

#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum SearchStopReason {
    /// A full round made no changes in either finite search catalog.
    Converged,
    RoundsLimit,
}

#[derive(Debug, Serialize)]
pub struct SearchStage {
    pub directory: String,
    pub input_keccak256: String,
    pub output_keccak256: String,
    pub rewrites: usize,
    pub lean_version: Option<String>,
}

#[derive(Debug, Serialize)]
pub struct SearchReport {
    pub evm_version: &'static str,
    pub tool_version: &'static str,
    pub original_keccak256: String,
    pub candidate_keccak256: String,
    /// Hash of the serialized scenarios.json saved beside this report.
    pub scenarios_keccak256: String,
    pub rounds_limit: usize,
    pub rounds_completed: usize,
    pub stop_reason: SearchStopReason,
    pub stages: Vec<SearchStage>,
    /// Direct original/final guarded replay, in scenario then transaction order.
    pub cases: Vec<CaseResult>,
    pub verification: &'static str,
}

/// Alternate the existing fixed-layout optimizer and bounded proposal discovery.
/// Every stage (including identity stages) uses the existing proof/replay gate.
/// Final acceptance additionally requires direct original/final guarded replay.
/// Output must be fresh; failures retain stage evidence but no root acceptance.
/// Files are not a crash-atomic transaction: result.json is written last.
pub fn search_scenarios(
    code: &[u8],
    scenarios: &[scenario::Scenario],
    rounds: usize,
    out: &Path,
) -> Result<SearchReport> {
    ensure!(rounds > 0, "search requires a positive round limit");
    fs::create_dir(out).context("search output directory must be fresh")?;
    let result = (|| {
        let serialized = serde_json::to_vec(scenarios)?;
        fs::write(out.join("original.hex"), hex::encode(code) + "\n")?;
        fs::write(out.join("scenarios.json"), &serialized)?;
        let mut report = SearchReport {
            evm_version: "Cancun",
            tool_version: env!("CARGO_PKG_VERSION"),
            original_keccak256: keccak256(code).to_string(),
            candidate_keccak256: keccak256(code).to_string(),
            scenarios_keccak256: keccak256(&serialized).to_string(),
            rounds_limit: rounds,
            rounds_completed: 0,
            stop_reason: SearchStopReason::RoundsLimit,
            stages: Vec::new(),
            cases: Vec::new(),
            verification: "Each stage passed local Lean artifact/stack proofs and supplied guarded scenario replay. Final bytes passed direct original/final guarded replay on the supplied fixtures. Convergence covers only the finite built-in and discovery catalogs, not global optimality. No whole-contract, all-input, all-gas, deployment, or code-identity equivalence proof.",
        };
        let mut candidate = code.to_vec();
        for round in 1..=rounds {
            let mut changed = false;
            for proposals in [false, true] {
                let directory = format!(
                    "round-{round}-{}",
                    if proposals { "proposals" } else { "builtins" }
                );
                let path = out.join(&directory);
                let discovered = if proposals {
                    Some(discover_proposals(&candidate)?)
                } else {
                    None
                };
                // Empty proposal batches are intentionally invalid at the batch API.
                // An empty plan checks the identical artifact through the same gate.
                let identity = RewritePlan {
                    original_keccak256: keccak256(&candidate).to_string(),
                    selected_pcs: Vec::new(),
                };
                let selection = match &discovered {
                    Some(batch) if !batch.sites.is_empty() => RewriteSelection::Proposals(batch),
                    Some(_) => RewriteSelection::Plan(&identity),
                    None => RewriteSelection::All(RuntimeMode::PreserveLayout),
                };
                let (stage, accepted) =
                    optimize_scenarios_selected(&candidate, scenarios, &path, selection)
                        .with_context(|| format!("search stage {directory}"))?;
                changed |= !stage.rewrites.is_empty();
                report.stages.push(SearchStage {
                    directory,
                    input_keccak256: keccak256(&candidate).to_string(),
                    output_keccak256: keccak256(&accepted).to_string(),
                    rewrites: stage.rewrites.len(),
                    lean_version: stage.lean_version,
                });
                candidate = accepted;
                // Progress is not acceptance, including when a later stage fails.
                fs::write(
                    out.join("stages.json"),
                    serde_json::to_vec_pretty(&report.stages)?,
                )?;
            }
            report.rounds_completed = round;
            if !changed {
                report.stop_reason = SearchStopReason::Converged;
                break;
            }
        }
        for (i, fixture) in scenarios.iter().enumerate() {
            let trace = out.join(format!("final-scenario-{i}-calls"));
            report.cases.extend(
                scenario::replay(
                    code,
                    &candidate,
                    fixture,
                    ReplayPolicy::GuardedCalls(&trace),
                )
                .with_context(|| format!("final original/candidate scenario {i}"))?,
            );
        }
        report.candidate_keccak256 = keccak256(&candidate).to_string();
        // Do all proof/replay work before exposing the root candidate. As with
        // optimize-runtime, an I/O error/crash can leave incomplete output.
        let serialized = serde_json::to_vec_pretty(&report)?;
        fs::write(out.join("candidate.hex"), hex::encode(&candidate) + "\n")?;
        fs::write(out.join("result.json"), serialized)?;
        Ok(report)
    })();
    if let Err(error) = &result {
        fs::write(out.join("failure.log"), format!("{error:#}\n"))?;
    }
    result
}
