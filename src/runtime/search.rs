//! Bounded deterministic search. Stage results are evidence for their own inputs;
//! only the root result marks successful final guarded replay.

use super::{
    CaseResult, ReplayPolicy, Report, RewritePlan, RewriteProposalBatch, RewriteProposalSite,
    RewriteSelection, discover_proposals, optimize_scenarios_selected, scenario, thread_sites,
};
use anyhow::{Context as _, Result, ensure};
use revm::primitives::{hex, keccak256};
use serde::Serialize;
use std::{fs, path::Path};

#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum SearchStopReason {
    /// A full round made no changes in either finite search catalog, excluding
    /// sites that failed alone (see `failures`).
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

/// A rejected proposal batch. Its sites were not applied; the search retried
/// with the first half of them, and excludes a site that failed alone.
#[derive(Debug, Serialize)]
pub struct SearchFailure {
    pub directory: String,
    pub sites: usize,
    pub error: String,
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
    /// Proposal batches that failed proof or replay (for example, a timeout).
    pub failures: Vec<SearchFailure>,
    /// Direct original/final guarded replay, in scenario then transaction order.
    pub cases: Vec<CaseResult>,
    pub verification: &'static str,
}

/// Alternate the existing fixed-layout optimizer and bounded proposal discovery.
/// Every stage (including identity stages) uses the existing proof/replay gate.
/// A failed proposal batch is recorded and retried with its first half; a site
/// that fails alone is excluded. Other stage failures abort the search.
/// Final acceptance additionally requires direct original/final guarded replay.
/// Output must be fresh; failures retain stage evidence but no root acceptance.
/// Files are not a crash-atomic transaction: result.json is written last.
pub fn search_scenarios(
    code: &[u8],
    scenarios: &[scenario::Scenario],
    rounds: usize,
    out: &Path,
) -> Result<SearchReport> {
    search_with(code, scenarios, rounds, out, optimize_scenarios_selected)
}

type Stage =
    fn(&[u8], &[scenario::Scenario], &Path, RewriteSelection<'_>) -> Result<(Report, Vec<u8>)>;

fn search_with(
    code: &[u8],
    scenarios: &[scenario::Scenario],
    rounds: usize,
    out: &Path,
    run_stage: Stage,
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
            failures: Vec::new(),
            cases: Vec::new(),
            verification: "Each stage passed local Lean artifact/stack proofs and supplied guarded scenario replay. Final bytes passed direct original/final guarded replay on the supplied fixtures. Convergence covers only the finite built-in and discovery catalogs, minus failed sites listed in failures, not global optimality. No whole-contract, all-input, all-gas, deployment, or code-identity equivalence proof.",
        };
        let mut candidate = code.to_vec();
        // Sites that failed alone; layout-preserving stages keep their offsets.
        let mut excluded: Vec<(usize, String, String)> = Vec::new();
        let key = |site: &RewriteProposalSite| {
            (site.original_pc, site.before.clone(), site.after.clone())
        };
        let mut threads_failed = false;
        for round in 1..=rounds {
            let mut changed = false;
            for kind in ["builtins", "threads", "proposals"] {
                let proposals = kind == "proposals";
                let threads = kind == "threads";
                // Threading runs only when sites exist; a failed threading
                // stage is recorded and threading is not retried.
                let thread_count = if threads && !threads_failed {
                    thread_sites(&candidate)?
                } else {
                    0
                };
                if threads && thread_count == 0 {
                    continue;
                }
                let mut sites: Vec<RewriteProposalSite> = if proposals {
                    discover_proposals(&candidate)?
                        .sites
                        .into_iter()
                        .filter(|site| !excluded.contains(&key(site)))
                        .collect()
                } else {
                    Vec::new()
                };
                for attempt in 0.. {
                    let mut directory = format!("round-{round}-{kind}");
                    if attempt > 0 {
                        directory.push_str(&format!("-retry-{attempt}"));
                    }
                    let input = keccak256(&candidate).to_string();
                    // Empty proposal batches are intentionally invalid at the batch API.
                    // An empty plan checks the identical artifact through the same gate.
                    let identity = RewritePlan {
                        original_keccak256: input.clone(),
                        selected_pcs: Vec::new(),
                    };
                    let batch = RewriteProposalBatch {
                        original_keccak256: input.clone(),
                        sites: sites.clone(),
                    };
                    let selection = if threads {
                        RewriteSelection::Threads
                    } else if !proposals {
                        RewriteSelection::All
                    } else if sites.is_empty() {
                        RewriteSelection::Plan(&identity)
                    } else {
                        RewriteSelection::Proposals(&batch)
                    };
                    let (stage, accepted) =
                        match run_stage(&candidate, scenarios, &out.join(&directory), selection) {
                            Ok(result) => result,
                            // Only discovered batches are retried; every other
                            // stage failure still aborts without acceptance.
                            Err(error) if !sites.is_empty() => {
                                report.failures.push(SearchFailure {
                                    directory,
                                    sites: sites.len(),
                                    error: format!("{error:#}"),
                                });
                                if sites.len() == 1 {
                                    excluded.push(key(&sites[0]));
                                    sites.clear();
                                } else {
                                    sites.truncate(sites.len() / 2);
                                }
                                continue;
                            }
                            Err(error) if threads => {
                                report.failures.push(SearchFailure {
                                    directory,
                                    sites: thread_count,
                                    error: format!("{error:#}"),
                                });
                                threads_failed = true;
                                break;
                            }
                            Err(error) => {
                                return Err(error.context(format!("search stage {directory}")));
                            }
                        };
                    changed |= !stage.rewrites.is_empty();
                    report.stages.push(SearchStage {
                        directory,
                        input_keccak256: input,
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
                    break;
                }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runtime::{Rewrite, from_hex};
    use anyhow::bail;

    fn scenarios() -> Vec<scenario::Scenario> {
        serde_json::from_value(serde_json::json!([{
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

    fn report(code: &[u8], rewrites: Vec<Rewrite>) -> Report {
        Report {
            evm_version: "Cancun",
            baseline_bytes: code.len(),
            candidate_bytes: code.len(),
            rewrites,
            cases: Vec::new(),
            lean_version: None,
            verification: "test stage",
        }
    }

    // Stands in for proof checking: multi-site batches "time out", singletons
    // apply their bytes, and other stages accept the identical artifact.
    fn singletons_only(
        code: &[u8],
        _: &[scenario::Scenario],
        _: &Path,
        selection: RewriteSelection<'_>,
    ) -> Result<(Report, Vec<u8>)> {
        let RewriteSelection::Proposals(batch) = selection else {
            return Ok((report(code, Vec::new()), code.to_vec()));
        };
        if batch.sites.len() > 1 {
            bail!("injected timeout");
        }
        let site = &batch.sites[0];
        let after = from_hex(&site.after)?;
        let mut candidate = code.to_vec();
        candidate[site.original_pc..site.original_pc + after.len()].copy_from_slice(&after);
        let rewrite = Rewrite {
            original_pc: site.original_pc,
            before: site.before.clone(),
            after: site.after.clone(),
            required_stack: 0,
        };
        Ok((report(code, vec![rewrite]), candidate))
    }

    fn always_fails(
        code: &[u8],
        _: &[scenario::Scenario],
        _: &Path,
        selection: RewriteSelection<'_>,
    ) -> Result<(Report, Vec<u8>)> {
        if matches!(selection, RewriteSelection::Proposals(_)) {
            bail!("injected rejection");
        }
        Ok((report(code, Vec::new()), code.to_vec()))
    }

    // Two independent swap windows; each discovered site saves gas.
    const CODE: &str = "5f5f5f5f5f5f5f5f90925090506122709092509050612270505050505000";

    #[test]
    fn failed_batches_are_halved_and_never_accepted() {
        let code = from_hex(CODE).unwrap();
        let sites = discover_proposals(&code).unwrap().sites.len();
        assert!(sites > 1);
        let dir = tempfile::tempdir().unwrap();
        let out = dir.path().join("halved");
        let report = search_with(&code, &scenarios(), 8, &out, singletons_only).unwrap();
        assert_eq!(report.stop_reason, SearchStopReason::Converged);
        assert!(!report.failures.is_empty());
        assert!(report.failures.iter().all(|failure| failure.sites > 1));
        assert_eq!(report.failures[0].directory, "round-1-proposals");
        assert!(
            report
                .stages
                .iter()
                .any(|stage| stage.directory == "round-1-proposals-retry-1")
        );
        let applied: usize = report.stages.iter().map(|stage| stage.rewrites).sum();
        assert_eq!(applied, sites);
        assert!(report.stages.iter().all(|stage| stage.rewrites <= 1));
        assert!(report.cases[0].candidate_gas < report.cases[0].baseline_gas);
        assert!(out.join("result.json").exists());
    }

    #[test]
    fn sites_failing_alone_are_excluded() {
        let code = from_hex(CODE).unwrap();
        let dir = tempfile::tempdir().unwrap();
        let out = dir.path().join("excluded");
        let report = search_with(&code, &scenarios(), 8, &out, always_fails).unwrap();
        assert_eq!(report.stop_reason, SearchStopReason::Converged);
        assert_eq!(report.failures.last().unwrap().sites, 1);
        assert!(report.stages.iter().all(|stage| stage.rewrites == 0));
        assert_eq!(report.candidate_keccak256, report.original_keccak256);
        assert_eq!(report.cases[0].candidate_gas, report.cases[0].baseline_gas);
    }
}
