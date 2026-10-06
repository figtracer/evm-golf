//! Project manifests: named contracts with their transaction fixtures, and the
//! three user-facing workflows (inspect, optimize, verify) over them.

use anyhow::{Context as _, Result, ensure};
use revm::primitives::{hex, keccak256};
use serde::{Deserialize, Serialize};
use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
};

use super::{
    CaseResult, MAX_PROPOSAL_SITES, RewriteProposalBatch, RewriteProposalSite, discover_proposals,
    input, optimize_scenarios_with_proposals, scenario::Scenario, search_scenarios,
};

/// Every accepted result carries this scope statement.
pub const SCOPE: &str = "Each accepted change passed local Lean certificates in the documented bounded model and guarded replay of the supplied transactions. This is not a whole-contract, all-input, all-gas, deployment, or code-identity equivalence proof.";

/// `project.json`: paths are relative to the manifest's directory.
#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Manifest {
    pub version: u32,
    pub contracts: Vec<ContractEntry>,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ContractEntry {
    pub id: String,
    /// Hex deployed runtime bytecode with immutables already patched.
    pub runtime: PathBuf,
    /// JSON array of account scenarios (accounts, caller, target, transactions).
    pub scenarios: PathBuf,
}

pub struct Contract {
    pub id: String,
    pub code: Vec<u8>,
    pub scenarios: Vec<Scenario>,
}

/// Exact patches for one or more contracts, each bound to its runtime hash.
/// `inspect` prints this document with discovered (unverified) sites.
#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Proposals {
    pub version: u32,
    pub contracts: Vec<ContractProposals>,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ContractProposals {
    pub id: String,
    pub original_keccak256: String,
    pub sites: Vec<RewriteProposalSite>,
}

#[derive(Debug, Serialize)]
pub struct ContractResult {
    pub id: String,
    pub accepted: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
    pub original_keccak256: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub candidate_keccak256: Option<String>,
    /// Sum over all supplied transactions, original then candidate.
    pub baseline_gas: u64,
    pub candidate_gas: u64,
    pub transactions: usize,
    /// Accepted rewrites (optimize: all stages; verify: submitted sites).
    pub rewrites: usize,
    /// Proposal batches that failed during optimize and were not applied.
    pub failed_batches: usize,
    /// Gas saved per call, grouped by called function.
    pub functions: Vec<FunctionGas>,
}

/// Savings of the supplied transactions that call one function. A function
/// saves different amounts on different paths, so the range is reported.
#[derive(Debug, Serialize)]
pub struct FunctionGas {
    /// Known signature, or the selector.
    pub function: String,
    pub calls: usize,
    pub saved_min: u64,
    pub saved_max: u64,
}

/// Common ERC20 and ERC4626 signatures, named in reports by their selector.
const KNOWN: &[&str] = &[
    "transfer(address,uint256)",
    "transferFrom(address,address,uint256)",
    "approve(address,uint256)",
    "balanceOf(address)",
    "allowance(address,address)",
    "totalSupply()",
    "name()",
    "symbol()",
    "decimals()",
    "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)",
    "nonces(address)",
    "DOMAIN_SEPARATOR()",
    "increaseAllowance(address,uint256)",
    "decreaseAllowance(address,uint256)",
    "mint(address,uint256)",
    "burn(uint256)",
    "burn(address,uint256)",
    "asset()",
    "totalAssets()",
    "convertToShares(uint256)",
    "convertToAssets(uint256)",
    "maxDeposit(address)",
    "previewDeposit(uint256)",
    "deposit(uint256,address)",
    "maxMint(address)",
    "previewMint(uint256)",
    "mint(uint256,address)",
    "maxWithdraw(address)",
    "previewWithdraw(uint256)",
    "withdraw(uint256,address,address)",
    "maxRedeem(address)",
    "previewRedeem(uint256)",
    "redeem(uint256,address,address)",
];

fn function_name(label: &str) -> String {
    KNOWN
        .iter()
        .find(|sig| format!("0x{}", hex::encode(&keccak256(sig.as_bytes())[..4])) == label)
        .map_or_else(|| label.to_owned(), |sig| (*sig).to_owned())
}

fn functions(cases: &[CaseResult]) -> Vec<FunctionGas> {
    let mut groups: std::collections::BTreeMap<&str, Vec<u64>> = Default::default();
    for case in cases {
        groups
            .entry(case.function.as_str())
            .or_default()
            .push(case.baseline_gas - case.candidate_gas);
    }
    groups
        .into_iter()
        .map(|(label, saved)| FunctionGas {
            function: function_name(label),
            calls: saved.len(),
            saved_min: *saved.iter().min().expect("nonempty group"),
            saved_max: *saved.iter().max().expect("nonempty group"),
        })
        .collect()
}

#[derive(Debug, Serialize)]
pub struct ProjectResult {
    pub scope: &'static str,
    pub contracts: Vec<ContractResult>,
}

fn valid_id(id: &str) -> bool {
    (1..=64).contains(&id.len())
        && id
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
}

/// Load and validate a manifest, keeping only the selected contract IDs (all
/// when `select` is empty).
pub fn load(path: &Path, select: &[String]) -> Result<Vec<Contract>> {
    let manifest: Manifest = serde_json::from_str(&input::read_json(path)?)
        .with_context(|| format!("invalid project manifest {}", path.display()))?;
    ensure!(manifest.version == 1, "unsupported project version");
    ensure!(!manifest.contracts.is_empty(), "project lists no contracts");
    let root = path.parent().unwrap_or(Path::new(""));
    let mut ids = BTreeSet::new();
    for entry in &manifest.contracts {
        ensure!(
            valid_id(&entry.id),
            "contract id {:?} must be 1-64 ASCII letters, digits, '-' or '_'",
            entry.id
        );
        ensure!(ids.insert(&entry.id), "duplicate contract id {}", entry.id);
    }
    for id in select {
        ensure!(ids.contains(id), "unknown contract id {id}");
    }
    let mut contracts = Vec::new();
    for entry in manifest.contracts {
        if !select.is_empty() && !select.contains(&entry.id) {
            continue;
        }
        let code = input::read_bytecode(&root.join(&entry.runtime))
            .with_context(|| format!("contract {}", entry.id))?;
        let scenarios: Vec<Scenario> =
            serde_json::from_str(&input::read_json(&root.join(&entry.scenarios))?)
                .with_context(|| format!("contract {} scenarios", entry.id))?;
        ensure!(
            !scenarios.is_empty() && scenarios.iter().all(|s| !s.transactions.is_empty()),
            "contract {} needs at least one scenario with a transaction",
            entry.id
        );
        contracts.push(Contract {
            id: entry.id,
            code,
            scenarios,
        });
    }
    Ok(contracts)
}

/// Discover bounded, unverified proposals for every contract.
pub fn inspect(contracts: &[Contract]) -> Result<Proposals> {
    let mut out = Vec::new();
    for contract in contracts {
        let batch = discover_proposals(&contract.code)
            .with_context(|| format!("contract {}", contract.id))?;
        out.push(ContractProposals {
            id: contract.id.clone(),
            original_keccak256: batch.original_keccak256,
            sites: batch.sites,
        });
    }
    Ok(Proposals {
        version: 1,
        contracts: out,
    })
}

fn totals(cases: &[CaseResult]) -> (u64, u64) {
    cases.iter().fold((0, 0), |(base, cand), case| {
        (base + case.baseline_gas, cand + case.candidate_gas)
    })
}

fn rejected(contract: &Contract, error: anyhow::Error) -> ContractResult {
    ContractResult {
        id: contract.id.clone(),
        accepted: false,
        error: Some(format!("{error:#}")),
        original_keccak256: keccak256(&contract.code).to_string(),
        candidate_keccak256: None,
        baseline_gas: 0,
        candidate_gas: 0,
        transactions: 0,
        rewrites: 0,
        failed_batches: 0,
        functions: Vec::new(),
    }
}

/// Bounded search per contract. Each contract is an independent job: results
/// do not cover interacting contracts replaced together.
pub fn optimize(contracts: &[Contract], rounds: usize, out: &Path) -> Result<ProjectResult> {
    fs::create_dir(out).context("output directory must be new")?;
    let mut results = Vec::new();
    for contract in contracts {
        eprintln!("optimizing {}", contract.id);
        let result = match search_scenarios(
            &contract.code,
            &contract.scenarios,
            rounds,
            &out.join(&contract.id),
        ) {
            Ok(report) => {
                let (baseline_gas, candidate_gas) = totals(&report.cases);
                ContractResult {
                    id: contract.id.clone(),
                    accepted: true,
                    error: None,
                    original_keccak256: report.original_keccak256,
                    candidate_keccak256: Some(report.candidate_keccak256),
                    baseline_gas,
                    candidate_gas,
                    transactions: report.cases.len(),
                    rewrites: report.stages.iter().map(|stage| stage.rewrites).sum(),
                    failed_batches: report.failures.len(),
                    functions: functions(&report.cases),
                }
            }
            Err(error) => rejected(contract, error),
        };
        results.push(result);
    }
    finish(&contracts.iter().collect::<Vec<_>>(), results, out)
}

/// Check exact submitted patches. Every site of a contract must pass, or that
/// contract is rejected unchanged.
pub fn verify(contracts: &[Contract], proposals: &Proposals, out: &Path) -> Result<ProjectResult> {
    ensure!(proposals.version == 1, "unsupported proposals version");
    ensure!(
        !proposals.contracts.is_empty(),
        "proposals list no contracts"
    );
    let mut ids = BTreeSet::new();
    for entry in &proposals.contracts {
        ensure!(
            ids.insert(&entry.id),
            "duplicate proposals for {}",
            entry.id
        );
        ensure!(
            contracts.iter().any(|c| c.id == entry.id),
            "proposals name unknown contract {}",
            entry.id
        );
        ensure!(
            (1..=MAX_PROPOSAL_SITES).contains(&entry.sites.len()),
            "contract {} needs 1..={MAX_PROPOSAL_SITES} sites",
            entry.id
        );
    }
    fs::create_dir(out).context("output directory must be new")?;
    let mut checked = Vec::new();
    let mut results = Vec::new();
    for entry in &proposals.contracts {
        let contract = contracts.iter().find(|c| c.id == entry.id).unwrap();
        checked.push(contract);
        eprintln!("verifying {}", contract.id);
        let batch = RewriteProposalBatch {
            original_keccak256: entry.original_keccak256.clone(),
            sites: entry.sites.clone(),
        };
        let result = match optimize_scenarios_with_proposals(
            &contract.code,
            &contract.scenarios,
            &out.join(&contract.id),
            &batch,
        ) {
            Ok(report) => {
                let (baseline_gas, candidate_gas) = totals(&report.cases);
                let candidate = super::from_hex(&fs::read_to_string(
                    out.join(&contract.id).join("candidate.hex"),
                )?)?;
                ContractResult {
                    id: contract.id.clone(),
                    accepted: true,
                    error: None,
                    original_keccak256: keccak256(&contract.code).to_string(),
                    candidate_keccak256: Some(keccak256(&candidate).to_string()),
                    baseline_gas,
                    candidate_gas,
                    transactions: report.cases.len(),
                    rewrites: report.rewrites.len(),
                    failed_batches: 0,
                    functions: functions(&report.cases),
                }
            }
            Err(error) => rejected(contract, error),
        };
        results.push(result);
    }
    finish(&checked, results, out)
}

/// Write `result.json` and `baseline/project.json` (the next baseline):
/// accepted contracts use their candidate, rejected ones keep the original.
fn finish(
    contracts: &[&Contract],
    results: Vec<ContractResult>,
    out: &Path,
) -> Result<ProjectResult> {
    let baseline = out.join("baseline");
    fs::create_dir(&baseline)?;
    let mut entries = Vec::new();
    for (contract, result) in contracts.iter().zip(&results) {
        let runtime = if result.accepted {
            fs::read_to_string(out.join(&contract.id).join("candidate.hex"))?
        } else {
            super::hex::encode(&contract.code) + "\n"
        };
        let runtime_path = format!("{}.hex", contract.id);
        let scenarios_path = format!("{}.scenarios.json", contract.id);
        fs::write(baseline.join(&runtime_path), runtime)?;
        fs::write(
            baseline.join(&scenarios_path),
            serde_json::to_vec_pretty(&contract.scenarios)?,
        )?;
        entries.push(ContractEntry {
            id: contract.id.clone(),
            runtime: runtime_path.into(),
            scenarios: scenarios_path.into(),
        });
    }
    fs::write(
        baseline.join("project.json"),
        serde_json::to_vec_pretty(&Manifest {
            version: 1,
            contracts: entries,
        })?,
    )?;
    let result = ProjectResult {
        scope: SCOPE,
        contracts: results,
    };
    fs::write(out.join("result.json"), serde_json::to_vec_pretty(&result)?)?;
    Ok(result)
}
