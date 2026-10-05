//! Conservative relocation and local rewrites for Cancun runtime bytecode.
//!
//! Lean checks individual gas-erased stack fragments. CFG/relocation are Rust
//! checks; supplied revm cases are finite tests, not whole-contract proofs.

use anyhow::{Context as _, Result, ensure};
use revm::{
    Context, InspectCommitEvm, MainBuilder, MainContext,
    bytecode::opcode::OpCode,
    context::{BlockEnv, TxEnv, result::ExecutionResult},
    database::InMemoryDB,
    primitives::{Address, B256, U256, hardfork::SpecId, hex, keccak256},
};
#[cfg(test)]
use revm::{
    bytecode::Bytecode,
    primitives::{Bytes, TxKind},
    state::AccountInfo,
};
use serde::{Deserialize, Serialize};
use std::{collections::BTreeMap, fs, path::Path};

use crate::proof;

mod artifact;
mod calls;
pub mod input;
mod layout;
mod precompile;
pub mod project;
mod proposal_search;
pub mod region;
pub mod scenario;
mod search;
mod window_proposal;
pub use layout::LayoutAnalysis;
pub use search::{SearchReport, SearchStage, SearchStopReason, search_scenarios};

use precompile::EcrecoverTrace;

// Built-in rewrites (all, or a hash-bound subset) or a discovered/submitted batch.
#[derive(Clone, Copy)]
enum RewriteSelection<'a> {
    All,
    Plan(&'a RewritePlan),
    Proposals(&'a RewriteProposalBatch),
}

// EIP-170 maximum deployed runtime size. Creation bytecode is not accepted here.
const MAX_RUNTIME_BYTES: usize = 24_576;
// Bound aggregate proof generation and site checks under the shared proof deadline.
const MAX_PROPOSAL_SITES: usize = 32;
#[derive(Debug, Clone)]
struct Instruction {
    pc: usize,
    bytes: Vec<u8>,
}

/// Isolated single-transaction fixture used by internal tests.
#[cfg(test)]
#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Case {
    pub calldata: String,
    pub gas_limit: u64,
    #[serde(default)]
    pub value: String,
    #[serde(default, deserialize_with = "input::unique_map")]
    pub storage: BTreeMap<String, String>,
}

/// One transaction. Explicit destinations are supported only by account scenarios.
#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Transaction {
    /// Defaults to the optimized account; requires an explicit account fixture.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub to: Option<String>,
    pub calldata: String,
    pub gas_limit: u64,
    #[serde(default)]
    pub value: String,
}

#[derive(Debug, Serialize)]
pub struct Rewrite {
    pub original_pc: usize,
    pub before: String,
    pub after: String,
    pub required_stack: usize,
}

/// Declarative selection bound to the exact immutable runtime input.
#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct RewritePlan {
    pub original_keccak256: String,
    pub selected_pcs: Vec<usize>,
}

/// Disjoint byte-pair proposals, all bound to the same immutable runtime.
#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct RewriteProposalBatch {
    pub original_keccak256: String,
    pub sites: Vec<RewriteProposalSite>,
}

/// One original-image interval in a proposal batch. Metadata is checker-derived.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct RewriteProposalSite {
    pub original_pc: usize,
    pub before: String,
    pub after: String,
}

#[derive(Debug, Serialize)]
pub struct RewriteOpportunities {
    pub original_keccak256: String,
    pub rewrites: Vec<Rewrite>,
}

#[derive(Debug, Serialize)]
pub struct CaseResult {
    pub baseline_gas: u64,
    pub candidate_gas: u64,
    pub outcome: String,
}

#[derive(Debug, Serialize)]
pub struct Report {
    pub evm_version: &'static str,
    pub baseline_bytes: usize,
    pub candidate_bytes: usize,
    pub rewrites: Vec<Rewrite>,
    pub cases: Vec<CaseResult>,
    pub lean_version: Option<String>,
    pub verification: &'static str,
}

/// Analyze reachable instructions without resolving jump values or stack heights.
pub fn analyze_layout(code: &[u8]) -> Result<LayoutAnalysis> {
    layout::analyze(code, false)
}

/// List trusted fixed-layout sites using the scenario-aware opcode guards.
/// This catalog is not proof or replay evidence for a candidate.
pub fn rewrite_opportunities(code: &[u8]) -> Result<RewriteOpportunities> {
    let analysis = layout::analyze(code, true)?;
    Ok(RewriteOpportunities {
        original_keccak256: keccak256(code).to_string(),
        rewrites: layout::opportunities(&analysis)?,
    })
}

/// Discover a deterministic, bounded set of unverified exact byte-pair proposals.
/// Empty sites means this heuristic found no eligible candidate. Acceptance still
/// requires the existing batch proof and guarded account-scenario replay.
pub fn discover_proposals(code: &[u8]) -> Result<RewriteProposalBatch> {
    proposal_search::discover(code)
}

/// Apply every built-in fixed-layout rewrite, prove the artifact and replay the
/// supplied scenarios with guarded calls.
pub fn optimize_scenarios(
    code: &[u8],
    scenarios: &[scenario::Scenario],
    out: &Path,
) -> Result<Report> {
    optimize_scenarios_selected(code, scenarios, out, RewriteSelection::All)
        .map(|(report, _)| report)
}

/// Prove disjoint original-image proposals together and replay the final candidate.
/// One invalid site, aggregate proof or supplied transaction rejects the entire batch.
pub fn optimize_scenarios_with_proposals(
    code: &[u8],
    scenarios: &[scenario::Scenario],
    out: &Path,
    proposals: &RewriteProposalBatch,
) -> Result<Report> {
    optimize_scenarios_selected(code, scenarios, out, RewriteSelection::Proposals(proposals))
        .map(|(report, _)| report)
}

fn optimize_scenarios_selected(
    code: &[u8],
    scenarios: &[scenario::Scenario],
    out: &Path,
    selection: RewriteSelection<'_>,
) -> Result<(Report, Vec<u8>)> {
    if let RewriteSelection::Proposals(proposals) = selection {
        ensure!(
            !proposals.sites.is_empty() && proposals.sites.len() <= MAX_PROPOSAL_SITES,
            "proposal batch requires 1..={MAX_PROPOSAL_SITES} sites"
        );
        input::validate(proposals, std::iter::empty())?;
    }
    input::validate(
        &scenarios,
        scenarios
            .iter()
            .flat_map(|s| s.transactions.iter().map(|tx| tx.gas_limit)),
    )?;
    ensure!(
        !scenarios.is_empty(),
        "supply at least one fixture scenario"
    );
    ensure!(
        scenarios.iter().all(|s| !s.transactions.is_empty()),
        "every scenario must contain at least one transaction"
    );
    optimize_checked(
        code,
        out,
        selection,
        serde_json::to_string(scenarios)?,
        |candidate| {
            scenarios
                .iter()
                .enumerate()
                .map(|(i, scenario)| {
                    let trace_dir = out.join(format!("scenario-{i}-calls"));
                    scenario::replay(
                        code,
                        candidate,
                        scenario,
                        ReplayPolicy::GuardedCalls(&trace_dir),
                    )
                    .with_context(|| format!("differential scenario {i}"))
                })
                .collect::<Result<Vec<_>>>()
                .map(|results| results.into_iter().flatten().collect())
        },
    )
}

// One acceptance path: prove the actual candidate before replay and publish it
// only after all supplied transactions pass.
fn optimize_checked(
    code: &[u8],
    out: &Path,
    selection: RewriteSelection<'_>,
    scenarios_json: String,
    replay: impl FnOnce(&[u8]) -> Result<Vec<CaseResult>>,
) -> Result<(Report, Vec<u8>)> {
    let analysis = layout::analyze(code, true)?;
    let (candidate, rewrites) = match selection {
        RewriteSelection::All => layout::transform(&analysis)?,
        RewriteSelection::Plan(plan) => {
            ensure!(
                plan.original_keccak256
                    .parse::<B256>()
                    .context("invalid plan baseline hash")?
                    == keccak256(code),
                "rewrite plan baseline hash does not match runtime bytecode"
            );
            layout::transform_selected(&analysis, &plan.selected_pcs)?
        }
        RewriteSelection::Proposals(proposals) => {
            ensure!(
                proposals
                    .original_keccak256
                    .parse::<B256>()
                    .context("invalid proposal baseline hash")?
                    == keccak256(code),
                "rewrite proposal baseline hash does not match runtime bytecode"
            );
            let mut rewrites = proposals
                .sites
                .iter()
                .map(|site| {
                    let before = from_hex(&site.before)?;
                    let after = from_hex(&site.after)?;
                    let local = window_proposal::certificate(&before, &after)
                        .with_context(|| format!("proposal at PC {}", site.original_pc))?;
                    Ok(Rewrite {
                        original_pc: site.original_pc,
                        before: hex::encode(&before),
                        after: hex::encode(&after),
                        required_stack: local.required,
                    })
                })
                .collect::<Result<Vec<_>>>()?;
            rewrites.sort_by_key(|site| site.original_pc);
            let candidate = layout::transform_proposals(&analysis, &rewrites)?;
            (candidate, rewrites)
        }
    };
    let copies = analysis.copies;
    fs::create_dir(out)?;
    if let RewriteSelection::Proposals(proposals) = selection {
        fs::write(
            out.join("proposals.json"),
            serde_json::to_string_pretty(proposals)? + "\n",
        )?;
    }
    fs::write(out.join("original.hex"), hex::encode(code) + "\n")?;
    fs::write(out.join("scenarios.json"), scenarios_json)?;
    fs::write(
        out.join("rewrites.json"),
        serde_json::to_string_pretty(&rewrites)? + "\n",
    )?;
    // Re-decode and revalidate the emitted control flow independently.
    layout::analyze(&candidate, true)?;
    let path = out.join("Rewrites.lean");
    let (source, names) = if matches!(selection, RewriteSelection::Proposals(_)) {
        artifact::proposal_batch_certificate(code, &candidate, &rewrites, &copies)?
    } else {
        artifact::certificate(code, &candidate, &rewrites, &copies)?
    };
    fs::write(&path, source)?;
    let lean_version = Some(proof::verify_named(&path, &names)?);
    let checked = match replay(&candidate) {
        Ok(checked) => checked,
        Err(error) => {
            fs::write(out.join("failure.log"), format!("{error:#}\n"))?;
            return Err(error);
        }
    };
    let report = Report {
        evm_version: "Cancun",
        baseline_bytes: code.len(),
        candidate_bytes: candidate.len(),
        rewrites,
        cases: checked,
        lean_version,
        verification: VERIFICATION,
    };
    fs::write(out.join("candidate.hex"), hex::encode(&candidate) + "\n")?;
    fs::write(
        out.join("result.json"),
        serde_json::to_string_pretty(&report)? + "\n",
    )?;
    Ok((report, candidate))
}

const VERIFICATION: &str = "Lean: exact artifact reconstruction, unchanged offsets, certified constant code-copy bytes and local bounded/contextual stack equivalence. revm: supplied account-fixture transactions, guarded nested calls and ordered storage/log effects including reverted effects. No full-EVM correspondence, whole-contract, all-input, all-gas, deployment, or code-identity equivalence proof.";

/// Decode hexadecimal bytecode/calldata; whitespace is allowed only around it.
pub fn from_hex(input: &str) -> Result<Vec<u8>> {
    hex::decode(input.trim()).context("expected hexadecimal bytes (optional 0x prefix)")
}

fn decode(code: &[u8]) -> Vec<Instruction> {
    let mut instructions = Vec::new();
    let mut pc = 0;
    while pc < code.len() {
        let size = if (0x60..=0x7f).contains(&code[pc]) {
            usize::from(code[pc] - 0x5f)
        } else {
            0
        };
        let end = (pc + size + 1).min(code.len());
        instructions.push(Instruction {
            pc,
            bytes: code[pc..end].to_vec(),
        });
        pc = end;
    }
    instructions
}

fn allowed(op: u8) -> bool {
    // Explicit Cancun allowlist. No calls, creation, gas/code introspection,
    // external-code operations, or selfdestruct. Unreachable bytes are retained.
    matches!(op, 0x00..=0x0b | 0x10..=0x1d | 0x20 | 0x30..=0x37 | 0x3a | 0x3d..=0x3e |
        0x40..=0x4a | 0x50..=0x57 | 0x59 | 0x5b..=0x5f | 0x60..=0x9f | 0xa0..=0xa4 | 0xf3 | 0xfd | 0xfe)
        && OpCode::info_by_op(op).is_some()
}

fn push_value(bytes: &[u8]) -> Option<U256> {
    let op = *bytes.first()?;
    if op == 0x5f {
        return Some(U256::ZERO);
    }
    ((0x60..=0x7f).contains(&op) && bytes.len() == usize::from(op - 0x5f) + 1)
        .then(|| U256::from_be_slice(&bytes[1..]))
}

fn push(value: U256) -> Vec<u8> {
    if value.is_zero() {
        return vec![0x5f];
    }
    let word = value.to_be_bytes::<32>();
    let first = word.iter().position(|&byte| byte != 0).unwrap();
    let mut bytes = vec![0x5f + (32 - first) as u8];
    bytes.extend_from_slice(&word[first..]);
    bytes
}

fn replacement(ops: &[&Instruction]) -> Option<(usize, Vec<u8>, usize)> {
    let a = ops.first()?;
    let b = ops.get(1);
    let c = ops.get(2);
    if let (Some(x), Some(y), Some(c)) = (
        push_value(&a.bytes),
        b.and_then(|b| push_value(&b.bytes)),
        c,
    ) {
        let value = match c.bytes[0] {
            0x01 => Some(y.wrapping_add(x)),
            0x02 => Some(y.wrapping_mul(x)),
            0x03 => Some(y.wrapping_sub(x)),
            0x16 => Some(y & x),
            0x17 => Some(y | x),
            0x18 => Some(y ^ x),
            0x1b => Some(if y >= U256::from(256) {
                U256::ZERO
            } else {
                x << usize::try_from(y).ok()?
            }),
            _ => None,
        };
        if let Some(value) = value {
            return Some((3, push(value), 0));
        }
    }
    if let Some(b) = b {
        if let Some(value) = push_value(&a.bytes) {
            if (value.is_zero() && matches!(b.bytes[0], 0x01 | 0x17 | 0x18))
                || (value == U256::from(1) && b.bytes[0] == 0x02)
            {
                return Some((2, vec![], 1));
            }
            if (value == U256::from(2) && b.bytes[0] == 0x02)
                || (value == U256::from(1) && b.bytes[0] == 0x1b)
            {
                return Some((2, vec![0x80, 0x01], 1));
            }
        }
        if (a.bytes[0] == 0x19 && b.bytes[0] == 0x19)
            || (a.bytes[0] == 0x80 && matches!(b.bytes[0], 0x16 | 0x17))
        {
            return Some((2, vec![], 1));
        }
    }
    push_value(&a.bytes).map(|value| (1, push(value), 0))
}

/// Shared Lean prelude: the bounded word model and shift normalization.
fn prelude() -> String {
    format!(
        "{}\n{}\nset_option maxRecDepth 4096\nset_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\nset_option pp.fullNames true\n",
        include_str!("../lean/Model.lean"),
        proof::NORMALIZATION,
    )
}

#[cfg(test)]
fn compare(original: &[u8], candidate: &[u8], case: &Case) -> Result<CaseResult> {
    compare_results(execute(original, case)?, execute(candidate, case)?)
}

fn compare_results(left: Execution, right: Execution) -> Result<CaseResult> {
    left.precompiles.compare(&right.precompiles)?;
    let Execution {
        result: left,
        state: left_state,
        ..
    } = left;
    let Execution {
        result: right,
        state: right_state,
        ..
    } = right;
    let same_result = match (&left, &right) {
        (
            ExecutionResult::Success {
                reason: a,
                output: x,
                ..
            },
            ExecutionResult::Success {
                reason: b,
                output: y,
                ..
            },
        ) => a == b && x == y,
        (ExecutionResult::Revert { output: a, .. }, ExecutionResult::Revert { output: b, .. }) => {
            a == b
        }
        _ => false, // Halts (including OOG) are never successful validation cases.
    };
    ensure!(
        same_result && left.logs() == right.logs() && left_state == right_state,
        "observable execution mismatch or exceptional halt; baseline={left:?}, candidate={right:?}; baseline state={left_state:?}, candidate state={right_state:?}"
    );
    ensure!(
        right.tx_gas_used() <= left.tx_gas_used(),
        "candidate increased measured gas"
    );
    Ok(CaseResult {
        baseline_gas: left.tx_gas_used(),
        candidate_gas: right.tx_gas_used(),
        outcome: if left.is_success() {
            "success"
        } else {
            "revert"
        }
        .into(),
    })
}

// State projection excludes only the substituted target code hash and uses zero
// gas price. Other code hashes, balances, nonces and nonzero storage are retained.
#[derive(Debug, PartialEq, Eq)]
struct AccountState {
    code_hash: B256,
    balance: U256,
    nonce: u64,
    storage: BTreeMap<U256, U256>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReplayPolicy<'a> {
    Transactions,
    SuccessfulEcrecover,
    GuardedCalls(&'a Path),
}

#[derive(Debug)]
struct Execution {
    result: ExecutionResult,
    state: BTreeMap<Address, AccountState>,
    precompiles: EcrecoverTrace,
}

#[cfg(test)]
fn execute(code: &[u8], case: &Case) -> Result<Execution> {
    let mut db = initial_db(code, &case.storage)?;
    execute_transaction(&mut db, &case.calldata, case.gas_limit, &case.value)
}

#[cfg(test)]
fn initial_db(code: &[u8], storage: &BTreeMap<String, String>) -> Result<InMemoryDB> {
    let contract = Address::repeat_byte(0x22);
    let caller = Address::repeat_byte(0x11);
    let bytecode = Bytecode::new_legacy(Bytes::copy_from_slice(code));
    let mut db = InMemoryDB::default();
    db.insert_account_info(
        contract,
        AccountInfo {
            code_hash: bytecode.hash_slow(),
            code: Some(bytecode),
            ..Default::default()
        },
    );
    db.insert_account_info(
        caller,
        AccountInfo {
            balance: U256::MAX,
            ..Default::default()
        },
    );
    let mut keys = std::collections::BTreeSet::new();
    for (key, value) in storage {
        let key = key.parse::<U256>()?;
        let value = value.parse::<U256>()?;
        ensure!(keys.insert(key), "duplicate numeric storage key");
        db.insert_account_storage(contract, key, value)?;
    }
    Ok(db)
}

#[cfg(test)]
fn execute_transaction(
    db: &mut InMemoryDB,
    calldata: &str,
    gas_limit: u64,
    value: &str,
) -> Result<Execution> {
    let contract = Address::repeat_byte(0x22);
    let caller = Address::repeat_byte(0x11);
    let nonce = db.load_account(caller)?.info.nonce;
    let tx = TxEnv::builder()
        .caller(caller)
        .kind(TxKind::Call(contract))
        .nonce(nonce)
        .gas_limit(gas_limit)
        .gas_price(0)
        .value(if value.is_empty() {
            U256::ZERO
        } else {
            value.parse()?
        })
        .data(Bytes::from(from_hex(calldata)?))
        .build()?;
    execute_env(
        db,
        tx,
        BlockEnv::default(),
        1,
        contract,
        ReplayPolicy::SuccessfulEcrecover,
        None,
    )
}

fn execute_env(
    db: &mut InMemoryDB,
    tx: TxEnv,
    block: BlockEnv,
    chain_id: u64,
    target: Address,
    policy: ReplayPolicy<'_>,
    calls: Option<&mut calls::Calls<'_>>,
) -> Result<Execution> {
    // Each transaction resets warmth/transient state; the database owns durable
    // state. Reverted executions still commit the sender nonce via revm.
    let mut precompiles = EcrecoverTrace::new(policy);
    let context = Context::mainnet()
        .modify_cfg_chained(|cfg| {
            cfg.set_spec_and_mainnet_gas_params(SpecId::CANCUN);
            cfg.chain_id = chain_id;
        })
        .with_block(block)
        .with_db(&mut *db);
    let result = match calls {
        Some(calls) => context
            .build_mainnet_with_inspector((&mut precompiles, calls))
            .inspect_tx_commit(tx)?,
        None => context
            .build_mainnet_with_inspector(&mut precompiles)
            .inspect_tx_commit(tx)?,
    };
    let state = db
        .cache
        .accounts
        .iter()
        .filter_map(|(address, account)| {
            let info = account.info()?;
            Some((
                *address,
                AccountState {
                    // Only the intentionally substituted target is exempt. In
                    // Cancun an existing target cannot delete/redeploy its code.
                    code_hash: if *address == target {
                        B256::ZERO
                    } else {
                        info.code_hash
                    },
                    balance: info.balance,
                    nonce: info.nonce,
                    storage: account
                        .storage
                        .iter()
                        .filter(|(_, value)| !value.is_zero())
                        .map(|(key, value)| (*key, *value))
                        .collect(),
                },
            ))
        })
        .collect();
    Ok(Execution {
        result,
        state,
        precompiles,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use revm::context::result::HaltReason;

    // Drop a leading `PUSH1 0; PUSH1 0; ADD` (or `PUSH1 0; ADD` after a
    // value) for replay-harness tests that need a cheaper equivalent program.
    fn cheaper(code: &[u8]) -> Vec<u8> {
        let text = hex::encode(code);
        let text = if let Some(rest) = text.strip_prefix("6000600001") {
            format!("5f5f{rest}")
        } else {
            text.replacen("600001", "", 1)
        };
        from_hex(&text).unwrap()
    }
    fn fixed(code: &[u8]) -> (Vec<u8>, Vec<Rewrite>) {
        layout::transform(&layout::analyze(code, false).unwrap()).unwrap()
    }
    fn bytes(text: &str) -> Vec<u8> {
        from_hex(text).unwrap()
    }
    fn case(data: &str) -> Case {
        Case {
            calldata: data.into(),
            gas_limit: 200_000,
            value: String::new(),
            storage: BTreeMap::new(),
        }
    }

    #[test]
    fn unknown_opcodes_preserve_halt_reason_and_rollback() {
        let mut checked = 0;
        for op in 0..=u8::MAX {
            if OpCode::info_by_op(op).is_some() {
                continue;
            }
            checked += 1;
            // Rewrite a MUL, write slot zero and emit a log before the unknown
            // instruction. Its exceptional halt rolls back all those effects.
            let mut original = bytes("60026002025060075f555f5fa0");
            original.extend([op, 0x5a]); // Unreachable GAS must remain byte-identical.
            let mut input = case("");
            input.storage.insert("0".into(), "9".into());
            let left = execute(&original, &input).unwrap();
            assert!(
                matches!(
                    left.result,
                    ExecutionResult::Halt {
                        reason: HaltReason::OpcodeNotFound,
                        ..
                    }
                ),
                "{op:02x}"
            );
            assert!(left.result.logs().is_empty());
            assert_eq!(
                left.state[&Address::repeat_byte(0x22)].storage[&U256::ZERO],
                U256::from(9)
            );
            let (candidate, rewrites) = fixed(&original);
            assert!(!rewrites.is_empty());
            assert!(candidate.ends_with(&[op, 0x5a]));
            let right = execute(&candidate, &input).unwrap();
            assert_eq!(left.result, right.result);
            assert_eq!(left.state, right.state);
            // Preserving a halt is not permission to accept halted fixtures.
            assert!(compare(&original, &candidate, &input).is_err());
        }
        assert_eq!(checked, 102); // Revalidate classification when revm changes.
    }

    #[test]
    fn checks_storage_logs_reverts_and_gas_failures() {
        for terminal in ["f3", "fd"] {
            // Store calldata+0, emit LOG0, then return/revert the same memory.
            let code = bytes(&format!("5f356000015f555f545f5260205fa060205f{terminal}"));
            let optimized = cheaper(&code);
            for initial in ["0", "7"] {
                for input in ["", &"ff".repeat(32)] {
                    let mut c = case(input);
                    c.storage.insert("0".into(), initial.into());
                    compare(&code, &optimized, &c).unwrap();
                }
            }
        }
        let mut initial = case("");
        initial.storage.insert("0".into(), "7".into());
        assert!(compare(&bytes("00"), &bytes("5f5f5500"), &initial).is_err());
        // A write rolled back by REVERT leaves the initial nonzero slot intact.
        compare(&bytes("5f5ffd"), &bytes("5f5f555f5ffd"), &initial).unwrap_err(); // extra gas is rejected.
        let Execution {
            state: reverted, ..
        } = execute(&bytes("5f5f555f5ffd"), &initial).unwrap();
        assert_eq!(
            reverted[&Address::repeat_byte(0x22)].storage[&U256::ZERO],
            U256::from(7)
        );
        let original = bytes("600060000100");
        let optimized = cheaper(&original);
        let mut low = case("");
        low.gas_limit = 21_002;
        assert!(compare(&original, &optimized, &low).is_err());
        // Saving a few gas can cross SSTORE's gas-left sentry even without GAS.
        let original = bytes("60006000015f5500");
        let optimized = cheaper(&original);
        low.gas_limit = 23_310;
        assert!(compare(&original, &optimized, &low).is_err());
        assert!(execute(&original, &low).unwrap().result.is_halt());
        assert!(execute(&optimized, &low).unwrap().result.is_success());
        assert!(compare(&bytes("60015f5500"), &bytes("60025f5500"), &case("")).is_err());
        assert!(
            compare(
                &bytes("60015f5260205ff3"),
                &bytes("60025f5260205ff3"),
                &case("")
            )
            .is_err()
        );
    }

    #[test]
    fn every_local_rewrite_family_preserves_the_full_revm_stack() {
        // Serialize every surviving word, including unrelated tail words, to memory.
        // revm's execution is independent of the small Lean fragment interpreter.
        let wrap = |fragment: &[u8], input: &[U256], outputs: usize| {
            let mut code = input
                .iter()
                .flat_map(|&word| push(word))
                .collect::<Vec<_>>();
            code.extend_from_slice(fragment);
            for i in 0..outputs {
                code.extend(push(U256::from(i * 32)));
                code.push(0x52);
            }
            code.extend(push(U256::from(outputs * 32)));
            code.extend([0x5f, 0xf3]);
            code
        };
        let edges = [
            U256::ZERO,
            U256::from(1),
            U256::from(2),
            U256::from(255),
            U256::from(256),
            U256::from(1) << 255,
            U256::MAX - U256::from(1),
            U256::MAX,
        ];
        let tail = [U256::from(0x1234), U256::MAX];
        let mut fragments = vec![
            bytes("6000"),
            bytes("610001"),
            bytes(&format!("7f{}ff", "00".repeat(31))),
        ];
        for x in edges {
            for y in edges {
                for opcode in [0x01, 0x02, 0x03, 0x16, 0x17, 0x18, 0x1b] {
                    let mut fragment = push(x);
                    fragment.extend(push(y));
                    fragment.push(opcode);
                    fragments.push(fragment);
                }
            }
        }
        for text in [
            "5f01", "600017", "600018", "600102", "600202", "60011b", "1919", "8016", "8017",
        ] {
            fragments.push(bytes(text));
        }
        for before in fragments {
            let decoded = decode(&before);
            let refs = decoded.iter().collect::<Vec<_>>();
            let (count, after, required) = replacement(&refs).unwrap();
            assert_eq!(count, decoded.len());
            for a in if required == 0 {
                &edges[..1]
            } else {
                &edges[..]
            } {
                let mut input = tail.to_vec();
                if required == 1 {
                    input.push(*a);
                }
                let outputs = decoded.iter().fold(input.len(), |height, op| {
                    let info = OpCode::info_by_op(op.bytes[0]).unwrap();
                    height - usize::from(info.inputs()) + usize::from(info.outputs())
                });
                compare(
                    &wrap(&before, &input, outputs),
                    &wrap(&after, &input, outputs),
                    &case(""),
                )
                .unwrap_or_else(|error| {
                    panic!(
                        "{} -> {}: {error:#}",
                        hex::encode(&before),
                        hex::encode(&after)
                    )
                });
            }
        }
        // Same top word, corrupted tail: a return-value-only check would miss it.
        let input = [tail[0], tail[1], U256::from(42)];
        assert!(
            compare(
                &wrap(&bytes("6001021919"), &input, 3),
                &wrap(&bytes("90505f90"), &input, 3),
                &case("")
            )
            .unwrap_err()
            .to_string()
            .contains("observable execution mismatch")
        );
    }

    #[test]
    fn runtime_rewrites_preserve_transient_storage_and_memory_copy() {
        for (code, words) in [
            ("5f356000015f5d5f5c5f5260205ff3", 1),
            ("5f356000015f5260205f60205e60405ff3", 2),
        ] {
            let code = bytes(code);
            let candidate = cheaper(&code);
            assert!(candidate.len() < code.len());
            for value in [U256::ZERO, U256::MAX] {
                let data = value.to_be_bytes::<32>();
                let mut input = case(&hex::encode(data));
                input.storage.insert("0".into(), "7".into());
                compare(&code, &candidate, &input).unwrap();
                let Execution { result, state, .. } = execute(&candidate, &input).unwrap();
                assert_eq!(result.output().unwrap().as_ref(), data.repeat(words));
                assert_eq!(
                    state[&Address::repeat_byte(0x22)].storage[&U256::ZERO],
                    U256::from(7)
                );
            }
        }
    }

    #[test]
    fn runtime_receipt_gas_applies_storage_refunds_and_the_refund_cap() {
        for code in ["60006000015f5500", "60006000015f5560075f5500"] {
            let code = bytes(code);
            let candidate = cheaper(&code);
            for initial in ["0", "7"] {
                let mut input = case("");
                input.storage.insert("0".into(), initial.into());
                compare(&code, &candidate, &input).unwrap();
            }
        }
        let code = bytes("60006000015f555f60015500");
        let candidate = cheaper(&code);
        let mut input = case("");
        input.storage = BTreeMap::from([("0".into(), "7".into()), ("1".into(), "7".into())]);
        let result = compare(&code, &candidate, &input).unwrap();
        // The five-gas instruction saving becomes four receipt gas at the cap.
        assert_eq!(
            (result.baseline_gas, result.candidate_gas),
            (24_813, 24_809)
        );
    }
}
