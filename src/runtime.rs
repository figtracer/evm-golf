//! Conservative relocation and local rewrites for Cancun runtime bytecode.
//!
//! Lean checks individual gas-erased stack fragments. CFG/relocation are Rust
//! checks; supplied revm cases are finite tests, not whole-contract proofs.

use anyhow::{Context as _, Result, ensure};
use revm::{
    Context, InspectCommitEvm, MainBuilder, MainContext,
    bytecode::{Bytecode, opcode::OpCode},
    context::{BlockEnv, TxEnv, result::ExecutionResult},
    database::InMemoryDB,
    primitives::{Address, B256, Bytes, TxKind, U256, hardfork::SpecId, hex, keccak256},
    state::AccountInfo,
};
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fs,
    path::Path,
    rc::Rc,
};

use crate::proof;

mod artifact;
mod calls;
pub mod input;
mod layout;
mod precompile;
pub mod region;
pub mod scenario;
pub use layout::LayoutAnalysis;

use precompile::EcrecoverTrace;

#[derive(Debug, Clone, Copy)]
pub enum RuntimeMode {
    Compact,
    PreserveLayout,
}

// The plan path always uses fixed layout and explicit account scenarios.
#[derive(Clone, Copy)]
enum RewriteSelection<'a> {
    All(RuntimeMode),
    Plan(&'a RewritePlan),
}

// EIP-170 maximum deployed runtime size. Creation bytecode is not accepted here.
const MAX_RUNTIME_BYTES: usize = 24_576;
const MAX_STACK: usize = 1024;
// Exact provenance states can grow combinatorially at joins. Fail closed after
// 64K retained states or 1M compact stack cells (~2 MiB payload plus containers).
// Queued states share their storage with the retained set through Rc.
const MAX_ANALYSIS_STATES: usize = 65_536;
const MAX_ANALYSIS_CELLS: usize = 1_048_576;
const UNKNOWN: u16 = u16::MAX;

#[derive(Debug, Serialize)]
pub struct Analysis {
    pub runtime_bytes: usize,
    pub reachable_instructions: usize,
    pub max_stack: usize,
    pub relocated_labels: usize,
    #[serde(skip)]
    instructions: Vec<Instruction>,
    #[serde(skip)]
    heights: BTreeMap<usize, BTreeSet<usize>>,
    // Proven label PUSH source PC -> original destination PC.
    #[serde(skip)]
    jumps: BTreeMap<usize, usize>,
}

#[derive(Debug, Clone)]
struct Instruction {
    pc: usize,
    bytes: Vec<u8>,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Case {
    pub calldata: String,
    pub gas_limit: u64,
    #[serde(default)]
    pub value: String,
    #[serde(default, deserialize_with = "input::unique_map")]
    pub storage: BTreeMap<String, String>,
}

/// One transaction in a sequence; storage is initialized once by `Sequence`.
#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Transaction {
    pub calldata: String,
    pub gas_limit: u64,
    #[serde(default)]
    pub value: String,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Sequence {
    #[serde(default, deserialize_with = "input::unique_map")]
    pub storage: BTreeMap<String, String>,
    pub transactions: Vec<Transaction>,
}

pub enum ExecutionInputs<'a> {
    Cases(&'a [Case]),
    Sequences(&'a [Sequence]),
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

/// Analyze all reachable paths, including both conditional edges. Unsupported
/// or ambiguous control flow fails closed; unreachable data is not executed.
pub fn analyze(code: &[u8]) -> Result<Analysis> {
    ensure!(
        code.len() <= MAX_RUNTIME_BYTES,
        "runtime exceeds EIP-170 size limit"
    );
    ensure!(
        !code.starts_with(&[0xef, 0x00]),
        "EOF bytecode is unsupported"
    );
    let instructions = decode(code);
    let index: BTreeMap<_, _> = instructions
        .iter()
        .enumerate()
        .map(|(i, op)| (op.pc, i))
        .collect();
    let mut heights: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    let mut jumps = BTreeMap::new();
    let mut data_uses = BTreeSet::new();
    let initial = Rc::new(Vec::<u16>::new());
    let mut states = BTreeMap::from([(0, BTreeSet::from([Rc::clone(&initial)]))]);
    let mut queue = VecDeque::from([(0, initial)]);
    let mut state_count = 1;
    let mut cell_count = 0;
    let mut max_stack = 0;
    while let Some((pc, incoming)) = queue.pop_front() {
        if pc == code.len() {
            continue;
        }
        let height = incoming.len();
        heights.entry(pc).or_default().insert(height);
        let &i = index.get(&pc).context("control flow enters PUSH data")?;
        let instruction = &instructions[i];
        let op = instruction.bytes[0];
        let Some(info) = OpCode::info_by_op(op) else {
            // revm maps absent opcode entries to OpcodeNotFound, an unconditional
            // exceptional halt. Preserve the byte and stop this path; do not
            // confuse known but unsupported (or fork-disabled) instructions.
            continue;
        };
        ensure!(
            allowed(op)
                || (op == 0x5a
                    && instructions
                        .get(i + 1)
                        .is_some_and(|next| next.bytes[0] == 0xfa))
                || (op == 0xfa && i > 0 && instructions[i - 1].bytes[0] == 0x5a),
            "unsupported or code/gas-sensitive opcode {} (0x{op:02x}) at PC {pc}",
            OpCode::name_by_op(op)
        );
        let size = if (0x60..=0x7f).contains(&op) {
            usize::from(op - 0x5f)
        } else {
            0
        };
        ensure!(
            instruction.bytes.len() == size + 1,
            "truncated PUSH at PC {pc}"
        );
        ensure!(
            height >= info.inputs() as usize,
            "stack underflow at PC {pc}"
        );
        let next_height = height - info.inputs() as usize + info.outputs() as usize;
        ensure!(next_height <= MAX_STACK, "stack overflow at PC {pc}");
        max_stack = max_stack.max(next_height);
        // Stack entries retain the originating PUSH PC, not merely its value.
        // Unknown results cannot become jump destinations in this analysis.
        let mut stack = incoming.as_ref().clone();
        let mut successors = Vec::new();
        match op {
            0x5f..=0x7f => stack.push(pc as u16), // EIP-170 bound fits u16.
            0x80..=0x8f => stack.push(stack[height - usize::from(op - 0x7f)]),
            0x90..=0x9f => stack.swap(height - 1, height - 1 - usize::from(op - 0x8f)),
            0x50 => {
                stack.pop();
            } // Discarded labels reveal no numeric value.
            0x01 | 0x02 | 0x17 | 0x18 => {
                let a = stack.pop().unwrap();
                let b = stack.pop().unwrap();
                let neutral = U256::from(u8::from(op == 0x02));
                // Preserve the other PUSH identity, never just its numeric value.
                // The neutral source is still data: relocating that same source
                // elsewhere would invalidate the identity and must be rejected.
                if let Some(source) = [a, b].into_iter().find(|&source| {
                    source != UNKNOWN
                        && push_value(&instructions[index[&usize::from(source)]].bytes)
                            == Some(neutral)
                }) {
                    data_uses.insert(source);
                    stack.push(if source == a { b } else { a });
                } else {
                    data_uses.extend([a, b]);
                    stack.push(UNKNOWN);
                }
            }
            0xfa => {
                // GAS is consumed immediately. Neither instruction can be a jump
                // entry, so its value cannot escape into other computation.
                let source = stack[height - 2];
                ensure!(
                    source != UNKNOWN
                        && push_value(&instructions[index[&usize::from(source)]].bytes)
                            == Some(U256::from(1)),
                    "STATICCALL at PC {pc} must have proven ECRECOVER address 1"
                );
                // The callee and all memory arguments are data, including any
                // PUSH origin also used elsewhere as a relocatable jump label.
                data_uses.extend(stack.drain(height - 6..height - 1));
                stack.pop(); // Adjacent GAS result.
                stack.push(UNKNOWN);
            }
            0x56 | 0x57 => {
                let source = stack.pop().unwrap();
                ensure!(
                    source != UNKNOWN,
                    "dynamic jump at PC {pc}: unresolved PUSH provenance"
                );
                let source = usize::from(source);
                let value = push_value(&instructions[index[&source]].bytes)
                    .context("invalid label provenance")?;
                let target =
                    usize::try_from(value).context("jump destination exceeds address space")?;
                ensure!(
                    index
                        .get(&target)
                        .is_some_and(|&j| instructions[j].bytes[0] == 0x5b),
                    "invalid jump destination {target} at PC {pc}"
                );
                jumps.insert(source, target);
                successors.push(target);
                if op == 0x57 {
                    data_uses.insert(stack.pop().unwrap()); // Conditions are data.
                }
            }
            _ => {
                for source in stack.drain(height - info.inputs() as usize..) {
                    data_uses.insert(source);
                }
                stack.resize(next_height, UNKNOWN);
            }
        }
        if !matches!(op, 0x00 | 0x56 | 0xf3 | 0xfd | 0xfe) {
            successors.push(pc + instruction.bytes.len());
        }
        let stack = Rc::new(stack);
        for next in successors {
            if next == code.len() {
                continue;
            }
            let at_pc = states.entry(next).or_default();
            if at_pc.contains(&stack) {
                continue;
            }
            ensure!(
                state_count < MAX_ANALYSIS_STATES && cell_count + stack.len() <= MAX_ANALYSIS_CELLS,
                "control-flow provenance analysis budget exhausted; no paths were accepted without analysis"
            );
            state_count += 1;
            cell_count += stack.len();
            at_pc.insert(Rc::clone(&stack));
            queue.push_back((next, Rc::clone(&stack)));
        }
    }
    for source in jumps.keys() {
        ensure!(
            !data_uses.contains(&(*source as u16)),
            "PUSH at PC {source} is used as both a jump label and data"
        );
    }
    Ok(Analysis {
        runtime_bytes: code.len(),
        reachable_instructions: heights.len(),
        max_stack,
        relocated_labels: jumps.len(),
        instructions,
        heights,
        jumps,
    })
}

/// Write a candidate only after local proofs and all supplied differential cases
/// pass. Original input, case inputs, and failure evidence remain on failure.
pub fn optimize(code: &[u8], cases: &[Case], out: &Path) -> Result<Report> {
    optimize_with(
        code,
        ExecutionInputs::Cases(cases),
        out,
        RuntimeMode::Compact,
    )
}

/// Replay each sequence from fresh state, committing between its transactions.
/// `Report::cases` follows input sequence order, then transaction order.
pub fn optimize_sequences(code: &[u8], sequences: &[Sequence], out: &Path) -> Result<Report> {
    optimize_with(
        code,
        ExecutionInputs::Sequences(sequences),
        out,
        RuntimeMode::Compact,
    )
}

/// Select compact relocation or fixed-layout rewrites while retaining the same
/// proof and concrete replay gates. Existing entry points select compact mode.
pub fn optimize_with(
    code: &[u8],
    inputs: ExecutionInputs<'_>,
    out: &Path,
    mode: RuntimeMode,
) -> Result<Report> {
    match inputs {
        ExecutionInputs::Cases(cases) => {
            input::validate(&cases, cases.iter().map(|case| case.gas_limit))?
        }
        ExecutionInputs::Sequences(sequences) => input::validate(
            &sequences,
            sequences
                .iter()
                .flat_map(|s| s.transactions.iter().map(|tx| tx.gas_limit)),
        )?,
    }
    let (filename, serialized, verification) = match inputs {
        ExecutionInputs::Cases(cases) => {
            ensure!(
                !cases.is_empty(),
                "supply at least one differential execution case"
            );
            (
                "cases.json",
                serde_json::to_string(cases)?,
                "Lean: local gas-erased stack rewrites only. Rust: conservative CFG and relocation checks. revm: supplied isolated transactions only. No whole-contract, all-gas, deployment, or code-identity equivalence proof.",
            )
        }
        ExecutionInputs::Sequences(sequences) => {
            ensure!(
                !sequences.is_empty(),
                "supply at least one transaction sequence"
            );
            ensure!(
                sequences.iter().all(|s| !s.transactions.is_empty()),
                "every sequence must contain at least one transaction"
            );
            (
                "sequences.json",
                serde_json::to_string(sequences)?,
                "Lean: local gas-erased stack rewrites only. Rust: conservative CFG and relocation checks. revm: supplied transaction sequences only. No whole-contract, all-gas, deployment, or code-identity equivalence proof.",
            )
        }
    };
    optimize_checked(
        code,
        out,
        RewriteSelection::All(mode),
        false,
        (filename, serialized),
        verification,
        |candidate| match inputs {
            ExecutionInputs::Cases(cases) => cases
                .iter()
                .enumerate()
                .map(|(i, case)| {
                    compare(code, candidate, case).with_context(|| format!("differential case {i}"))
                })
                .collect(),
            ExecutionInputs::Sequences(sequences) => sequences
                .iter()
                .enumerate()
                .map(|(i, sequence)| {
                    compare_sequence(code, candidate, sequence)
                        .with_context(|| format!("differential sequence {i}"))
                })
                .collect::<Result<Vec<_>>>()
                .map(|results| results.into_iter().flatten().collect()),
        },
    )
}

/// Optimize against explicit accounts and constructor-initialized state. The
/// fixed-layout mode also guards calls against the explicit account fixtures.
pub fn optimize_scenarios(
    code: &[u8],
    scenarios: &[scenario::Scenario],
    out: &Path,
    mode: RuntimeMode,
) -> Result<Report> {
    optimize_scenarios_selected(code, scenarios, out, RewriteSelection::All(mode))
}

/// Verify a hash-bound selection through the same proof and replay gates.
pub fn optimize_scenarios_with_plan(
    code: &[u8],
    scenarios: &[scenario::Scenario],
    out: &Path,
    plan: &RewritePlan,
) -> Result<Report> {
    input::validate(plan, std::iter::empty())?;
    optimize_scenarios_selected(code, scenarios, out, RewriteSelection::Plan(plan))
}

fn optimize_scenarios_selected(
    code: &[u8],
    scenarios: &[scenario::Scenario],
    out: &Path,
    selection: RewriteSelection<'_>,
) -> Result<Report> {
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
    let guard_calls = !matches!(selection, RewriteSelection::All(RuntimeMode::Compact));
    optimize_checked(
        code,
        out,
        selection,
        guard_calls,
        ("scenarios.json", serde_json::to_string(scenarios)?),
        "Lean: local gas-erased stack rewrites only. Rust: conservative CFG and relocation checks. revm: supplied account-fixture transactions only. No whole-contract, all-gas, deployment, or code-identity equivalence proof.",
        |candidate| {
            scenarios
                .iter()
                .enumerate()
                .map(|(i, scenario)| {
                    let trace_dir = out.join(format!("scenario-{i}-calls"));
                    let policy = if guard_calls {
                        ReplayPolicy::GuardedCalls(&trace_dir)
                    } else {
                        ReplayPolicy::SuccessfulEcrecover
                    };
                    scenario::replay(code, candidate, scenario, policy)
                        .with_context(|| format!("differential scenario {i}"))
                })
                .collect::<Result<Vec<_>>>()
                .map(|results| results.into_iter().flatten().collect())
        },
    )
}

// One acceptance path for every input format: prove the actual candidate before
// replay and publish it only after all supplied transactions pass.
fn optimize_checked(
    code: &[u8],
    out: &Path,
    selection: RewriteSelection<'_>,
    guard_calls: bool,
    input_file: (&str, String),
    verification: &'static str,
    replay: impl FnOnce(&[u8]) -> Result<Vec<CaseResult>>,
) -> Result<Report> {
    let mode = match selection {
        RewriteSelection::All(mode) => mode,
        RewriteSelection::Plan(_) => RuntimeMode::PreserveLayout,
    };
    let (candidate, rewrites, copies) = match selection {
        RewriteSelection::All(RuntimeMode::Compact) => {
            let (candidate, rewrites) = transform(&analyze(code)?)?;
            (candidate, rewrites, Vec::new())
        }
        RewriteSelection::All(RuntimeMode::PreserveLayout) => {
            let analysis = layout::analyze(code, guard_calls)?;
            let (candidate, rewrites) = layout::transform(&analysis)?;
            (candidate, rewrites, analysis.copies)
        }
        RewriteSelection::Plan(plan) => {
            ensure!(guard_calls, "rewrite plans require account scenarios");
            ensure!(
                plan.original_keccak256
                    .parse::<B256>()
                    .context("invalid plan baseline hash")?
                    == keccak256(code),
                "rewrite plan baseline hash does not match runtime bytecode"
            );
            let analysis = layout::analyze(code, guard_calls)?;
            let (candidate, rewrites) = layout::transform_selected(&analysis, &plan.selected_pcs)?;
            (candidate, rewrites, analysis.copies)
        }
    };
    let verification = match mode {
        RuntimeMode::Compact => verification,
        RuntimeMode::PreserveLayout if guard_calls => {
            "Lean: exact artifact reconstruction, unchanged offsets, certified constant code-copy bytes and local bounded/contextual stack equivalence. revm: supplied account-fixture transactions, guarded nested calls and ordered storage/log effects including reverted effects. No full-EVM correspondence, whole-contract, all-input, all-gas, deployment, or code-identity equivalence proof."
        }
        RuntimeMode::PreserveLayout => {
            "Lean: exact artifact reconstruction, unchanged byte offsets, instruction boundaries, jump destinations, local stack profiles and gas-erased fragment equivalence under complete prefixes/suffixes in the bounded 1024-word model. Rust: conservative reachability; no global stack-height proof. revm: supplied transactions only. No whole-contract, all-gas, deployment, or code-identity equivalence proof."
        }
    };
    fs::create_dir(out)?;
    if let RewriteSelection::Plan(plan) = selection {
        fs::write(
            out.join("plan.json"),
            serde_json::to_string_pretty(plan)? + "\n",
        )?;
    }
    fs::write(out.join("original.hex"), hex::encode(code) + "\n")?;
    fs::write(out.join(input_file.0), input_file.1)?;
    fs::write(
        out.join("rewrites.json"),
        serde_json::to_string_pretty(&rewrites)? + "\n",
    )?;
    // Re-decode and revalidate the emitted control flow independently.
    match mode {
        RuntimeMode::Compact => {
            analyze(&candidate)?;
        }
        RuntimeMode::PreserveLayout => {
            layout::analyze(&candidate, guard_calls)?;
        }
    }
    let lean_version = if rewrites.is_empty() && matches!(mode, RuntimeMode::Compact) {
        None
    } else {
        let path = out.join("Rewrites.lean");
        let (source, names) = match mode {
            RuntimeMode::Compact => certificates(&rewrites)?,
            RuntimeMode::PreserveLayout => {
                artifact::certificate(code, &candidate, &rewrites, &copies)?
            }
        };
        fs::write(&path, source)?;
        Some(proof::verify_named(
            &path,
            &names,
            proof::AxiomPolicy::Foundational,
        )?)
    };
    let checked = replay(&candidate);
    let checked = match checked {
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
        verification,
    };
    fs::write(out.join("candidate.hex"), hex::encode(&candidate) + "\n")?;
    fs::write(
        out.join("result.json"),
        serde_json::to_string_pretty(&report)? + "\n",
    )?;
    Ok(report)
}

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

fn transform(analysis: &Analysis) -> Result<(Vec<u8>, Vec<Rewrite>)> {
    let mut instructions = analysis.instructions.clone();
    let mut rewrites = Vec::new();
    // Each accepted replacement strictly shrinks bytes. Restart locally so folds
    // expose further folds; protected branches and barriers are never consumed.
    let mut i = 0;
    while i < instructions.len() {
        let op = &instructions[i];
        if !analysis.heights.contains_key(&op.pc) || analysis.jumps.contains_key(&op.pc) {
            i += 1;
            continue;
        }
        let available = instructions[i..]
            .iter()
            .take(3)
            .take_while(|op| {
                analysis.heights.contains_key(&op.pc) && !analysis.jumps.contains_key(&op.pc)
            })
            .collect::<Vec<_>>();
        if let Some((count, after, required)) = replacement(&available) {
            let before = available[..count]
                .iter()
                .flat_map(|op| op.bytes.clone())
                .collect::<Vec<_>>();
            if after.len() < before.len() {
                let pc = op.pc;
                rewrites.push(Rewrite {
                    original_pc: pc,
                    before: hex::encode(&before),
                    after: hex::encode(&after),
                    required_stack: required,
                });
                // Replacements can contain multiple instructions. Keep the source
                // span's original PC for proof provenance and reachability only.
                let new = decode(&after).into_iter().map(|mut op| {
                    op.pc = pc;
                    op
                });
                instructions.splice(i..i + count, new);
                i = i.saturating_sub(2);
                continue;
            }
        }
        i += 1;
    }
    let mut positions = BTreeMap::new();
    let mut offset = 0;
    for op in &instructions {
        if op.bytes[0] == 0x5b {
            positions.insert(op.pc, offset);
        }
        offset += op.bytes.len();
    }
    let mut candidate = Vec::with_capacity(offset);
    for op in &instructions {
        if let Some(target) = analysis.jumps.get(&op.pc) {
            let target = *positions
                .get(target)
                .context("lost jump destination during relocation")?;
            let size = op.bytes.len() - 1;
            let value = U256::from(target).to_be_bytes::<32>();
            ensure!(
                value[..32 - size].iter().all(|&b| b == 0),
                "relocated target no longer fits PUSH"
            );
            candidate.push(op.bytes[0]);
            candidate.extend_from_slice(&value[32 - size..]);
        } else {
            candidate.extend_from_slice(&op.bytes);
        }
    }
    Ok((candidate, rewrites))
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

fn certificates(rewrites: &[Rewrite]) -> Result<(String, Vec<String>)> {
    let mut source = format!(
        "{}\n{}\nset_option maxRecDepth 4096\nset_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\nset_option pp.fullNames true\n",
        include_str!("../lean/Model.lean"),
        proof::NORMALIZATION,
    );
    let mut names = Vec::new();
    // Repeated sites share the same local theorem; source locations remain in JSON.
    let mut seen = BTreeSet::new();
    for rewrite in rewrites {
        if !seen.insert((&rewrite.before, &rewrite.after, rewrite.required_stack)) {
            continue;
        }
        let before = from_hex(&rewrite.before)?;
        let after = from_hex(&rewrite.after)?;
        let name = format!("runtime_rewrite_{}", names.len());
        let stack = if rewrite.required_stack == 0 {
            "tail"
        } else {
            "a :: tail"
        };
        source.push_str(&format!("theorem {name} (a x y : Golf.Word) (tail : List Golf.Word) :\n  ∃ output, Golf.run {} {:?} ({stack}) x y = some output ∧\n    Golf.run {} {:?} ({stack}) x y = some output := by\n  refine ⟨_, rfl, ?_⟩\n  simp [Golf.run, Golf.immediate, GolfProof.shift_one, GolfProof.shift_power, BitVec.mul_two, BitVec.two_mul, BitVec.mul_comm]\n#print axioms {name}\n\n", before.len()+1, before, after.len()+1, after));
        names.push(name);
    }
    Ok((source, names))
}

fn compare(original: &[u8], candidate: &[u8], case: &Case) -> Result<CaseResult> {
    compare_results(execute(original, case)?, execute(candidate, case)?)
}

fn compare_sequence(
    original: &[u8],
    candidate: &[u8],
    sequence: &Sequence,
) -> Result<Vec<CaseResult>> {
    let mut left = initial_db(original, &sequence.storage)?;
    let mut right = initial_db(candidate, &sequence.storage)?;
    sequence
        .transactions
        .iter()
        .enumerate()
        .map(|(i, tx)| {
            (|| {
                compare_results(
                    execute_transaction(&mut left, &tx.calldata, tx.gas_limit, &tx.value)?,
                    execute_transaction(&mut right, &tx.calldata, tx.gas_limit, &tx.value)?,
                )
            })()
            .with_context(|| format!("transaction {i}"))
        })
        .collect()
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

fn execute(code: &[u8], case: &Case) -> Result<Execution> {
    let mut db = initial_db(code, &case.storage)?;
    execute_transaction(&mut db, &case.calldata, case.gas_limit, &case.value)
}

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
    let mut keys = BTreeSet::new();
    for (key, value) in storage {
        let key = key.parse::<U256>()?;
        let value = value.parse::<U256>()?;
        ensure!(keys.insert(key), "duplicate numeric storage key");
        db.insert_account_storage(contract, key, value)?;
    }
    Ok(db)
}

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
    use tempfile::tempdir;

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
    fn compact_ecrecover_requires_constant_callee_on_every_path() {
        for code in [
            "5f5f5f5f60015afa5000",   // direct literal
            "60015f5f5f5f845afa5000", // retained PUSH through DUP5
        ] {
            let original = bytes(code);
            let (candidate, _) = transform(&analyze(&original).unwrap()).unwrap();
            analyze(&candidate).unwrap();
            compare(&original, &candidate, &case("")).unwrap();
        }
        for code in [
            "5a50",                                         // escaped gas value
            "5f5f5f5f60015a8050fa5000",                     // gas copied before consumption
            "5f5f5f5f600260fffffa5000",                     // another callee and constant gas
            "5f5f5f5f5f35600e5760016011565b5f355b5afa5000", // unknown callee at join
            "5f5f5f5f5f35600e5760016011565b60025b5afa5000", // literal 1 or 2 at join
        ] {
            assert!(analyze(&bytes(code)).is_err(), "{code}");
        }
        let shared_label = bytes("5f5b60015f5f5f5f845afa5056");
        assert!(
            analyze(&shared_label)
                .unwrap_err()
                .to_string()
                .contains("both a jump label and data")
        );
    }

    #[test]
    fn sequence_detects_divergence_hidden_by_isolated_cases() {
        let original = bytes("5f545f35015f5500"); // accumulate calldata in slot 0
        let candidate = bytes("5f355f5500"); // overwrite slot 0
        let one = format!("{:064x}", 1);
        compare(&original, &candidate, &case(&one)).unwrap();
        let sequence = Sequence {
            storage: BTreeMap::new(),
            transactions: (0..2)
                .map(|_| Transaction {
                    calldata: one.clone(),
                    gas_limit: 200_000,
                    value: String::new(),
                })
                .collect(),
        };
        let error = compare_sequence(&original, &candidate, &sequence).unwrap_err();
        assert!(format!("{error:#}").contains("transaction 1: observable execution mismatch"));
    }

    #[test]
    fn sequence_commits_state_and_rolls_back_reverted_value_writes_and_logs() {
        // Store calldata; revert with a log when calldata is zero.
        let code = bytes("5f35805f55600e575f5fa05f5ffd5b00");
        let initial = BTreeMap::from([("9".into(), "11".into())]);
        let contract = Address::repeat_byte(0x22);
        let caller = Address::repeat_byte(0x11);
        let mut db = initial_db(&code, &initial).unwrap();
        let Execution {
            result: first,
            state: before,
            ..
        } = execute_transaction(&mut db, &format!("{:064x}", 1), 200_000, "7").unwrap();
        assert!(first.is_success());
        assert_eq!(before[&contract].balance, U256::from(7));
        assert_eq!(before[&contract].storage[&U256::ZERO], U256::from(1));
        let Execution {
            result: revert,
            state: after,
            ..
        } = execute_transaction(&mut db, "", 200_000, "3").unwrap();
        assert!(matches!(revert, ExecutionResult::Revert { .. }));
        assert!(revert.logs().is_empty());
        assert_eq!(after[&contract], before[&contract]);
        assert_eq!(after[&caller].balance, U256::MAX - U256::from(7));
        assert_eq!(after[&caller].nonce, 2);
        let Execution {
            result: third,
            state,
            ..
        } = execute_transaction(&mut db, &format!("{:064x}", 2), 200_000, "").unwrap();
        assert!(third.is_success());
        assert_eq!(state[&contract].storage[&U256::ZERO], U256::from(2));
        assert_eq!(state[&contract].storage[&U256::from(9)], U256::from(11));
        assert_eq!(state[&caller].nonce, 3);
        // Invalid transactions commit nothing, including the nonce.
        assert!(execute_transaction(&mut db, "", 20_000, "").is_err());
        assert_eq!(db.load_account(caller).unwrap().info.nonce, 3);
    }

    #[test]
    fn sequence_resets_transient_storage_and_access_warmth() {
        let mut transient =
            initial_db(&bytes("5f5c5f5260015f5d60205ff3"), &BTreeMap::new()).unwrap();
        let mut cold = initial_db(
            &bytes("5f545f5260205ff3"),
            &BTreeMap::from([("0".into(), "7".into())]),
        )
        .unwrap();
        let mut gas = Vec::new();
        for _ in 0..2 {
            let Execution { result: output, .. } =
                execute_transaction(&mut transient, "", 200_000, "").unwrap();
            assert_eq!(output.output().unwrap().as_ref(), &[0; 32]);
            let Execution { result: output, .. } =
                execute_transaction(&mut cold, "", 200_000, "").unwrap();
            assert_eq!(U256::from_be_slice(output.output().unwrap()), U256::from(7));
            gas.push(output.tx_gas_used());
        }
        assert_eq!(gas[0], gas[1]);
    }

    #[test]
    fn sequence_clears_persisted_storage_without_losing_untouched_slots() {
        let code = bytes("5f355f5500");
        let initial = BTreeMap::from([("9".into(), "11".into())]);
        let mut db = initial_db(&code, &initial).unwrap();
        execute_transaction(&mut db, &format!("{:064x}", 7), 200_000, "").unwrap();
        let Execution { state: cleared, .. } =
            execute_transaction(&mut db, "", 200_000, "").unwrap();
        assert_eq!(
            cleared[&Address::repeat_byte(0x22)].storage,
            BTreeMap::from([(U256::from(9), U256::from(11))])
        );
    }

    #[test]
    fn unknown_opcodes_preserve_halt_reason_and_rollback_in_both_modes() {
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
            for mode in [RuntimeMode::Compact, RuntimeMode::PreserveLayout] {
                let (candidate, rewrites) = match mode {
                    RuntimeMode::Compact => transform(&analyze(&original).unwrap()).unwrap(),
                    RuntimeMode::PreserveLayout => {
                        layout::transform(&layout::analyze(&original, false).unwrap()).unwrap()
                    }
                };
                assert!(!rewrites.is_empty());
                assert!(candidate.ends_with(&[op, 0x5a]));
                let right = execute(&candidate, &input).unwrap();
                assert_eq!(left.result, right.result);
                assert_eq!(left.state, right.state);
                // Preserving a halt is not permission to accept halted fixtures.
                assert!(compare(&original, &candidate, &input).is_err());
            }
        }
        assert_eq!(checked, 102); // Revalidate classification when revm changes.
    }

    #[test]
    fn unknown_terminals_do_not_hide_jump_targets_or_push_data() {
        for op in 0..=u8::MAX {
            if OpCode::info_by_op(op).is_some() {
                continue;
            }
            // Either halt at the unknown byte or take a valid branch that has a
            // genuine rewrite. The branch target remains reachable after a halt.
            let original = vec![
                0x5f, 0x35, 0x60, 7, 0x57, op, 0x5a, 0x5b, 0x60, 2, 0x60, 2, 0x02, 0x50, 0x00,
            ];
            for mode in [RuntimeMode::Compact, RuntimeMode::PreserveLayout] {
                let candidate = match mode {
                    RuntimeMode::Compact => transform(&analyze(&original).unwrap()).unwrap().0,
                    RuntimeMode::PreserveLayout => {
                        layout::transform(&layout::analyze(&original, false).unwrap())
                            .unwrap()
                            .0
                    }
                };
                assert_eq!(candidate[5], op);
                compare(&original, &candidate, &case(&format!("{:064x}", 1))).unwrap();
                assert!(compare(&original, &candidate, &case("")).is_err());
            }
            // Jump over the halt to a GAS instruction: this must still reject.
            let jumped = [0x60, 4, 0x56, op, 0x5b, 0x5a];
            assert!(analyze(&jumped).is_err());
            assert!(layout::analyze(&jumped, false).is_err());
            // PUSH data does not terminate the path to unsupported GAS.
            let embedded = [0x60, op, 0x50, 0x5a];
            assert!(analyze(&embedded).is_err());
            assert!(layout::analyze(&embedded, false).is_err());
        }
        for op in [0x1e, 0x4b, 0xe6, 0xe7, 0xe8, 0x39, 0xf1, 0xff] {
            assert!(OpCode::info_by_op(op).is_some());
            assert!(analyze(&[op, 0]).is_err());
            assert!(layout::analyze(&[op, 0], false).is_err());
        }
    }

    #[test]
    fn decoder_and_control_flow_reject_unsupported_paths() {
        for (code, message) in [
            ("600356605b00", "invalid jump"), // 5b is PUSH data, not a target.
            ("5f3556", "dynamic jump"),
            ("6101", "truncated PUSH"),
            ("600057", "stack underflow"),
            ("585000", "code/gas-sensitive"),
            ("595a5000", "code/gas-sensitive"),
            ("4b00", "unsupported"),
            ("ef00", "EOF"),
            ("01", "stack underflow"),
        ] {
            assert!(
                analyze(&bytes(code))
                    .unwrap_err()
                    .to_string()
                    .contains(message),
                "{code}"
            );
        }
        let huge_jump = format!("7f{}56", "ff".repeat(32));
        assert!(
            analyze(&bytes(&huge_jump))
                .unwrap_err()
                .to_string()
                .contains("address space")
        );
        assert!(analyze(&bytes("60585000585a4b6101")).is_ok()); // constants and unreachable tail.
        assert!(analyze(&vec![0x5f; 1024]).is_ok());
        assert!(
            analyze(&vec![0x5f; 1025])
                .unwrap_err()
                .to_string()
                .contains("overflow")
        );
        // An identity cannot hide a transient stack overflow.
        let mut overflowing = vec![0x5f; 1024];
        overflowing.extend_from_slice(&[0x5f, 0x01]);
        assert!(analyze(&overflowing).is_err());
        assert!(analyze(&bytes("5b5f56")).is_ok()); // balanced loop and PUSH0 destination.
        assert!(
            analyze(&bytes("5b5f5f56"))
                .unwrap_err()
                .to_string()
                .contains("analysis budget exhausted")
        );
    }

    #[test]
    fn relocates_both_branches_and_retains_unreachable_bytes() {
        // condition ? store 6 : store 5; shared return. Offsets are original PCs.
        let code = bytes("5f35600e57600060050160195600585b60006006015b5f5260205ff3006101");
        // Construct valid targets from actual JUMPDEST locations, not immediate data.
        let mut code = code;
        let destinations: Vec<_> = decode(&code)
            .iter()
            .filter(|op| op.bytes[0] == 0x5b)
            .map(|op| op.pc)
            .collect();
        code[3] = destinations[0] as u8;
        code[11] = destinations[1] as u8;
        let analysis = analyze(&code).unwrap();
        let (optimized, changes) = transform(&analysis).unwrap();
        assert!(!changes.is_empty());
        assert!(optimized.len() < code.len());
        assert!(optimized.ends_with(&bytes("006101")));
        assert_eq!(analyze(&optimized).unwrap().relocated_labels, 2);
        for calldata in ["0x", "0x01", &format!("0x{}01", "00".repeat(31))] {
            compare(&code, &optimized, &case(calldata)).unwrap();
        }
    }

    #[test]
    fn shares_targets_at_distinct_stack_heights_and_rejects_invalid_edges() {
        // Both branches reach a shared STOP with different stack heights.
        let code = bytes("5f356008575f6008565b00");
        let mut code = code;
        code[3] = 9;
        code[7] = 9;
        let analysis = analyze(&code).unwrap();
        assert_eq!(analysis.heights[&9], BTreeSet::from([0, 1]));
        // A value-dependent condition does not exempt its other edge from checks.
        assert!(analyze(&bytes("5f60065700005b50")).is_err());
    }

    #[test]
    fn resolves_shared_internal_returns_and_rejects_labels_used_as_data() {
        // Call the same helper twice, with different return labels and depths.
        let code = bytes("60056013565b600b6013565b015f5260205ff35b60026003019056");
        let analysis = analyze(&code).unwrap();
        assert_eq!(analysis.relocated_labels, 4);
        assert_eq!(analysis.heights[&19], BTreeSet::from([1, 2]));
        let (candidate, changes) = transform(&analysis).unwrap();
        assert!(!changes.is_empty());
        assert_eq!(analyze(&candidate).unwrap().relocated_labels, 4);
        compare(&code, &candidate, &case("")).unwrap();
        let Execution { result, .. } = execute(&candidate, &case("")).unwrap();
        assert_eq!(
            U256::from_be_slice(result.output().unwrap()),
            U256::from(10)
        );

        for code in [
            "6008805f52565f005b00", // label alias stored to memory.
            "60058057005b00",       // label also consumed as condition.
            "6006805f55565b00",     // label also stored to storage.
        ] {
            assert!(analyze(&bytes(code)).is_err(), "{code}");
        }
        // Neutral arithmetic retains the original PUSH identity.
        assert!(analyze(&bytes("60055f01565b00")).is_ok());
        // Same numeric constant, different source: only the second is a label.
        assert!(analyze(&bytes("60075f526007565b00")).is_ok());
        // Discarding an alias or leaving it below RETURN operands is harmless.
        assert!(analyze(&bytes("60068050565f5b00")).is_ok());
        assert!(analyze(&bytes("600480565b5f5ff3")).is_ok());
    }

    #[test]
    fn neutral_arithmetic_preserves_jump_sources_in_both_operand_orders() {
        for op in [0x01, 0x02, 0x17, 0x18] {
            for reversed in [false, true] {
                for conditional in [false, true] {
                    let neutral = u8::from(op == 0x02);
                    let mut code = bytes("600050"); // Shrinks before the label source.
                    if conditional {
                        code.extend(bytes("6001"));
                    }
                    if reversed {
                        code.extend([0x60, neutral]);
                    }
                    let label = code.len();
                    code.extend([0x61, 0, 0]);
                    if !reversed {
                        code.extend([0x60, neutral]);
                    }
                    // SWAP changes order; DUP/POP must retain the surviving tag.
                    code.extend([0x90, 0x80, 0x50, op]);
                    code.push(if conditional { 0x57 } else { 0x56 });
                    code.push(0x00);
                    let target = code.len();
                    code.extend(bytes("5b60075f5260205ff3"));
                    code[label + 1..label + 3].copy_from_slice(&(target as u16).to_be_bytes());
                    let analysis = analyze(&code).unwrap();
                    assert_eq!(analysis.jumps, BTreeMap::from([(label, target)]));
                    let (candidate, changes) = transform(&analysis).unwrap();
                    assert!(!changes.is_empty());
                    assert_eq!(analyze(&candidate).unwrap().relocated_labels, 1);
                    compare(&code, &candidate, &case("")).unwrap();
                }
            }
        }
    }

    #[test]
    fn neutral_labels_share_targets_and_relocate_across_push_byte_boundaries() {
        let mut code = bytes("6000505f35");
        let first = code.len();
        code.extend(bytes("6101005f0157"));
        let second = code.len();
        code.extend(bytes("6101005f1856"));
        code.resize(256, 0x00);
        code.extend(bytes("5b60075f5260205ff35b60095f5260205ff3"));
        let analysis = analyze(&code).unwrap();
        assert_eq!(
            analysis.jumps,
            BTreeMap::from([(first, 256), (second, 256)])
        );
        let (candidate, _) = transform(&analysis).unwrap();
        let analyzed = analyze(&candidate).unwrap();
        assert_eq!(analyzed.relocated_labels, 2);
        assert!(analyzed.jumps.values().all(|&target| target < 256));
        let one = format!("{:064x}", 1);
        for input in ["", one.as_str()] {
            compare(&code, &candidate, &case(input)).unwrap();
        }
        let source = *analyzed.jumps.keys().next().unwrap();
        let mut stale = candidate.clone();
        stale[source + 1..source + 3].copy_from_slice(&256u16.to_be_bytes());
        assert!(compare(&code, &stale, &case(&one)).is_err());
        // A valid but redirected edge must also fail execution comparison.
        let alternate = decode(&candidate)
            .into_iter()
            .filter(|op| op.bytes[0] == 0x5b)
            .map(|op| op.pc)
            .next_back()
            .unwrap();
        let mut redirected = candidate;
        redirected[source + 1..source + 3].copy_from_slice(&(alternate as u16).to_be_bytes());
        assert!(compare(&code, &redirected, &case(&one)).is_err());
    }

    #[test]
    fn neutral_arithmetic_does_not_hide_data_escapes_or_unknown_targets() {
        for (code, message) in [
            ("6006600101565b00", "unresolved PUSH provenance"), // Non-neutral addition.
            ("5f355f0156", "unresolved PUSH provenance"),       // Unknown calldata.
            ("600b805f015f52566000005b00", "both a jump label and data"), // Memory alias.
            ("6007805f0157005b00", "both a jump label and data"), // Conditional alias.
            ("5b5f8060090150565b00", "both a jump label and data"), // Neutral zero label.
            ("5f5b50600180600b02505f9056", "both a jump label and data"), // Neutral one label.
        ] {
            let error = analyze(&bytes(code)).unwrap_err();
            assert!(error.to_string().contains(message), "{code}: {error}");
        }
    }

    #[test]
    fn preserves_stack_arithmetic_order_and_cascaded_relocations() {
        let samples = [
            "60026003035f5260205ff3",             // 3 - 2, not 2 - 3.
            "60016101001b5f5260205ff3",           // shift by 256.
            "5f3560000160010260011b5f5260205ff3", // arbitrary input identities.
            "5f351919801680175f5260205ff3",       // DUP/AND/OR and complement.
            "5f35610002025f5260205ff3",           // cascaded PUSH -> MUL -> DUP ADD.
            "5f356002576000", // protected jump operand targets PUSH data: reject.
        ];
        for (i, text) in samples.iter().enumerate() {
            let code = bytes(text);
            if i == samples.len() - 1 {
                assert!(analyze(&code).is_err());
                continue;
            }
            let (optimized, _) = transform(&analyze(&code).unwrap()).unwrap();
            analyze(&optimized).unwrap();
            for input in ["", "ff", &"ff".repeat(32)] {
                compare(&code, &optimized, &case(input)).unwrap();
            }
        }
        let code = bytes("6002600301"); // implicit STOP at end of code.
        let (optimized, _) = transform(&analyze(&code).unwrap()).unwrap();
        compare(&code, &optimized, &case("")).unwrap();
    }

    #[test]
    fn checks_storage_logs_reverts_and_gas_failures() {
        for terminal in ["f3", "fd"] {
            // Store calldata+0, emit LOG0, then return/revert the same memory.
            let code = bytes(&format!("5f356000015f555f545f5260205fa060205f{terminal}"));
            let (optimized, _) = transform(&analyze(&code).unwrap()).unwrap();
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
        let (optimized, _) = transform(&analyze(&original).unwrap()).unwrap();
        let mut low = case("");
        low.gas_limit = 21_002;
        assert!(compare(&original, &optimized, &low).is_err());
        // Saving a few gas can cross SSTORE's gas-left sentry even without GAS.
        let original = bytes("60006000015f5500");
        let (optimized, _) = transform(&analyze(&original).unwrap()).unwrap();
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
            let (candidate, rewrites) = transform(&analyze(&code).unwrap()).unwrap();
            assert!(!rewrites.is_empty());
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
            let (candidate, _) = transform(&analyze(&code).unwrap()).unwrap();
            for initial in ["0", "7"] {
                let mut input = case("");
                input.storage.insert("0".into(), initial.into());
                compare(&code, &candidate, &input).unwrap();
            }
        }
        let code = bytes("60006000015f555f60015500");
        let (candidate, _) = transform(&analyze(&code).unwrap()).unwrap();
        let mut input = case("");
        input.storage = BTreeMap::from([("0".into(), "7".into()), ("1".into(), "7".into())]);
        let result = compare(&code, &candidate, &input).unwrap();
        // The seven-gas instruction saving becomes five receipt gas at the cap.
        assert_eq!(
            (result.baseline_gas, result.candidate_gas),
            (24_813, 24_808)
        );
    }

    #[test]
    #[ignore = "requires Lean 4.34.0"]
    fn checks_local_certificates_and_rejects_corruption() {
        let dir = tempdir().unwrap();
        for (i, text) in [
            "5f3560000160010260011b191980165f5260205ff3",
            "60026003036002025f5260205ff3",
            "60016101001b5f5260205ff3",
        ]
        .iter()
        .enumerate()
        {
            let code = bytes(text);
            let report = optimize(
                &code,
                &[case("ff"), case("")],
                &dir.path().join(format!("run{i}")),
            )
            .unwrap();
            assert!(!report.rewrites.is_empty());
            assert!(report.lean_version.is_some());
        }
        let wrong = Rewrite {
            original_pc: 0,
            before: "6001".into(),
            after: "5f".into(),
            required_stack: 0,
        };
        let (source, names) = certificates(&[wrong]).unwrap();
        let path = dir.path().join("Wrong.lean");
        fs::write(&path, source).unwrap();
        assert!(proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational).is_err());
        // Empty-stack identities must not be certified using a missing precondition.
        let wrong = Rewrite {
            original_pc: 0,
            before: "5f01".into(),
            after: "".into(),
            required_stack: 0,
        };
        let (source, names) = certificates(&[wrong]).unwrap();
        let path = dir.path().join("Underflow.lean");
        fs::write(&path, source).unwrap();
        assert!(proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational).is_err());
        // Equality of two failing model executions is not a valid rewrite proof.
        let both_fail = Rewrite {
            original_pc: 0,
            before: "fe".into(),
            after: "fd".into(),
            required_stack: 0,
        };
        let (source, names) = certificates(&[both_fail]).unwrap();
        let path = dir.path().join("BothFail.lean");
        fs::write(&path, source).unwrap();
        assert!(proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational).is_err());
    }
}
