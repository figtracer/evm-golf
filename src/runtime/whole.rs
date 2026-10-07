//! Whole-program refinement certificates against pinned EVMYulLean.
//!
//! The generator covers every instruction reachable from pc 0 or a JUMPDEST and
//! emits one Lean obligation per instruction. Lean then proves, for the whole
//! program, that every successful or reverting original run is matched by the
//! candidate. Only small images with the supported opcode profile are accepted.

use anyhow::{Context as _, Result, bail, ensure};
use revm::primitives::{U256, hex, keccak256};
use serde::Serialize;
use std::{collections::BTreeSet, fmt::Write as _, fs, path::Path};

use super::{Instruction, decode};

mod facts;
use crate::proof;

/// Obligations decode through a byte-list lemma, so per-instruction cost is
/// nearly independent of image size; the limit is EIP-170.
pub const MAX_WHOLE_BYTES: usize = super::MAX_RUNTIME_BYTES;

#[derive(Debug, Serialize)]
pub struct WholeCertificate {
    pub claim: &'static str,
    pub original_keccak256: String,
    pub candidate_keccak256: String,
    pub runtime_bytes: usize,
    pub covered_instructions: usize,
    /// (pc, stack facts) pairs; a pc reached in several contexts counts once per context.
    pub checked_entries: usize,
    /// Whether entries carry stack facts (only when a window needs them).
    pub stack_facts: bool,
    pub power_sites: Vec<usize>,
    pub thread_sites: Vec<usize>,
    pub window_sites: Vec<usize>,
    /// Call instructions, with the GAS directly before them.
    pub call_sites: Vec<usize>,
    /// CODECOPY instructions; each copies a constant range on which the images agree.
    pub codecopy_sites: Vec<usize>,
    /// Constant addresses read by EXTCODEHASH or EXTCODECOPY; assumed not to be the owner.
    pub inspected: Vec<usize>,
    pub assumptions: Vec<&'static str>,
    pub unproved: Vec<&'static str>,
    pub lean_version: String,
}

#[derive(Clone)]
struct PowerSite {
    pc: usize,
    width: usize,
    exponent: usize,
}

/// `PUSHn from; JUMPI` rewritten to `PUSHn to; JUMPI`, where `from` holds the
/// unchanged trampoline `JUMPDEST; PUSHm to; JUMP`.
#[derive(Clone)]
struct ThreadSite {
    pc: usize,
    width: usize,
    from: usize,
    to: usize,
    to_width: usize,
}

/// Equal-length straight-line stack windows (PUSH, DUP, SWAP, POP).
#[derive(Clone)]
struct WindowSite {
    pc: usize,
    end: usize,
    old: Vec<(usize, Vec<u8>)>,
    new: Vec<(usize, Vec<u8>)>,
}

/// A call opcode, optionally with the GAS that feeds it directly before.
#[derive(Clone)]
struct CallSite {
    op: u8,
    /// Stack inputs of the call opcode.
    inputs: usize,
    gas_first: bool,
}

impl CallSite {
    fn len(&self) -> usize {
        if self.gas_first { 2 } else { 1 }
    }
    /// Slots popped from the stack at the point: GAS pushes the gas argument itself.
    fn pop(&self) -> usize {
        self.inputs - usize::from(self.gas_first)
    }
    fn lean(&self) -> (&'static str, &'static str) {
        match self.op {
            0xf1 => ("Operation.CALL", "CallOp.call"),
            0xf2 => ("Operation.CALLCODE", "CallOp.callcode"),
            0xf4 => ("Operation.DELEGATECALL", "CallOp.delegatecall"),
            _ => ("Operation.STATICCALL", "CallOp.staticcall"),
        }
    }
}

#[derive(Clone)]
enum Site {
    Power(PowerSite),
    Thread(ThreadSite),
    Window(WindowSite),
}

impl Site {
    fn pc(&self) -> usize {
        match self {
            Site::Power(s) => s.pc,
            Site::Thread(s) => s.pc,
            Site::Window(s) => s.pc,
        }
    }
    /// Both sites are PUSHn followed by one opcode.
    fn end(&self) -> usize {
        match self {
            Site::Power(s) => s.pc + s.width + 2,
            Site::Thread(s) => s.pc + s.width + 2,
            Site::Window(s) => s.end,
        }
    }
}

enum Obligation {
    Same {
        op: String,
        arg: String,
        same: String,
        len: usize,
    },
    Jump,
    Jumpi,
    Halt {
        op: &'static str,
        which: &'static str,
        congruent: &'static str,
    },
    FallOff,
    Invalid,
    Power(PowerSite),
    Thread(ThreadSite),
    Window(WindowSite),
    Call(CallSite),
    /// A code copy; its offset and size must be constants at every entry.
    CodeCopy,
    /// EXTCODEHASH or EXTCODECOPY; the address must be a constant at every entry.
    ExtCode {
        hash: bool,
    },
}

pub fn certify(original: &[u8], candidate: &[u8], out: &Path) -> Result<WholeCertificate> {
    let plan = plan(original, candidate)?;
    fs::create_dir(out)
        .with_context(|| format!("use a new output directory: {}", out.display()))?;
    fs::write(out.join("original.hex"), hex::encode(original) + "\n")?;
    fs::write(out.join("candidate.hex"), hex::encode(candidate) + "\n")?;
    let modules = render(original, candidate, &plan);
    for (name, source) in &modules {
        fs::write(out.join(format!("{name}.lean")), source)?;
    }
    let names: Vec<String> = modules.iter().map(|(name, _)| name.clone()).collect();
    let lean_version = proof::verify_region(out, proof::RegionKind::Whole(&names))?;
    let report = WholeCertificate {
        claim: "whole-program refinement of the interpreter X, code execution Ξ, message call Θ and transaction Υ",
        original_keccak256: keccak256(original).to_string(),
        candidate_keccak256: keccak256(candidate).to_string(),
        runtime_bytes: original.len(),
        covered_instructions: plan.analysis.obligations.len(),
        checked_entries: plan.analysis.entries.values().map(Vec::len).sum(),
        stack_facts: plan.precise,
        power_sites: plan
            .points()
            .filter_map(|(pc, obligation)| {
                matches!(obligation, Obligation::Power(_)).then_some(*pc)
            })
            .collect(),
        thread_sites: plan
            .points()
            .filter_map(|(pc, obligation)| {
                matches!(obligation, Obligation::Thread(_)).then_some(*pc)
            })
            .collect(),
        window_sites: plan
            .points()
            .filter_map(|(pc, obligation)| {
                matches!(obligation, Obligation::Window(_)).then_some(*pc)
            })
            .collect(),
        call_sites: plan
            .points()
            .filter_map(|(pc, obligation)| matches!(obligation, Obligation::Call(_)).then_some(*pc))
            .collect(),
        codecopy_sites: plan
            .points()
            .filter_map(|(pc, obligation)| {
                matches!(obligation, Obligation::CodeCopy).then_some(*pc)
            })
            .collect(),
        inspected: plan.inspected.clone(),
        assumptions: {
            let mut list = vec![
                "Ξ: a fresh call frame whose current and original account maps differ only in the owner's deployed code; X: states at pc 0 equal except deployed code, execution count and extra candidate gas",
                "valid jump tables are computed by the checked-scanner profile of D_J",
                "if the original returns success or revert, so does the candidate with the same fuel or more, with equal output; on success, related account maps, equal substate and no less gas; on revert, no less gas; the candidate never ends with more gas than it started with",
            ];
            if !plan.inspected.is_empty() {
                list.push("the constant addresses read by EXTCODEHASH or EXTCODECOPY (result.json `inspected`) are not the owner");
            }
            if plan.calls() {
                list.push("CalleeSummary: a callee other than the owner's code, run on related account maps with at least the original's gas, returns the same created set, substate, status and output, related account maps, no less gas than the original and no more than it was given; the original's callee keeps the owner's account");
                list.push("Reentry: calls back into the owner's code return success or revert in the original run (ecrecover_summary shows CalleeSummary holds for the ecrecover precompile given at least 3000 gas)");
                list.push("the owner is not a precompile address");
            }
            list
        },
        unproved: {
            let mut list = vec![
                "Θ and Υ for calls and transactions that do not target the owner directly",
                "opcodes outside the supported profile: creation, GAS that does not directly feed a call, CODECOPY whose range is not constant or is changed by a rewrite, and EXTCODEHASH or EXTCODECOPY with a non-constant address",
                "exceptional original runs (the claim is conditioned on original success or revert)",
                "revm correspondence",
            ];
            if plan.calls() {
                list.push("callee behaviour outside CalleeSummary and Reentry, for example a callee that reads the owner's code or that runs out of gas only in the original");
            }
            list
        },
        lean_version,
    };
    fs::write(
        out.join("result.json"),
        serde_json::to_string_pretty(&report)? + "\n",
    )?;
    Ok(report)
}

struct Plan {
    analysis: facts::Analysis,
    jumpdests: Vec<usize>,
    /// Entries carry stack facts because some window needs them.
    precise: bool,
    /// Sorted constant addresses read by EXTCODEHASH or EXTCODECOPY.
    inspected: Vec<usize>,
}

impl Plan {
    fn points(&self) -> impl Iterator<Item = (&usize, &Obligation)> {
        self.analysis.obligations.iter()
    }

    /// Some reached instruction is a call; the certificate then needs the call assumptions.
    fn calls(&self) -> bool {
        self.points().any(|(_, o)| matches!(o, Obligation::Call(_)))
    }

    /// The final theorems take environment assumptions.
    fn assumes(&self) -> bool {
        self.calls() || !self.inspected.is_empty()
    }
}

fn plan(original: &[u8], candidate: &[u8]) -> Result<Plan> {
    ensure!(
        original.len() == candidate.len(),
        "whole-program certificates need equal-length images"
    );
    ensure!(
        !original.is_empty() && original.len() <= MAX_WHOLE_BYTES,
        "whole-program certificates accept 1..={MAX_WHOLE_BYTES} runtime bytes"
    );
    let instructions = decode(original);
    let starts: BTreeSet<usize> = instructions.iter().map(|i| i.pc).collect();
    let jumpdests = jump_table(original);
    ensure!(
        jumpdests == jump_table(candidate),
        "rewrite changes the valid jump table"
    );
    // Facts of the unchanged original choose window boundaries; the final
    // analysis then treats each rewrite site as one step.
    let first = facts::analyze(original, &jumpdests, true, &mut |pc| {
        obligation_at(original, &instructions, &starts, &[], pc)
    })?;
    let env_at = |pc: usize| facts::env(&facts::joined(&first, pc));
    let sites = power_sites(original, candidate, &instructions, &starts, &env_at)?;
    // Facts multiply the entries; use them only when some window needs them or a
    // code copy must have a constant range.
    let precise = sites.iter().any(|site| match site {
        Site::Window(w) => !window_check(&w.old, &w.new, &[]),
        _ => false,
    }) || first
        .obligations
        .values()
        .any(|o| matches!(o, Obligation::CodeCopy | Obligation::ExtCode { .. }));
    let analysis = facts::analyze(original, &jumpdests, precise, &mut |pc| {
        obligation_at(original, &instructions, &starts, &sites, pc)
    })?;
    let mut inspected = BTreeSet::new();
    for (pc, list) in &analysis.entries {
        match analysis.obligations.get(pc) {
            Some(Obligation::ExtCode { .. }) => {
                for fs in list {
                    let addr = constant(fs, 0).with_context(|| {
                        format!(
                            "external code read at pc {pc} needs a constant address on every path"
                        )
                    })?;
                    inspected.insert(addr);
                }
            }
            Some(Obligation::Window(site)) => {
                for fs in list {
                    ensure!(
                        window_check(&site.old, &site.new, &facts::env(fs)),
                        "the window at pc {pc} needs stack facts that do not hold on every path"
                    );
                }
            }
            Some(Obligation::CodeCopy) => {
                for fs in list {
                    let (off, len) = codecopy_range(fs).with_context(|| {
                        format!(
                            "CODECOPY at pc {pc} needs a constant offset and size on every path"
                        )
                    })?;
                    let lo = off.min(original.len());
                    let hi = (off + len).min(original.len());
                    ensure!(
                        original[lo..hi] == candidate[lo..hi],
                        "CODECOPY at pc {pc} copies bytes {off}..{} that a rewrite changes",
                        off + len
                    );
                }
            }
            _ => {}
        }
    }
    Ok(Plan {
        analysis,
        jumpdests,
        precise,
        inspected: inspected.into_iter().collect(),
    })
}

/// The constant value of slot `i`, from the facts about the inputs.
fn constant(fs: &[facts::Abs], i: usize) -> Option<usize> {
    match fs.get(i).and_then(|a| a.set.as_deref()) {
        Some([v]) => usize::try_from(*v).ok(),
        _ => None,
    }
}

/// The constant offset and size a code copy reads, from the facts about its inputs.
fn codecopy_range(fs: &[facts::Abs]) -> Option<(usize, usize)> {
    Some((constant(fs, 1)?, constant(fs, 2)?))
}

/// The obligation at a pc that execution reaches. Bytes such as trailing
/// metadata that no execution reaches need none.
fn obligation_at(
    original: &[u8],
    instructions: &[Instruction],
    starts: &BTreeSet<usize>,
    sites: &[Site],
    pc: usize,
) -> Result<Obligation> {
    if pc >= original.len() {
        return Ok(Obligation::FallOff);
    }
    ensure!(
        starts.contains(&pc),
        "execution reaches pc {pc}, which is not an instruction boundary"
    );
    if let Some(site) = sites.iter().find(|s| s.pc() == pc) {
        return Ok(match site.clone() {
            Site::Power(power) => Obligation::Power(power),
            Site::Thread(thread) => Obligation::Thread(thread),
            Site::Window(window) => Obligation::Window(window),
        });
    }
    ensure!(
        !sites.iter().any(|s| s.pc() < pc && pc < s.end()),
        "execution reaches pc {pc} inside a rewrite site"
    );
    let index = instructions
        .binary_search_by_key(&pc, |i| i.pc)
        .expect("boundary has an instruction");
    classify(&instructions[index], instructions.get(index + 1))
}

fn push_width(op: u8) -> usize {
    if (0x60..=0x7f).contains(&op) {
        usize::from(op - 0x5f)
    } else {
        0
    }
}

/// JUMPDEST offsets at instruction boundaries, in scan order.
fn jump_table(code: &[u8]) -> Vec<usize> {
    decode(code)
        .iter()
        .filter(|i| i.bytes[0] == 0x5b)
        .map(|i| i.pc)
        .collect()
}

/// Every byte difference must lie inside `PUSHn 2^k; MUL` rewritten to `PUSHn k; SHL`.
fn power_sites(
    original: &[u8],
    candidate: &[u8],
    instructions: &[Instruction],
    starts: &BTreeSet<usize>,
    env_at: &dyn Fn(usize) -> Vec<usize>,
) -> Result<Vec<Site>> {
    let instruction_at = |pc: usize| instructions.iter().find(|i| i.pc == pc);
    let mut sites: Vec<Site> = Vec::new();
    for (pc, (a, b)) in original.iter().zip(candidate).enumerate() {
        if a == b || sites.last().is_some_and(|s| pc < s.end()) {
            continue;
        }
        let start = *starts
            .range(..=pc)
            .next_back()
            .context("difference before the first instruction")?;
        let index = instructions
            .iter()
            .position(|i| i.pc == start)
            .expect("start is an instruction");
        let push = &instructions[index];
        let width = push_width(push.bytes[0]);
        let next = instructions.get(index + 1);
        let value = U256::from_be_slice(&push.bytes[1..]);
        let replaced = U256::from_be_slice(&candidate[start + 1..start + 1 + width]);
        let same_push = width > 0 && candidate[start] == push.bytes[0];
        // Jump threading: only the destination immediate changes.
        if let (true, Some(jumpi)) = (same_push, next)
            && jumpi.bytes == [0x57]
            && candidate[jumpi.pc] == 0x57
            && pc < jumpi.pc
        {
            let from = value.to::<usize>();
            let to = replaced.to::<usize>();
            let trampoline = (instruction_at(from), instruction_at(from + 1));
            if let (Some(dest), Some(push2)) = trampoline
                && value < U256::from(original.len())
                && dest.bytes == [0x5b]
                && push_width(push2.bytes[0]) > 0
                && U256::from_be_slice(&push2.bytes[1..]) == replaced
                && instruction_at(from + 1 + push2.bytes.len()).is_some_and(|j| j.bytes == [0x56])
                && original[from..from + 2 + push2.bytes.len()]
                    == candidate[from..from + 2 + push2.bytes.len()]
            {
                sites.push(Site::Thread(ThreadSite {
                    pc: start,
                    width,
                    from,
                    to,
                    to_width: push2.bytes.len() - 1,
                }));
                continue;
            }
        }
        let exponent = (width > 0 && value.count_ones() == 1).then(|| value.trailing_zeros());
        match (exponent, next) {
            (Some(k), Some(mul))
                if mul.bytes == [0x02]
                    && same_push
                    && candidate[mul.pc] == 0x1b
                    && replaced == U256::from(k)
                    && pc < mul.pc + 1 =>
            {
                sites.push(Site::Power(PowerSite {
                    pc: start,
                    width,
                    exponent: k,
                }))
            }
            _ => {
                // A window may need a few unchanged instructions before the
                // first difference, e.g. `PUSH0 DUP1` -> `PUSH0 PUSH0`.
                let floor = sites.last().map_or(0, Site::end);
                let mut error = None;
                let mut found = None;
                // Prefer a window that needs no stack facts.
                'search: for facts in [false, true] {
                    for back in 0..8 {
                        let Some(at) = index.checked_sub(back) else {
                            break;
                        };
                        let begin = &instructions[at];
                        if begin.pc < floor || (back > 0 && !window_op(&begin.bytes)) {
                            break;
                        }
                        let env = if facts { env_at(begin.pc) } else { Vec::new() };
                        match window_site(original, candidate, begin.pc, pc, &env) {
                            Ok(site) => {
                                found = Some(site);
                                break 'search;
                            }
                            Err(e) => error = error.or(Some(e)),
                        }
                    }
                }
                match found {
                    Some(site) => sites.push(Site::Window(site)),
                    None => return Err(error.expect("at least one attempt")),
                }
            }
        }
    }
    Ok(sites)
}

/// Binary window opcodes in the order of the Lean `BinK` constructors.
const BINARY: [u8; 20] = [
    0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x0b, 0x10, 0x11, 0x12, 0x13, 0x14, 0x16, 0x17, 0x18,
    0x1a, 0x1b, 0x1c, 0x1d,
];
/// Unary window opcodes in the order of the Lean `UnK` constructors.
const UNARY: [u8; 2] = [0x15, 0x19];

fn window_op(bytes: &[u8]) -> bool {
    (matches!(bytes[0], 0x5f..=0x7f | 0x80..=0x9f | 0x50)
        || BINARY.contains(&bytes[0])
        || UNARY.contains(&bytes[0]))
        && bytes.len() == push_width(bytes[0]) + 1
}

/// The smallest span from `start`, ending at a common instruction boundary after
/// every differing byte, whose two sides pass the window check. Only window
/// opcodes may appear on either side.
fn window_site(
    original: &[u8],
    candidate: &[u8],
    start: usize,
    first: usize,
    env: &[usize],
) -> Result<WindowSite> {
    const MAX_WINDOW: usize = 48;
    let step = |code: &[u8], pc: usize| (pc + push_width(code[pc]) + 1).min(code.len());
    let (mut o, mut c) = (start, start);
    let mut old = Vec::new();
    let mut new = Vec::new();
    let mut last = first;
    loop {
        if o == c && o > last {
            let same = o >= original.len()
                || original[o..step(original, o)] == candidate[o..step(candidate, o)];
            if same && window_check(&old, &new, env) {
                return Ok(WindowSite {
                    pc: start,
                    end: o,
                    old,
                    new,
                });
            }
        }
        ensure!(
            old.len() + new.len() < MAX_WINDOW && o < original.len() && c < candidate.len(),
            "unsupported difference at byte {first}: not a power, threading or stack-window rewrite"
        );
        if o <= c {
            let next = step(original, o);
            old.push((o, original[o..next].to_vec()));
            o = next;
        } else {
            let next = step(candidate, c);
            new.push((c, candidate[c..next].to_vec()));
            c = next;
        }
        ensure!(
            old.iter().chain(&new).all(|(_, b)| window_op(b)),
            "unsupported difference at byte {first}: not a power, threading or stack-window rewrite"
        );
        let reach = o.max(c);
        if let Some(d) = (last..reach).rev().find(|&i| original[i] != candidate[i]) {
            last = last.max(d);
        }
    }
}

#[derive(Clone, PartialEq)]
enum Sym {
    Input(usize),
    Lit(U256),
    Un(u8, Box<Sym>),
    Bin(u8, Box<Sym>, Box<Sym>),
}

const ADD: u8 = 0x01;
const MUL: u8 = 0x02;
const SUB: u8 = 0x03;
const DIV: u8 = 0x04;
const LT: u8 = 0x10;
const SLT: u8 = 0x12;
const EQ: u8 = 0x14;
const ISZERO: u8 = 0x15;
const AND: u8 = 0x16;
const OR: u8 = 0x17;

fn index(table: &[u8], op: u8) -> usize {
    table.iter().position(|&o| o == op).unwrap()
}

/// Mirror of the Lean `Sym.lt`.
fn sym_lt(a: &Sym, b: &Sym) -> bool {
    use Sym::*;
    match (a, b) {
        (Lit(x), Lit(y)) => x < y,
        (Lit(_), _) => true,
        (Input(_), Lit(_)) => false,
        (Input(i), Input(j)) => i < j,
        (Input(_), _) => true,
        (Un(f, x), Un(g, y)) if f == g => sym_lt(x, y),
        (Un(f, _), Un(g, _)) => index(&UNARY, *f) < index(&UNARY, *g),
        (Un(..), Bin(..)) => true,
        (Un(..), _) => false,
        (Bin(f, x, y), Bin(g, z, w)) if f == g => {
            if x == z {
                sym_lt(y, w)
            } else {
                sym_lt(x, z)
            }
        }
        (Bin(f, ..), Bin(g, ..)) => index(&BINARY, *f) < index(&BINARY, *g),
        (Bin(..), _) => false,
    }
}

/// Interpreter result of a foldable binary opcode on (top, second).
fn bin_value(op: u8, a: U256, b: U256) -> U256 {
    let bit = |c: bool| U256::from(u8::from(c));
    let shift = |f: fn(U256, usize) -> U256| {
        if a >= U256::from(256) {
            U256::ZERO
        } else {
            f(b, a.to::<usize>())
        }
    };
    match op {
        ADD => a.wrapping_add(b),
        MUL => a.wrapping_mul(b),
        SUB => a.wrapping_sub(b),
        DIV => a.checked_div(b).unwrap_or_default(),
        0x06 => a.checked_rem(b).unwrap_or_default(),
        LT => bit(a < b),
        0x11 => bit(a > b),
        EQ => bit(a == b),
        AND => a & b,
        OR => a | b,
        0x18 => a ^ b,
        0x1b => shift(|v, k| v << k),
        _ => shift(|v, k| v >> k),
    }
}

fn ident(op: u8) -> Option<U256> {
    match op {
        ADD | OR | 0x18 => Some(U256::ZERO),
        MUL => Some(U256::from(1)),
        AND => Some(U256::MAX),
        _ => None,
    }
}

fn flat(op: u8, s: Sym, out: &mut Vec<Sym>) {
    match s {
        Sym::Bin(g, a, b) if g == op => {
            flat(op, *a, out);
            flat(op, *b, out);
        }
        s => out.push(s),
    }
}

/// Mirror of the Lean `Sym.bits`: an upper bound on the bit length of a value,
/// given bounds `env` on the inputs.
fn bits(s: &Sym, env: &[usize]) -> usize {
    match s {
        Sym::Input(i) => env.get(*i).copied().unwrap_or(256),
        Sym::Un(0x19, _) => 256,
        Sym::Lit(v) => 256 - v.leading_zeros(),
        Sym::Un(..) => 1,
        Sym::Bin(op, a, b) => match *op {
            AND => bits(a, env).min(bits(b, env)),
            OR | 0x18 => bits(a, env).max(bits(b, env)),
            LT | 0x11 | SLT | 0x13 | EQ => 1,
            DIV | 0x06 => bits(a, env),
            0x1c => bits(b, env),
            _ => 256,
        },
    }
}

/// Mirror of the Lean `acNorm`: fold literals, drop a literal mask that keeps
/// every bit the other operands can have, sort operands, drop duplicates of
/// idempotent operators and rebuild a right-nested term.
fn ac_norm(op: u8, e: U256, list: Vec<Sym>, env: &[usize]) -> Sym {
    let mut c = e;
    let mut rest = Vec::new();
    for s in list {
        match s {
            Sym::Lit(v) => c = bin_value(op, c, v),
            s => rest.push(s),
        }
    }
    let absorb = match op {
        MUL | AND => Some(U256::ZERO),
        OR => Some(U256::MAX),
        _ => None,
    };
    let low = rest.iter().map(|s| bits(s, env)).fold(256, usize::min);
    let ones = if low >= 256 {
        U256::MAX
    } else {
        (U256::from(1) << low) - U256::from(1)
    };
    if op == AND && c & ones == ones {
        c = e;
    }
    if absorb == Some(c) {
        return Sym::Lit(c);
    }
    rest.sort_by(|x, y| {
        if sym_lt(x, y) {
            std::cmp::Ordering::Less
        } else if x == y {
            std::cmp::Ordering::Equal
        } else {
            std::cmp::Ordering::Greater
        }
    });
    if matches!(op, AND | OR) {
        rest.dedup();
    }
    if c != e {
        rest.insert(0, Sym::Lit(c));
    }
    let mut it = rest.into_iter().rev();
    let Some(mut acc) = it.next() else {
        return Sym::Lit(e);
    };
    for s in it {
        acc = Sym::Bin(op, Box::new(s), Box::new(acc));
    }
    acc
}

fn pow2(k: U256) -> U256 {
    U256::from(1) << k.to::<usize>()
}

/// Mirror of the Lean `normOp`.
fn norm_op(op: u8, a: Sym, b: Sym, env: &[usize]) -> Sym {
    let zero = Sym::Lit(U256::ZERO);
    let big = |k: &U256| *k >= U256::from(256);
    let bin = |f: u8, x: Sym, y: Sym| Sym::Bin(f, Box::new(x), Box::new(y));
    match (op, a, b) {
        (SUB, a, b) if a == b => zero,
        (SUB, a, Sym::Lit(c)) => {
            let mut l = Vec::new();
            flat(ADD, a, &mut l);
            l.push(Sym::Lit(U256::ZERO.wrapping_sub(c)));
            ac_norm(ADD, U256::ZERO, l, env)
        }
        (0x1b, Sym::Lit(k), _) if big(&k) => zero,
        (0x1b, Sym::Lit(k), b) => {
            let mut l = Vec::new();
            flat(MUL, b, &mut l);
            l.push(Sym::Lit(pow2(k)));
            ac_norm(MUL, U256::from(1), l, env)
        }
        (0x1c, Sym::Lit(k), _) if big(&k) => zero,
        (0x1c, Sym::Lit(k), b) if k.is_zero() => b,
        (0x1c, Sym::Lit(k), b) => bin(DIV, b, Sym::Lit(pow2(k))),
        (0x11, a, b) => bin(LT, b, a),
        (0x13, a, b) => bin(SLT, b, a),
        (EQ, a, b) if b == zero => Sym::Un(ISZERO, Box::new(a)),
        (EQ, a, b) if a == zero => Sym::Un(ISZERO, Box::new(b)),
        (EQ, a, b) if sym_lt(&b, &a) => bin(EQ, b, a),
        (op, a, b) => bin(op, a, b),
    }
}

/// Mirror of the Lean `norm`: a canonical form modulo commutativity,
/// associativity, identities and a few strength reductions.
fn norm(s: &Sym, env: &[usize]) -> Sym {
    match s {
        Sym::Un(op, a) => match norm(a, env) {
            Sym::Lit(x) if *op == ISZERO => Sym::Lit(U256::from(u8::from(x.is_zero()))),
            Sym::Lit(x) => Sym::Lit(!x),
            Sym::Un(ISZERO, y) if *op == ISZERO && bits(&y, env) <= 1 => *y,
            a => Sym::Un(*op, Box::new(a)),
        },
        Sym::Bin(op, a, b) => {
            let (a, b) = (norm(a, env), norm(b, env));
            if let Some(e) = ident(*op) {
                let mut l = Vec::new();
                flat(*op, a, &mut l);
                flat(*op, b, &mut l);
                return ac_norm(*op, e, l, env);
            }
            match (&a, &b) {
                (Sym::Lit(x), Sym::Lit(y))
                    if matches!(*op, SUB | DIV | 0x06 | LT | 0x11 | EQ | 0x1b | 0x1c) =>
                {
                    Sym::Lit(bin_value(*op, *x, *y))
                }
                _ => norm_op(*op, a, b, env),
            }
        }
        s => s.clone(),
    }
}

/// Mirror of the Lean `srun`: the symbolic stack (top first), the number of
/// inputs pulled, the height after each instruction and the gas cost.
fn sym_run(instrs: &[(usize, Vec<u8>)]) -> (Vec<Sym>, usize, Vec<i64>, usize) {
    let (mut a, mut m, mut heights, mut cost) = (Vec::<Sym>::new(), 0usize, Vec::new(), 0usize);
    for (_, b) in instrs {
        let (need, c) = match b[0] {
            0x02 | 0x04..=0x07 | 0x0b => (2, 5),
            op if BINARY.contains(&op) => (2, 3),
            op if UNARY.contains(&op) => (1, 3),
            0x5f => (0, 2),
            0x60..=0x7f => (0, 3),
            op @ 0x80..=0x8f => (usize::from(op - 0x7f), 3),
            op @ 0x90..=0x9f => (usize::from(op - 0x8f) + 1, 3),
            _ => (1, 2),
        };
        // `a` is top first; pull missing inputs from below.
        while a.len() < need {
            a.push(Sym::Input(m));
            m += 1;
        }
        match b[0] {
            0x5f..=0x7f => a.insert(0, Sym::Lit(U256::from_be_slice(&b[1..]))),
            op @ 0x80..=0x8f => a.insert(0, a[usize::from(op - 0x80)].clone()),
            op @ 0x90..=0x9f => a.swap(0, usize::from(op - 0x8f)),
            op if BINARY.contains(&op) => {
                let x = a.remove(0);
                let y = a.remove(0);
                a.insert(0, Sym::Bin(op, Box::new(x), Box::new(y)));
            }
            op if UNARY.contains(&op) => {
                let x = a.remove(0);
                a.insert(0, Sym::Un(op, Box::new(x)));
            }
            _ => {
                a.remove(0);
            }
        }
        cost += c;
        heights.push(a.len() as i64 - m as i64);
    }
    (a, m, heights, cost)
}

/// Mirror of the Lean `windowCheck`; Lean decides it again in the certificate.
fn window_check(old: &[(usize, Vec<u8>)], new: &[(usize, Vec<u8>)], env: &[usize]) -> bool {
    let (mut an, mn, hn, cn) = sym_run(new);
    let (ao, mo, ho, co) = sym_run(old);
    if mn > mo {
        return false;
    }
    an.extend((mn..mo).map(Sym::Input));
    an.iter()
        .map(|s| norm(s, env))
        .eq(ao.iter().map(|s| norm(s, env)))
        && cn <= co
        && new.len() <= old.len()
        && !old.is_empty()
        && hn.iter().all(|h| ho.iter().any(|g| h <= g))
}

fn classify(instruction: &Instruction, next: Option<&Instruction>) -> Result<Obligation> {
    let op = instruction.bytes[0];
    let call = |op: u8, gas_first: bool| {
        Obligation::Call(CallSite {
            op,
            inputs: if matches!(op, 0xf1 | 0xf2) { 7 } else { 6 },
            gas_first,
        })
    };
    let simple = |name: &str| Obligation::Same {
        op: format!("Operation.{name}"),
        arg: "none".to_owned(),
        same: format!("same_{}", name.to_lowercase()),
        len: 1,
    };
    Ok(match op {
        0x60..=0x7f => {
            let width = instruction.bytes.len() - 1;
            Obligation::Same {
                op: format!("(Operation.Push .PUSH{width})"),
                arg: format!(
                    "(some (UInt256.ofNat {}, {width}))",
                    U256::from_be_slice(&instruction.bytes[1..])
                ),
                same: format!("(same_push .PUSH{width} (by decide))"),
                len: width + 1,
            }
        }
        0x5f => Obligation::Same {
            op: "(Operation.Push .PUSH0)".to_owned(),
            arg: "none".to_owned(),
            same: "same_push0".to_owned(),
            len: 1,
        },
        0x80..=0x8f => simple(&format!("DUP{}", op - 0x7f)),
        0x90..=0x9f => simple(&format!("SWAP{}", op - 0x8f)),
        0x38 | 0x3b => Obligation::Same {
            op: format!(
                "Operation.{}",
                if op == 0x38 {
                    "CODESIZE"
                } else {
                    "EXTCODESIZE"
                }
            ),
            arg: "none".to_owned(),
            same: format!(
                "({}_same size_eq)",
                if op == 0x38 {
                    "codesize"
                } else {
                    "extcodesize"
                }
            ),
            len: 1,
        },
        0x56 => Obligation::Jump,
        0x57 => Obligation::Jumpi,
        0xf1 | 0xf2 | 0xf4 | 0xfa => call(op, false),
        0x39 => Obligation::CodeCopy,
        0x3f => Obligation::ExtCode { hash: true },
        0x3c => Obligation::ExtCode { hash: false },
        0x5a => match next {
            Some(n) if matches!(n.bytes[0], 0xf1 | 0xf2 | 0xf4 | 0xfa) => call(n.bytes[0], true),
            _ => bail!(
                "GAS at pc {} is supported only directly before a call opcode",
                instruction.pc
            ),
        },
        0x00 => Obligation::Halt {
            op: "Operation.STOP",
            which: "(Or.inl rfl)",
            congruent: "congruent_stop.at",
        },
        0xf3 => Obligation::Halt {
            op: "Operation.RETURN",
            which: "(Or.inr (Or.inl rfl))",
            congruent: "congruent_return.at",
        },
        0xfd => Obligation::Halt {
            op: "Operation.REVERT",
            which: "(Or.inr (Or.inr (Or.inl rfl)))",
            congruent: "congruent_revert.at",
        },
        0xff => Obligation::Halt {
            op: "Operation.SELFDESTRUCT",
            which: "(Or.inr (Or.inr (Or.inr rfl)))",
            congruent: "(selfdestruct_at size_pos.1 size_pos.2)",
        },
        0x0c..=0x0f
        | 0x1e..=0x1f
        | 0x21..=0x2f
        | 0x4b..=0x4f
        | 0xa5..=0xef
        | 0xf6..=0xf9
        | 0xfb..=0xfc
        | 0xfe => Obligation::Invalid,
        // Creation, external code reads and stray GAS stay outside the profile.
        _ => match simple_name(op) {
            Some(name) => simple(name),
            None => bail!(
                "unsupported opcode 0x{op:02x} at pc {} for whole-program certificates",
                instruction.pc
            ),
        },
    })
}

fn simple_name(op: u8) -> Option<&'static str> {
    Some(match op {
        0x01 => "ADD",
        0x02 => "MUL",
        0x03 => "SUB",
        0x04 => "DIV",
        0x05 => "SDIV",
        0x06 => "MOD",
        0x07 => "SMOD",
        0x08 => "ADDMOD",
        0x09 => "MULMOD",
        0x0a => "EXP",
        0x0b => "SIGNEXTEND",
        0x10 => "LT",
        0x11 => "GT",
        0x12 => "SLT",
        0x13 => "SGT",
        0x14 => "EQ",
        0x15 => "ISZERO",
        0x16 => "AND",
        0x17 => "OR",
        0x18 => "XOR",
        0x19 => "NOT",
        0x1a => "BYTE",
        0x1b => "SHL",
        0x1c => "SHR",
        0x1d => "SAR",
        0x30 => "ADDRESS",
        0x32 => "ORIGIN",
        0x33 => "CALLER",
        0x34 => "CALLVALUE",
        0x35 => "CALLDATALOAD",
        0x36 => "CALLDATASIZE",
        0x3a => "GASPRICE",
        0x50 => "POP",
        0x51 => "MLOAD",
        0x52 => "MSTORE",
        0x53 => "MSTORE8",
        0x5b => "JUMPDEST",
        0x58 => "PC",
        0x20 => "KECCAK256",
        0x37 => "CALLDATACOPY",
        0x3d => "RETURNDATASIZE",
        0x41 => "COINBASE",
        0x42 => "TIMESTAMP",
        0x43 => "NUMBER",
        0x45 => "GASLIMIT",
        0x46 => "CHAINID",
        0x54 => "SLOAD",
        0x55 => "SSTORE",
        0x5d => "TSTORE",
        0x5e => "MCOPY",
        0x40 => "BLOCKHASH",
        0x59 => "MSIZE",
        0x5c => "TLOAD",
        0xa0 => "LOG0",
        0xa1 => "LOG1",
        0xa2 => "LOG2",
        0xa3 => "LOG3",
        0xa4 => "LOG4",
        0x31 => "BALANCE",
        0x47 => "SELFBALANCE",
        0x3e => "RETURNDATACOPY",
        0x44 => "PREVRANDAO",
        0x48 => "BASEFEE",
        0x49 => "BLOBHASH",
        0x4a => "BLOBBASEFEE",
        _ => return None,
    })
}

/// Obligations per point module; each module must compile within the
/// per-module proof budget.
const POINTS_PER_MODULE: usize = 48;
/// Point chunks whose fact lists share one table module.
const CHUNKS_PER_TABLE: usize = 8;
const BYTES_PER_CHUNK: usize = 1024;

const HEADER: &str = "set_option Elab.async false\nset_option maxRecDepth 131072\nset_option maxHeartbeats 4000000\nopen EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition GolfWhole\nnamespace GolfWholeCertificate\n\n";

fn nat_list(values: impl Iterator<Item = usize>) -> String {
    let items: Vec<String> = values.map(|v| v.to_string()).collect();
    format!("[{}]", items.join(", "))
}

/// Right-nested concatenation of named lists.
fn nested(names: &[String]) -> String {
    match names {
        [] => "[]".to_owned(),
        [one] => one.clone(),
        [first, rest @ ..] => format!("{first} ++ ({})", nested(rest)),
    }
}

/// Membership of chunk `k` in the right-nested concatenation of `n` chunks.
fn in_chunk_term(k: usize, n: usize) -> String {
    let mut term = if k + 1 == n {
        "h".to_owned()
    } else {
        "List.mem_append.mpr (Or.inl h)".to_owned()
    };
    for _ in 0..k {
        term = format!("List.mem_append.mpr (Or.inr ({term}))");
    }
    term
}

fn render(original: &[u8], candidate: &[u8], plan: &Plan) -> Vec<(String, String)> {
    let mut modules = Vec::new();
    let mut image = format!("import WholeUpsilon\nimport WholeShape\n{HEADER}");
    for (side, code) in [("old", original), ("new", candidate)] {
        let mut names = Vec::new();
        for (i, chunk) in code.chunks(BYTES_PER_CHUNK).enumerate() {
            let name = format!("{side}Chunk{i}");
            writeln!(
                image,
                "def {name} : List Nat := {}",
                nat_list(chunk.iter().map(|b| usize::from(*b)))
            )
            .unwrap();
            names.push(name);
        }
        // Tails let each decode fact drop at most one chunk in the kernel.
        let n = names.len();
        for i in (0..n).rev() {
            let body = if i + 1 == n {
                format!("{side}Chunk{i}")
            } else {
                format!("{side}Chunk{i} ++ {side}Tail{}", i + 1)
            };
            writeln!(image, "def {side}Tail{i} : List Nat := {body}").unwrap();
        }
        writeln!(
            image,
            "def {side}Bytes : List Nat := {side}Tail0\ndef {side}Code : ByteArray := ofBytes {side}Bytes\ntheorem {side}Drop0 : {side}Bytes.drop 0 = {side}Tail0 := rfl"
        )
        .unwrap();
        for i in 1..n {
            writeln!(
                image,
                "theorem {side}Drop{i} : {side}Bytes.drop {} = {side}Tail{i} :=\n  drop_step (k := {}) (n := {BYTES_PER_CHUNK}) {side}Drop{} rfl (by decide +kernel)",
                i * BYTES_PER_CHUNK,
                (i - 1) * BYTES_PER_CHUNK,
                i - 1
            )
            .unwrap();
        }
        let _ = nested;
    }
    writeln!(
        image,
        "def jumpsN : List Nat := {}\ndef jumps : Array UInt256 := (jumpsN.map UInt256.ofNat).toArray\nend GolfWholeCertificate",
        nat_list(plan.jumpdests.iter().copied())
    )
    .unwrap();
    modules.push(("WholeImage".to_owned(), image));
    // One obligation per (pc, facts) entry, in pc order. Fact lists and the
    // entry table are split across modules to stay within the module budget.
    let entries: Vec<(usize, usize)> = plan
        .analysis
        .entries
        .iter()
        .flat_map(|(pc, list)| (0..list.len()).map(move |i| (*pc, i)))
        .collect();
    let chunks: Vec<&[(usize, usize)]> = entries.chunks(POINTS_PER_MODULE).collect();
    let mut place = std::collections::BTreeMap::new();
    for (k, chunk) in chunks.iter().enumerate() {
        for (i, entry) in chunk.iter().enumerate() {
            place.insert(*entry, (k, i));
        }
    }
    let mut point_names = Vec::new();
    let mut table_imports = String::new();
    for (g, group) in chunks.chunks(CHUNKS_PER_TABLE).enumerate() {
        let mut m = format!("import WholeImage\n{HEADER}");
        for (j, chunk) in group.iter().enumerate() {
            let k = g * CHUNKS_PER_TABLE + j;
            for &(pc, i) in *chunk {
                let fs = &plan.analysis.entries[&pc][i];
                writeln!(m, "def F{pc}_{i} : List Abs := {}", facts_term(fs)).unwrap();
            }
            let name = format!("pointsChunk{k}");
            let items: Vec<String> = chunk
                .iter()
                .map(|(pc, i)| format!("({pc}, F{pc}_{i})"))
                .collect();
            writeln!(
                m,
                "def {name} : List (Nat × List Abs) := [{}]",
                items.join(", ")
            )
            .unwrap();
            point_names.push(name);
        }
        m.push_str("end GolfWholeCertificate\n");
        writeln!(table_imports, "import WholeTable{g}").unwrap();
        modules.push((format!("WholeTable{g}"), m));
    }
    let mut index = format!("{table_imports}{HEADER}");
    writeln!(
        index,
        "def table : List (Nat × List Abs) := {}\nabbrev Q : UInt256 → List UInt256 → Prop := Inv table\n/-- Call and external code obligations need the environment assumptions; a runtime without them has none. -/\ndef HC : Prop := {}\n/-- Constant addresses read by EXTCODEHASH or EXTCODECOPY. -/\ndef inspected : List Nat := {}",
        nested(&point_names),
        if plan.assumes() { "True" } else { "False" },
        nat_list(plan.inspected.iter().copied())
    )
    .unwrap();
    for k in 0..chunks.len() {
        writeln!(
            index,
            "theorem in_chunk{k} {{x : Nat × List Abs}} (h : x ∈ pointsChunk{k}) : x ∈ table := {}",
            in_chunk_term(k, chunks.len())
        )
        .unwrap();
    }
    index.push_str("end GolfWholeCertificate\n");
    modules.push(("WholeIndex".to_owned(), index));
    // Per-block scanner states and byte bounds, checked in separate modules.
    let mut block_modules = Vec::new();
    let mut jumps_proof = String::new();
    for (side, code) in [("old", original), ("new", candidate)] {
        let chunks: Vec<&[u8]> = code.chunks(BYTES_PER_CHUNK).collect();
        // Scanner state (pending immediate bytes, pc) and each block's own jumpdests.
        let mut state = (0usize, 0usize);
        let mut states = Vec::new();
        let mut locals: Vec<Vec<usize>> = Vec::new();
        for chunk in &chunks {
            states.push(state);
            let (mut k, mut pc) = state;
            let mut local = Vec::new();
            for &b in *chunk {
                if k == 0 {
                    if b == 0x5b {
                        local.push(pc);
                    }
                    k = push_width(b);
                } else {
                    k -= 1;
                }
                pc += 1;
            }
            locals.push(local);
            state = (k, pc);
        }
        states.push(state);
        let prefix = |i: usize| -> Vec<usize> { locals[..i].concat() };
        for (group, indices) in (0..chunks.len()).collect::<Vec<_>>().chunks(6).enumerate() {
            let name = format!(
                "WholeBlocks{}{group}",
                if side == "old" { "Old" } else { "New" }
            );
            let mut m = format!("import WholeImage\n{HEADER}");
            for &i in indices {
                let (k, pc) = states[i];
                let (k2, pc2) = states[i + 1];
                writeln!(
                    m,
                    "theorem {side}Scan{i} : scanS {side}Chunk{i} {k} {pc} #[] = ({k2}, {pc2}, {}) := by decide +kernel\ntheorem {side}Bound{i} : ∀ x ∈ {side}Chunk{i}, x < 256 := by decide +kernel\ntheorem {side}Len{i} : {side}Chunk{i}.length = {} := by decide +kernel",
                    word_array(&locals[i]),
                    chunks[i].len()
                )
                .unwrap();
            }
            m.push_str("end GolfWholeCertificate\n");
            block_modules.push(name.clone());
            modules.push((name, m));
        }
        let n = chunks.len();
        let last = n - 1;
        let (k, pc) = states[last];
        writeln!(
            jumps_proof,
            "theorem {side}ScanT{last} : scanL {side}Tail{last} {k} {pc} {} = jumps := scan_last' {side}Scan{last} (by decide +kernel)\ntheorem {side}BoundT{last} : ∀ x ∈ {side}Tail{last}, x < 256 := {side}Bound{last}\ntheorem {side}LenT{last} : {side}Tail{last}.length = {} := {side}Len{last}",
            word_array(&prefix(last)),
            chunks[last].len()
        )
        .unwrap();
        for i in (0..last).rev() {
            let (k, pc) = states[i];
            writeln!(
                jumps_proof,
                "theorem {side}ScanT{i} : scanL {side}Tail{i} {k} {pc} {} = jumps := scan_block' {side}Scan{i} (by decide +kernel) {side}ScanT{}\ntheorem {side}BoundT{i} : ∀ x ∈ {side}Tail{i}, x < 256 := bound_append {side}Bound{i} {side}BoundT{}\ntheorem {side}LenT{i} : {side}Tail{i}.length = {} := length_block {side}Len{i} {side}LenT{}",
                word_array(&prefix(i)),
                i + 1,
                i + 1,
                code.len() - i * BYTES_PER_CHUNK,
                i + 1
            )
            .unwrap();
        }
        writeln!(
            jumps_proof,
            "theorem {side}_jumps : D_J {side}Code (UInt256.ofNat 0) = jumps := by\n  rw [show {side}Code = ofBytes {side}Bytes from rfl, dj_scan {side}Bytes {side}BoundT0 (by rw [show {side}Bytes = {side}Tail0 from rfl, {side}LenT0]; decide)]\n  exact {side}ScanT0"
        )
        .unwrap();
    }
    let block_imports: String = block_modules
        .iter()
        .map(|m| format!("import {m}\n"))
        .chain(std::iter::once("import WholeIndex\n".to_owned()))
        .collect();
    // Jumps whose destination is unknown may reach every JUMPDEST, which then
    // has an entry without facts.
    let any_targets = if plan.analysis.any {
        "theorem anyTargets : ∀ x, jumps.contains x = true → ∀ st, Q x st :=\n  top_targets table jumpsN (by decide +kernel)\n"
    } else {
        ""
    };
    modules.push((
        "WholeJumps".to_owned(),
        format!(
            "{block_imports}{HEADER}{jumps_proof}\n{any_targets}theorem len_eq : oldBytes.length = newBytes.length := by\n  rw [show oldBytes = oldTail0 from rfl, show newBytes = newTail0 from rfl, oldLenT0, newLenT0]\ntheorem size_pos : 0 < oldCode.size ∧ 0 < newCode.size := by\n  show 0 < (ofBytes oldBytes).size ∧ 0 < (ofBytes newBytes).size\n  simp only [ofBytes, ByteArray.size, List.size_toArray, List.length_map]\n  rw [show oldBytes = oldTail0 from rfl, show newBytes = newTail0 from rfl, oldLenT0, newLenT0]\n  decide\ntheorem size_eq : oldCode.size = newCode.size := by\n  show (ofBytes oldBytes).size = (ofBytes newBytes).size\n  simp only [ofBytes, ByteArray.size, List.size_toArray, List.length_map]\n  exact len_eq\nend GolfWholeCertificate\n"
        ),
    ));
    let mem = |pc: usize, fs: &[facts::Abs]| -> String {
        let (i, _) = plan
            .analysis
            .target(pc, fs)
            .expect("every successor has an entry");
        let (k, at) = place[&(pc, i)];
        format!("(in_chunk{k} (mem_at (l := pointsChunk{k}) {at} (x := ({pc}, F{pc}_{i})) rfl))")
    };
    for (k, chunk) in chunks.iter().enumerate() {
        let mut s = format!("import WholeJumps\n{HEADER}");
        for &(pc, i) in *chunk {
            let obligation = &plan.analysis.obligations[&pc];
            let fs = &plan.analysis.entries[&pc][i];
            writeln!(
                s,
                "theorem point_{pc}_{i} : Point HC inspected oldCode newCode jumps Q (Holds F{pc}_{i}) (UInt256.ofNat {pc}) :=\n  {}",
                obligation_term(pc, obligation, fs, original, &plan.jumpdests, &mem)
            )
            .unwrap();
        }
        writeln!(
            s,
            "\ntheorem cover{k} : ∀ p ∈ pointsChunk{k}, Point HC inspected oldCode newCode jumps Q (Holds p.2) (UInt256.ofNat p.1) :="
        )
        .unwrap();
        for (pc, i) in *chunk {
            writeln!(s, "  entries_cons point_{pc}_{i} <|").unwrap();
        }
        s.push_str("  entries_nil\nend GolfWholeCertificate\n");
        modules.push((format!("WholePoints{k}"), s));
    }
    let imports: String = (0..chunks.len())
        .map(|i| format!("import WholePoints{i}\n"))
        .collect();
    let covers: Vec<String> = (0..chunks.len()).map(|k| format!("cover{k}")).collect();
    let mut cover = covers.last().expect("at least one point").clone();
    for name in covers.iter().rev().skip(1) {
        cover = format!("entries_app {name} ({cover})");
    }
    let mut s = format!("{imports}{HEADER}");
    writeln!(
        s,
        "theorem cover : ∀ p ∈ table, Point HC inspected oldCode newCode jumps Q (Holds p.2) (UInt256.ofNat p.1) :=\n  {cover}"
    )
    .unwrap();
    // With calls or external code reads, the final theorems take the environment assumptions.
    let (hyps, pass, env) = if plan.assumes() {
        (
            "\n    (callees : CalleeSummary owner oldCode newCode) (reentry : Reentry owner oldCode)\n    (notPrecompile : owner ∉ π)\n    (notInspected : ∀ a ∈ inspected, AccountAddress.ofUInt256 (UInt256.ofNat a) ≠ owner)",
            " callees reentry notPrecompile notInspected",
            "(fun _ => callees) (fun _ => reentry) (fun _ => notPrecompile) (fun _ => notInspected)",
        )
    } else {
        ("", "", "False.elim False.elim False.elim False.elim")
    };
    writeln!(
        s,
        "
/-- From any pair of states at pc 0 that differ only in deployed code, execution
count and extra candidate gas, every successful or reverting original run of `X`
is matched by a candidate run with the same fuel or more, with equal output and
related final state. -/
theorem whole_certificate (owner : AccountAddress){hyps} (fuel surplus skipped : ℕ) (s t : State)
    (r : ExecutionResult State)
    (rel : DeployedOffset owner oldCode newCode surplus skipped s t)
    (start : s.pc = UInt256.ofNat 0)
    (ok : X fuel (D_J oldCode (UInt256.ofNat 0)) s = .ok r) :
    ∀ fuel', fuel ≤ fuel' → ∃ r', X fuel' (D_J newCode (UInt256.ofNat 0)) t = .ok r' ∧
      OutcomeRelated owner oldCode newCode t.gasAvailable.toNat r r' := by
  rw [old_jumps] at ok
  rw [new_jumps]
  exact whole_refines owner oldCode newCode jumps jumps Q HC inspected (cover_of cover) (fun _ h => h)
    old_jumps.symm new_jumps.symm ⟨(0, F0_0), {start}, rfl, trivial⟩ {env}
    fuel s t surplus skipped r rel (by rw [start]; exact ⟨(0, F0_0), {start}, rfl, trivial⟩) ok

theorem cert (owner : AccountAddress){hyps} (N : ℕ) : Cert owner oldCode newCode N :=
  fun fuel _ s t surplus skipped r rel start _ ok =>
    whole_certificate owner{pass} fuel surplus skipped s t r rel start ok

/-- The same claim for the code-execution function Ξ, from a fresh call frame
whose account maps differ only in the owner's deployed code. -/
theorem xi_certificate (owner : AccountAddress){hyps} (fuel : ℕ)
    (created : Batteries.RBSet AccountAddress compare) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (σ σ₀ τ τ₀ : AccountMap .EVM) (g : UInt256)
    (A : Substate) (I : ExecutionEnv .EVM)
    (current : MapsRelated owner oldCode newCode σ τ)
    (original : MapsRelated owner oldCode newCode σ₀ τ₀)
    (oldCurrent : ∃ a, σ.find? owner = some a ∧ a.code = oldCode)
    (oldOriginal : ∃ a, σ₀.find? owner = some a ∧ a.code = oldCode)
    (newCurrent : ∃ a, τ.find? owner = some a ∧ a.code = newCode)
    (newOriginal : ∃ a, τ₀.find? owner = some a ∧ a.code = newCode)
    (R : ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate))
    (run : Ξ fuel created genesis blocks σ σ₀ g A {{I with codeOwner := owner, code := oldCode}} = .ok R) :
    ∀ fuel', fuel ≤ fuel' →
      ∃ R', Ξ fuel' created genesis blocks τ τ₀ g A {{I with codeOwner := owner, code := newCode}} = .ok R' ∧
        XiRelated owner oldCode newCode g R R' :=
  xi_refines owner oldCode newCode fuel (cert owner{pass} fuel) fuel (le_refl _) created genesis blocks
    σ σ₀ τ τ₀ g g 0 rfl A I current original oldCurrent oldOriginal newCurrent newOriginal R run

/-- The same claim for the message-call function Θ on a call to the owner, when the
original's inner Ξ returns success or revert. -/
theorem theta_certificate (owner : AccountAddress){hyps} (fuel : ℕ) (bvh : List ByteArray)
    (created : Batteries.RBSet AccountAddress compare) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (σ σ₀ τ τ₀ : AccountMap .EVM) (A : Substate)
    (s o : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader) (w : Bool)
    (current : MapsRelated owner oldCode newCode σ τ)
    (original : MapsRelated owner oldCode newCode σ₀ τ₀)
    (oldCurrent : ∃ a, σ.find? owner = some a ∧ a.code = oldCode)
    (oldOriginal : ∃ a, σ₀.find? owner = some a ∧ a.code = oldCode)
    (newCurrent : ∃ a, τ.find? owner = some a ∧ a.code = newCode)
    (newOriginal : ∃ a, τ₀.find? owner = some a ∧ a.code = newCode)
    (R : ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate))
    (inner : Ξ fuel created genesis blocks (transfer σ s owner v) σ₀ g A
      (thetaEnv bvh s o owner oldCode p v' d e H w) = .ok R) :
    ∃ Q, Θ (fuel + 1) bvh created genesis blocks σ σ₀ A s o owner (.Code oldCode) g p v v' d e H w = .ok Q ∧
      ∀ fuel', fuel ≤ fuel' →
        ∃ Q', Θ (fuel' + 1) bvh created genesis blocks τ τ₀ A s o owner (.Code newCode) g p v v' d e H w = .ok Q' ∧
          ThetaRelated owner oldCode newCode g Q Q' :=
  theta_refines owner oldCode newCode fuel (cert owner{pass} fuel) fuel (le_refl _) bvh created genesis
    blocks σ σ₀ τ τ₀ A s o g g 0 rfl p v v' d e H w current original oldCurrent oldOriginal newCurrent
    newOriginal R inner

/-- The same claim for the transaction function Υ on a message call to the owner:
both runs finalize related provisional states with the same substate and status, and
the candidate has at least as much remaining gas (so, by `charged_mono`, is charged
no more gas when its remaining gas is within the limit). -/
theorem upsilon_certificate (owner : AccountAddress){hyps} (fuel : ℕ) (σ τ : AccountMap .EVM) (H_f : ℕ)
    (H genesis : BlockHeader) (blocks : ProcessedBlocks) (T : Transaction) (S_T : AccountAddress)
    (rel : MapsRelated owner oldCode newCode σ τ)
    (oldσ : ∃ a, σ.find? owner = some a ∧ a.code = oldCode)
    (newτ : ∃ a, τ.find? owner = some a ∧ a.code = newCode)
    (hr : T.base.recipient = some owner) (notPre : owner ∉ π)
    (R : ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate))
    (inner : Ξ fuel .empty genesis blocks
      (transfer (txCheckpoint σ H_f H T S_T) S_T owner T.base.value) (txCheckpoint σ H_f H T S_T)
      (txGas T) (txSubstate H T S_T owner)
      (thetaEnv T.blobVersionedHashes S_T S_T owner oldCode (txPrice H_f T) T.base.value T.base.data 0 H true) =
        .ok R) :
    ∃ σP g A z, Υ (fuel + 1) σ H_f H genesis blocks T S_T =
        .ok ((finalize σP g A H_f H T S_T).1, A, z, (finalize σP g A H_f H T S_T).2) ∧
      ∀ fuel', fuel ≤ fuel' → ∃ σP' g', MapsRelated owner oldCode newCode σP σP' ∧ g.toNat ≤ g'.toNat ∧
        Υ (fuel' + 1) τ H_f H genesis blocks T S_T =
          .ok ((finalize σP' g' A H_f H T S_T).1, A, z, (finalize σP' g' A H_f H T S_T).2) :=
  upsilon_refines owner oldCode newCode fuel (cert owner{pass} fuel) fuel (le_refl _) σ τ H_f H genesis
    blocks T S_T rel oldσ newτ hr notPre R inner

#print axioms whole_certificate
#print axioms xi_certificate
#print axioms theta_certificate
#print axioms upsilon_certificate
end GolfWholeCertificate",
        start = mem(0, &[])
    )
    .unwrap();
    modules.push(("WholeCertificate".to_owned(), s));
    modules
}

fn wop(bytes: &[u8]) -> String {
    match bytes[0] {
        0x5f => "WOp.push0".to_owned(),
        op @ 0x60..=0x7f => {
            let width = usize::from(op - 0x5f);
            format!(
                "WOp.push .PUSH{width} (UInt256.ofNat {}) {width}",
                U256::from_be_slice(&bytes[1..])
            )
        }
        op @ 0x80..=0x8f => format!("WOp.dup {}", op - 0x7f),
        op @ 0x90..=0x9f => format!("WOp.swap {}", op - 0x8f),
        0x50 => "WOp.pop".to_owned(),
        0x15 => "WOp.un .iszero".to_owned(),
        0x19 => "WOp.un .not".to_owned(),
        op => {
            const NAMES: [&str; 20] = [
                "add",
                "mul",
                "sub",
                "div",
                "sdiv",
                "mod",
                "smod",
                "signextend",
                "lt",
                "gt",
                "slt",
                "sgt",
                "eq",
                "and",
                "or",
                "xor",
                "byte",
                "shl",
                "shr",
                "sar",
            ];
            format!("WOp.bin .{}", NAMES[index(&BINARY, op)])
        }
    }
}

fn word_array(values: &[usize]) -> String {
    let words: Vec<String> = values
        .iter()
        .map(|v| format!("UInt256.ofNat {v}"))
        .collect();
    format!("#[{}]", words.join(", "))
}

fn tail2(side: &str, at: usize) -> String {
    let i = at / BYTES_PER_CHUNK;
    format!(
        "{side}Bytes {side}Tail{i} {} {at} (by decide +kernel) {side}Drop{i} (by decide)",
        i * BYTES_PER_CHUNK
    )
}

/// Lean literal for a fact list.
fn facts_term(fs: &[facts::Abs]) -> String {
    let items: Vec<String> = fs
        .iter()
        .map(|a| match &a.set {
            None => format!("⟨{}, none⟩", a.bits),
            Some(set) => {
                let values: Vec<String> = set.iter().map(U256::to_string).collect();
                format!("⟨{}, some [{}]⟩", a.bits, values.join(", "))
            }
        })
        .collect();
    format!("[{}]", items.join(", "))
}

fn obligation_term(
    pc: usize,
    obligation: &Obligation,
    fs: &[facts::Abs],
    code: &[u8],
    jumpdests: &[usize],
    mem: &dyn Fn(usize, &[facts::Abs]) -> String,
) -> String {
    const K: &str = "(by decide +kernel)";
    let tail = |side: &str, at: usize| {
        let i = at / BYTES_PER_CHUNK;
        format!(
            "{side}Bytes {side}Tail{i} {} {at} {side}Drop{i} (by decide)",
            i * BYTES_PER_CHUNK
        )
    };
    let fact = |side: &str, at: usize| format!("(decode_tail {} (by decide) {K})", tail(side, at));
    let fact2 =
        |side: &str, at: usize| format!("(decode_tail' {} (by decide) {K})", tail2(side, at));
    let get =
        |side: &str, at: usize| format!("(decode_tail_getD {} (by decide) {K})", tail(side, at));
    let old = |at: usize| fact("old", at);
    let new = |at: usize| fact("new", at);
    let dests: BTreeSet<usize> = jumpdests.iter().copied().collect();
    // Destinations of a jump: each listed value is covered or not a JUMPDEST.
    let targets = |set: &[U256], tail: &[facts::Abs]| {
        let mut term = "targets_nil".to_owned();
        for c in set.iter().rev() {
            term = match facts::dest(&dests, *c) {
                Some(c) => format!("(targets_mem {} {K} {term})", mem(c, tail)),
                None => format!("(targets_bad {K} {term})"),
            };
        }
        term
    };
    let jump = |kind: &str, tail: &[facts::Abs]| match fs.first().and_then(|a| a.set.as_ref()) {
        Some(set) => format!("({kind}_set (by rfl) {})", targets(set, tail)),
        None => format!("({kind}_any anyTargets)"),
    };
    match obligation {
        Obligation::Same { op, arg, same, len } => {
            let bytes = &code[pc..pc + len];
            let (eff, xf) = if window_op(bytes) {
                (
                    format!("(eff_wop ({}) (by decide))", wop(bytes)),
                    format!("(xf_wop (by decide) {K})"),
                )
            } else {
                let (_, _, name) = facts::shape(bytes[0]).expect("every opcode has a stack shape");
                (format!("({name} _)"), format!("(xf_shape {K})"))
            };
            format!(
                ".same _ {op} {arg} {} {same}.2.1 {same}.2.2 {} {} (same_next {eff} {xf} {K} {})",
                // Size-dependent facts are already specialized to the two images.
                if same.contains("size_eq") {
                    format!("{same}.1")
                } else {
                    format!("{same}.1.at")
                },
                old(pc),
                new(pc),
                mem(pc + len, &facts::xfer_same(bytes, fs))
            )
        }
        Obligation::Jump => format!(
            ".jump _ {} {} {}",
            old(pc),
            new(pc),
            jump("jump", &facts::drop(fs, 1))
        ),
        Obligation::Jumpi => format!(
            ".jumpi _ {} {} (jumpi_next {K} {} {K}) {}",
            old(pc),
            new(pc),
            mem(pc + 1, &facts::drop(fs, 2)),
            jump("jumpi", &facts::drop(fs, 2))
        ),
        Obligation::Halt {
            op,
            which,
            congruent,
        } => format!(
            ".halt _ {op} none {congruent} {which} {} {}",
            get("old", pc),
            get("new", pc)
        ),
        Obligation::FallOff => format!(
            ".halt _ Operation.STOP none congruent_stop.at (Or.inl rfl) {} {}",
            get("old", pc),
            get("new", pc)
        ),
        Obligation::Invalid => format!(".invalid _ {}", old(pc)),
        Obligation::Thread(site) => {
            let jumpi = site.pc + site.width + 1;
            let push2 = site.from + 1;
            let jump = push2 + site.to_width + 1;
            let rest = facts::drop(fs, 1);
            format!(
                ".segment _ (fun owner nj hj => thread_segment owner oldCode newCode jumps nj _ _ (UInt256.ofNat {pc}) .PUSH{w} .PUSH{m} {w} {m} (UInt256.ofNat {from}) (UInt256.ofNat {to}) (by decide) (by decide) {} {} {} {} {} {} {} (thread_fall {K} {} {K}) (thread_target {K} {} {K}) hj)",
                old(pc),
                new(pc),
                fact2("old", jumpi),
                fact2("new", jumpi),
                old(site.from),
                fact2("old", push2),
                fact2("old", jump),
                mem(jumpi + 1, &rest),
                mem(site.to, &rest),
                w = site.width,
                m = site.to_width,
                from = site.from,
                to = site.to,
            )
        }
        Obligation::Window(site) => {
            let ops = |instrs: &[(usize, Vec<u8>)]| {
                let items: Vec<String> = instrs.iter().map(|(_, b)| wop(b)).collect();
                format!("[{}]", items.join(", "))
            };
            let wcode = |side: &str, instrs: &[(usize, Vec<u8>)]| {
                let mut term = format!("(WCode.nil (UInt256.ofNat {}))", site.end);
                for (i, (at, bytes)) in instrs.iter().enumerate().rev() {
                    let after = at + bytes.len();
                    term = format!(
                        "(WCode.cons (UInt256.ofNat {at}) (UInt256.ofNat {after}) (UInt256.ofNat {}) ({}) {} (by decide) {} {K} {term})",
                        site.end,
                        wop(bytes),
                        ops(&instrs[i + 1..]),
                        fact(side, *at),
                    );
                }
                term
            };
            format!(
                ".segment _ (fun owner nj _ => window_segment owner oldCode newCode jumps nj _ _ (UInt256.ofNat {pc}) (UInt256.ofNat {}) {} {} _ {} {} {K} window_fits (window_next {} {K} {} {K}))",
                site.end,
                ops(&site.old),
                ops(&site.new),
                wcode("old", &site.old),
                wcode("new", &site.new),
                ops(&site.old),
                mem(site.end, &facts::xfer_window(&site.old, fs)),
            )
        }
        Obligation::Call(site) => {
            let (op, hop) = site.lean();
            let mut next = vec![facts::top()];
            next.extend(facts::drop(fs, site.pop()));
            let target = mem(pc + site.len(), &next);
            if site.gas_first {
                format!(
                    ".gascall _ {op} {} trivial {hop} {} {} {} {} (call_next {K} {target} {K})",
                    site.inputs,
                    old(pc),
                    new(pc),
                    old(pc + 1),
                    new(pc + 1)
                )
            } else {
                format!(
                    ".call _ {op} {} trivial {hop} {} {} (call_next {K} {target} {K})",
                    site.inputs,
                    old(pc),
                    new(pc)
                )
            }
        }
        Obligation::ExtCode { hash } => {
            let addr = constant(fs, 0).expect("checked by the plan");
            if *hash {
                let mut next = vec![facts::top()];
                next.extend(facts::drop(fs, 1));
                format!(
                    ".extcodehash _ {addr} (by decide) trivial (by decide) {} {} (addr_args rfl) (extcodehash_next {K} {} {K})",
                    old(pc),
                    new(pc),
                    mem(pc + 1, &next)
                )
            } else {
                format!(
                    ".extcodecopy _ {addr} (by decide) trivial (by decide) {} {} (addr_args rfl) (extcodecopy_next {K} {} {K})",
                    old(pc),
                    new(pc),
                    mem(pc + 1, &facts::drop(fs, 4))
                )
            }
        }
        Obligation::CodeCopy => {
            let (off, len) = codecopy_range(fs).expect("checked by the plan");
            format!(
                ".codecopy _ {off} {len} (by decide) (by decide) {} {} (write_congr oldBytes newBytes {off} {len} len_eq {K}) (codecopy_args rfl rfl) (codecopy_next {K} {} {K})",
                old(pc),
                new(pc),
                mem(pc + 1, &facts::drop(fs, 3))
            )
        }
        Obligation::Power(site) => {
            let mul = site.pc + site.width + 1;
            let mut next = vec![facts::top()];
            next.extend(facts::drop(fs, 1));
            format!(
                ".power _ .PUSH{w} {w} {k} (by decide) (by decide) ⟨{}, {}⟩ ⟨{}, {}⟩ (power_next {K} {} {K})",
                old(pc),
                fact2("old", mul),
                new(pc),
                fact2("new", mul),
                mem(mul + 1, &next),
                w = site.width,
                k = site.exponent
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plans_power_site_and_rejects_other_differences() {
        let original = hex::decode("34600a576007600402005b600080fd").unwrap();
        let candidate = hex::decode("34600a57600760021b005b600080fd").unwrap();
        let planned = plan(&original, &candidate).unwrap();
        assert_eq!(planned.jumpdests, vec![10]);
        let pcs: Vec<usize> = planned.points().map(|(pc, _)| *pc).collect();
        assert_eq!(pcs, vec![0, 1, 3, 4, 6, 9, 10, 11, 13, 14]);
        // Unreachable trailing bytes need no obligation.
        let tail = hex::decode("34600a576007600402005b600080fdf1").unwrap();
        assert_eq!(plan(&tail, &tail).unwrap().points().count(), 11);
        assert!(matches!(first(&planned, 6), Obligation::Power(_)));
        let wrong = hex::decode("34600a57600760031b005b600080fd").unwrap();
        assert!(plan_err(&original, &wrong).contains("unsupported difference"));
        let create = hex::decode("f000").unwrap();
        assert!(plan_err(&create, &create).contains("unsupported opcode 0xf0"));
    }

    #[test]
    fn plans_calls_with_their_gas() {
        // PUSH0 x6; GAS; STATICCALL; POP; PUSH0 x7; CALL; POP; PUSH0 x6; GAS; DELEGATECALL;
        // CALLCODE; STOP.
        let code = hex::decode("5f5f5f5f5f5f5afa505f5f5f5f5f5f5ff1505f5f5f5f5f5f5af4f200").unwrap();
        let planned = plan(&code, &code).unwrap();
        assert!(planned.calls());
        assert!(matches!(
            first(&planned, 24),
            Obligation::Call(CallSite {
                op: 0xf4,
                inputs: 6,
                gas_first: true
            })
        ));
        assert!(matches!(
            first(&planned, 26),
            Obligation::Call(CallSite {
                op: 0xf2,
                inputs: 7,
                gas_first: false
            })
        ));
        assert!(matches!(
            first(&planned, 6),
            Obligation::Call(CallSite {
                gas_first: true,
                ..
            })
        ));
        assert!(matches!(
            first(&planned, 16),
            Obligation::Call(CallSite {
                gas_first: false,
                ..
            })
        ));
        // SELFDESTRUCT halts: nothing after it is reached.
        let destruct = hex::decode("5fff00").unwrap();
        let halting = plan(&destruct, &destruct).unwrap();
        assert!(matches!(first(&halting, 1), Obligation::Halt { .. }));
        assert!(!halting.analysis.obligations.contains_key(&2));
        // The call opcode after GAS is covered by the GAS point.
        assert!(!planned.analysis.obligations.contains_key(&7));
        let pcs: Vec<usize> = planned.points().map(|(pc, _)| *pc).collect();
        assert_eq!(
            pcs,
            vec![
                0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                24, 26, 27
            ]
        );
        // GAS anywhere else is not supported.
        let gas = hex::decode("5a00").unwrap();
        assert!(plan_err(&gas, &gas).contains("GAS at pc 0"));
        let plain = hex::decode("34600a576007600402005b600080fd").unwrap();
        assert!(!plan(&plain, &plain).unwrap().calls());
    }

    #[test]
    fn plans_constant_code_copies() {
        // PUSH1 4 PUSH1 2 MUL POP; PUSH1 2 PUSH1 15 PUSH0 CODECOPY; PC POP; STOP; two data bytes.
        let original = hex::decode("6004600202506002600f5f39585000aabb").unwrap();
        let candidate = hex::decode("600460011b506002600f5f39585000aabb").unwrap();
        let planned = plan(&original, &candidate).unwrap();
        assert!(matches!(first(&planned, 11), Obligation::CodeCopy));
        assert!(planned.precise);
        assert_eq!(
            codecopy_range(&planned.analysis.entries[&11][0]),
            Some((15, 2))
        );
        // A copy that reads the rewritten bytes is rejected before Lean.
        let reads = hex::decode("600460020250600260025f39585000aabb").unwrap();
        let reads_new = hex::decode("600460011b50600260025f39585000aabb").unwrap();
        assert!(plan_err(&reads, &reads_new).contains("a rewrite changes"));
        // A copy with a calldata offset has no constant range.
        let dynamic = hex::decode("60025f355f3900").unwrap();
        assert!(plan_err(&dynamic, &dynamic).contains("constant offset"));
        // Code reads of constant addresses are collected; a CALLER address is rejected.
        let reads = hex::decode("60013f505f5f5f60023c00").unwrap();
        let planned = plan(&reads, &reads).unwrap();
        assert_eq!(planned.inspected, vec![1, 2]);
        assert!(planned.assumes());
        let caller = hex::decode("333f5000").unwrap();
        assert!(plan_err(&caller, &caller).contains("constant address"));
    }

    #[test]
    fn plans_threading_site_and_its_destination() {
        let original = hex::decode("346007570000005b600b565b600080fd").unwrap();
        let candidate = hex::decode("34600b570000005b600b565b600080fd").unwrap();
        let planned = plan(&original, &candidate).unwrap();
        assert!(matches!(first(&planned, 1), Obligation::Thread(_)));
        let pcs: Vec<usize> = planned.points().map(|(pc, _)| *pc).collect();
        // The trampoline at 7 is no longer reached.
        assert_eq!(pcs, vec![0, 1, 4, 11, 12, 14, 15]);
        // A destination without the matching trampoline is rejected.
        let wrong = hex::decode("34600c570000005b600b565b600080fd").unwrap();
        assert!(plan_err(&original, &wrong).contains("unsupported difference"));
    }

    #[test]
    fn plans_stack_windows() {
        // PUSH1 0x20 DUP2 SWAP1 -> DUP1 PUSH2 0x0020, followed by STOP.
        let original = hex::decode("6020819000").unwrap();
        let candidate = hex::decode("806100200000").unwrap()[..5].to_vec();
        let planned = plan(&original, &candidate).unwrap();
        assert!(matches!(first(&planned, 0), Obligation::Window(_)));
        // An idempotent mask: x AND m AND m -> x AND m.
        let mask = hex::decode("60ff1660ff1600").unwrap();
        let fewer = hex::decode("60ff1660ff5000").unwrap();
        assert!(has_window(&plan(&mask, &fewer).unwrap()));
        // Operands of commutative operators may be reordered.
        let mask = hex::decode("8060ff1600").unwrap();
        let swapped = hex::decode("60ff811600").unwrap();
        assert!(has_window(&plan(&mask, &swapped).unwrap()));
        // A window that changes the result is rejected before Lean.
        let bad = hex::decode("8061002100").unwrap();
        assert!(plan_err(&original, &bad).contains("unsupported difference"));
    }

    #[test]
    fn normalizes_modulo_algebraic_laws() {
        let x = || Sym::Input(0);
        let y = || Sym::Input(1);
        let lit = |v: U256| Sym::Lit(v);
        let bin = |op: u8, a: Sym, b: Sym| Sym::Bin(op, Box::new(a), Box::new(b));
        let same = |a: Sym, b: Sym| norm(&a, &[]) == norm(&b, &[]);
        assert!(same(bin(0x11, x(), y()), bin(LT, y(), x())));
        assert!(same(
            bin(SUB, x(), lit(U256::from(3))),
            bin(ADD, lit(U256::ZERO.wrapping_sub(U256::from(3))), x())
        ));
        assert!(same(
            bin(0x1c, lit(U256::from(224)), x()),
            bin(DIV, x(), lit(U256::from(1) << 224))
        ));
        assert!(same(
            bin(0x1b, lit(U256::from(5)), x()),
            bin(MUL, lit(U256::from(32)), x())
        ));
        let m = || lit(U256::from(0xff));
        assert!(same(
            bin(AND, x(), bin(AND, m(), y())),
            bin(AND, bin(AND, y(), x()), bin(AND, m(), x()))
        ));
        assert!(same(
            bin(EQ, x(), lit(U256::ZERO)),
            Sym::Un(ISZERO, Box::new(x()))
        ));
        assert!(same(
            bin(ADD, bin(ADD, x(), lit(U256::from(3))), lit(U256::from(4))),
            bin(ADD, lit(U256::from(7)), x())
        ));
        assert!(!same(bin(SUB, x(), y()), bin(SUB, y(), x())));
        // Range facts: a comparison already fits in one bit, a byte in eight.
        let one = || lit(U256::from(1));
        assert!(same(bin(AND, bin(LT, x(), y()), one()), bin(LT, x(), y())));
        let iszero = |a: Sym| Sym::Un(ISZERO, Box::new(a));
        assert!(same(iszero(iszero(bin(EQ, x(), y()))), bin(EQ, x(), y())));
        assert!(same(
            bin(AND, bin(AND, x(), m()), lit(U256::from(0xffff))),
            bin(AND, x(), m())
        ));
        assert!(!same(bin(AND, x(), one()), x()));
        assert!(!same(bin(0x12, x(), y()), bin(0x12, y(), x())));
    }

    #[test]
    fn carries_facts_across_jumps() {
        // CALLER; PUSH1 5; JUMP; STOP; JUMPDEST; PUSH20 2^160-1; AND; ... RETURN.
        // The mask is a no-op because CALLER is below 2^160 on every path.
        let mask = format!("33600556005b73{}165f5260205ff3", "ff".repeat(20));
        let dropped = format!("33600556005b73{}505f5260205ff3", "00".repeat(20));
        let original = hex::decode(&mask).unwrap();
        let planned = plan(&original, &hex::decode(&dropped).unwrap()).unwrap();
        assert!(matches!(first(&planned, 6), Obligation::Window(_)));
        assert!(planned.precise);
        // The dead STOP after the JUMP needs no obligation.
        assert!(!planned.analysis.obligations.contains_key(&4));
        let at = &planned.analysis.entries[&5];
        assert_eq!(at.len(), 1);
        assert_eq!(
            at[0],
            vec![facts::Abs {
                bits: 160,
                set: None
            }]
        );
        // With a destination read from calldata the JUMPDEST knows nothing.
        let unknown = mask.replacen("6005", "5f35", 1);
        let candidate = dropped.replacen("6005", "5f35", 1);
        assert!(
            plan_err(
                &hex::decode(unknown).unwrap(),
                &hex::decode(candidate).unwrap()
            )
            .contains("unsupported difference")
        );
    }

    fn has_window(plan: &Plan) -> bool {
        plan.points()
            .any(|(_, o)| matches!(o, Obligation::Window(_)))
    }

    fn first(plan: &Plan, pc: usize) -> &Obligation {
        &plan.analysis.obligations[&pc]
    }

    fn plan_err(a: &[u8], b: &[u8]) -> String {
        match plan(a, b) {
            Ok(_) => String::new(),
            Err(error) => error.to_string(),
        }
    }
}
