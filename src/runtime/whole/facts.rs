//! Per-point stack facts for whole-program certificates.
//!
//! The analysis is untrusted: Lean checks every transfer again. Facts describe
//! the original stack only (top first). A pc may carry several fact lists, one
//! per calling context: lists that agree on every slot holding possible jump
//! destinations (return addresses) are joined, others stay apart up to
//! `MAX_CONTEXTS`; beyond that all are joined.

use anyhow::Result;
use revm::primitives::U256;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

use super::{Obligation, Sym, bits, sym_run, window_op};

/// Distinct calling contexts kept per pc before they are all joined.
const MAX_CONTEXTS: usize = 256;
/// Largest value set kept for one slot.
const MAX_SET: usize = 32;

/// Mirror of the Lean `Abs`: the value is below `2^bits` and, if `set` is
/// given, one of its (sorted) elements.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct Abs {
    pub bits: usize,
    pub set: Option<Vec<U256>>,
}

pub(super) type Facts = Vec<Abs>;

pub(super) fn top() -> Abs {
    Abs {
        bits: 256,
        set: None,
    }
}

fn is_top(a: &Abs) -> bool {
    a.bits >= 256 && a.set.is_none()
}

fn lit_bits(v: U256) -> usize {
    256 - v.leading_zeros()
}

/// Mirror of the Lean `litAbs`.
fn lit_abs(v: U256) -> Abs {
    Abs {
        bits: lit_bits(v),
        set: Some(vec![v]),
    }
}

/// Mirror of the Lean `absOf`.
fn abs_of(fs: &[Abs], s: &Sym) -> Abs {
    match s {
        Sym::Input(i) => fs.get(*i).cloned().unwrap_or_else(top),
        Sym::Lit(v) => lit_abs(*v),
        s => Abs {
            bits: bits(s, &env(fs)),
            set: None,
        },
    }
}

/// Bit bounds of the slots, the window normalizer's environment.
pub(super) fn env(fs: &[Abs]) -> Vec<usize> {
    fs.iter().map(|a| a.bits).collect()
}

/// Mirror of the Lean `xferS`: replace the top `m` slots by the terms `a`.
fn xfer_syms(a: &[Sym], m: usize, fs: &[Abs]) -> Facts {
    let mut out: Facts = a.iter().map(|s| abs_of(fs, s)).collect();
    out.extend(fs.iter().skip(m).cloned());
    out
}

/// Mirror of the Lean `Abs.le`.
fn le(a: &Abs, b: &Abs) -> bool {
    let below = |x: &U256| b.bits >= 256 || *x < (U256::from(1) << b.bits);
    let bounded = a.bits <= b.bits || a.set.as_ref().is_some_and(|l| l.iter().all(below));
    let member = match (&b.set, &a.set) {
        (None, _) => true,
        (Some(lb), Some(la)) => la.iter().all(|x| lb.contains(x)),
        (Some(_), None) => false,
    };
    bounded && member
}

/// Mirror of the Lean `implies`.
pub(super) fn implies(fs: &[Abs], gs: &[Abs]) -> bool {
    gs.len() <= fs.len() && fs.iter().zip(gs).all(|(a, b)| le(a, b))
}

fn join_abs(a: &Abs, b: &Abs) -> Abs {
    let set = match (&a.set, &b.set) {
        (Some(x), Some(y)) => {
            let u: BTreeSet<U256> = x.iter().chain(y).copied().collect();
            (u.len() <= MAX_SET).then(|| u.into_iter().collect())
        }
        _ => None,
    };
    Abs {
        bits: a.bits.max(b.bits),
        set,
    }
}

fn join(a: &[Abs], b: &[Abs]) -> Facts {
    canon(a.iter().zip(b).map(|(x, y)| join_abs(x, y)).collect())
}

/// Drop trailing slots without information.
fn canon(mut fs: Facts) -> Facts {
    while fs.last().is_some_and(is_top) {
        fs.pop();
    }
    fs
}

/// Stack shape of an instruction outside windows: inputs popped and facts
/// about the pushed values, mirroring the Lean `eff_*` lemmas.
pub(super) fn shape(op: u8) -> Option<(usize, Facts, &'static str)> {
    let t = || vec![top()];
    let addr = || {
        vec![Abs {
            bits: 160,
            set: None,
        }]
    };
    Some(match op {
        0x0a => (2, t(), "eff_exp"),
        0x08 => (3, t(), "eff_addmod"),
        0x09 => (3, t(), "eff_mulmod"),
        0x30 => (0, addr(), "eff_address"),
        0x32 => (0, addr(), "eff_origin"),
        0x33 => (0, addr(), "eff_caller"),
        0x34 => (0, t(), "eff_callvalue"),
        0x36 => (0, t(), "eff_calldatasize"),
        0x3a => (0, t(), "eff_gasprice"),
        0x48 => (0, t(), "eff_basefee"),
        0x44 => (0, t(), "eff_prevrandao"),
        0x4a => (0, t(), "eff_blobbasefee"),
        0x38 => (0, t(), "eff_codesize"),
        0x42 => (0, t(), "eff_timestamp"),
        0x43 => (0, t(), "eff_number"),
        0x45 => (0, t(), "eff_gaslimit"),
        0x46 => (0, t(), "eff_chainid"),
        0x41 => (0, t(), "eff_coinbase"),
        0x47 => (0, t(), "eff_selfbalance"),
        0x59 => (0, t(), "eff_msize"),
        0x3d => (0, t(), "eff_returndatasize"),
        0x52 => (2, vec![], "eff_mstore"),
        0x53 => (2, vec![], "eff_mstore8"),
        0x20 => (2, t(), "eff_keccak256"),
        0x37 => (3, vec![], "eff_calldatacopy"),
        0x5e => (3, vec![], "eff_mcopy"),
        0x3e => (3, vec![], "eff_returndatacopy"),
        0xa0 => (2, vec![], "eff_log0"),
        0xa1 => (3, vec![], "eff_log1"),
        0xa2 => (4, vec![], "eff_log2"),
        0xa3 => (5, vec![], "eff_log3"),
        0xa4 => (6, vec![], "eff_log4"),
        0x40 => (1, t(), "eff_blockhash"),
        0x49 => (1, t(), "eff_blobhash"),
        0x51 => (1, t(), "eff_mload"),
        0x35 => (1, t(), "eff_calldataload"),
        0x54 => (1, t(), "eff_sload"),
        0x5c => (1, t(), "eff_tload"),
        0x31 => (1, t(), "eff_balance"),
        0x3b => (1, t(), "eff_extcodesize"),
        0x55 => (2, vec![], "eff_sstore"),
        0x5d => (2, vec![], "eff_tstore"),
        0x5b => (0, vec![], "eff_jumpdest"),
        0x58 => (0, t(), "eff_pc"),
        _ => return None,
    })
}

/// Facts after one non-branching instruction (Lean `xferW` or `Shape`).
pub(super) fn xfer_same(bytes: &[u8], fs: &[Abs]) -> Facts {
    if window_op(bytes) {
        let (a, m, _, _) = sym_run(&[(0, bytes.to_vec())]);
        return xfer_syms(&a, m, fs);
    }
    match shape(bytes[0]) {
        Some((pop, outs, _)) => {
            let mut out = outs;
            out.extend(fs.iter().skip(pop).cloned());
            out
        }
        None => Vec::new(),
    }
}

/// Facts at the end of a window, from the original instructions.
pub(super) fn xfer_window(old: &[(usize, Vec<u8>)], fs: &[Abs]) -> Facts {
    let (a, m, _, _) = sym_run(old);
    xfer_syms(&a, m, fs)
}

pub(super) fn drop(fs: &[Abs], n: usize) -> Facts {
    fs.iter().skip(n).cloned().collect()
}

/// Destinations a jump may take given the facts about its target slot; `None`
/// means unknown, so every JUMPDEST.
fn targets(head: Option<&Abs>) -> Option<Vec<U256>> {
    head.and_then(|a| a.set.clone())
}

/// Successor of one entry, with the facts the Lean transfer produces.
pub(super) enum Edge {
    /// A fixed successor pc.
    To(usize, Facts),
    /// A jump with known destinations: each valid one gets the tail facts.
    Known(Vec<U256>, Facts),
    /// A jump with an unknown destination: every JUMPDEST without facts.
    Any,
}

pub(super) fn edges(pc: usize, obligation: &Obligation, fs: &[Abs], code: &[u8]) -> Vec<Edge> {
    let jump = |head: Option<&Abs>, tail: Facts| match targets(head) {
        Some(set) => Edge::Known(set, tail),
        None => Edge::Any,
    };
    match obligation {
        Obligation::Same { len, .. } => {
            vec![Edge::To(pc + len, xfer_same(&code[pc..pc + len], fs))]
        }
        Obligation::Jump => vec![jump(fs.first(), drop(fs, 1))],
        Obligation::Jumpi => vec![Edge::To(pc + 1, drop(fs, 2)), jump(fs.first(), drop(fs, 2))],
        Obligation::Halt { .. } | Obligation::FallOff | Obligation::Invalid => vec![],
        Obligation::Power(site) => {
            let mut out = vec![top()];
            out.extend(drop(fs, 1));
            vec![Edge::To(site.pc + site.width + 2, out)]
        }
        Obligation::Thread(site) => vec![
            Edge::To(site.pc + site.width + 2, drop(fs, 1)),
            Edge::To(site.to, drop(fs, 1)),
        ],
        Obligation::Window(site) => vec![Edge::To(site.end, xfer_window(&site.old, fs))],
        Obligation::Call(site) => {
            let mut out = vec![top()];
            out.extend(drop(fs, site.pop()));
            vec![Edge::To(pc + site.len(), out)]
        }
        Obligation::CodeCopy => vec![Edge::To(pc + 1, drop(fs, 3))],
        Obligation::ExtCode { hash: true } => {
            let mut out = vec![top()];
            out.extend(drop(fs, 1));
            vec![Edge::To(pc + 1, out)]
        }
        Obligation::ExtCode { hash: false } => vec![Edge::To(pc + 1, drop(fs, 4))],
    }
}

/// The fact lists at one pc. Lists whose calling contexts agree on the
/// topmost `level` return-address slots are joined.
struct Slot {
    level: usize,
    list: Vec<Facts>,
}

pub(super) struct Analysis {
    /// Fact lists per reached pc, sorted.
    pub entries: BTreeMap<usize, Vec<Facts>>,
    pub obligations: BTreeMap<usize, Obligation>,
    /// Some jump has an unknown destination.
    pub any: bool,
}

impl Analysis {
    /// The entry at `pc` that the transfer result `fs` implies.
    pub fn target(&self, pc: usize, fs: &[Abs]) -> Option<(usize, &Facts)> {
        let list = self.entries.get(&pc)?;
        list.iter()
            .enumerate()
            .find(|(_, g)| g.as_slice() == fs)
            .or_else(|| list.iter().enumerate().find(|(_, g)| implies(fs, g)))
    }
}

/// `c` as a valid jump destination.
pub(super) fn dest(dests: &BTreeSet<usize>, c: U256) -> Option<usize> {
    let c = usize::try_from(c).ok()?;
    dests.contains(&c).then_some(c)
}

/// Explore (pc, facts) entries from pc 0 with an empty stack. Without
/// `precise`, every entry has no facts, so each jump may reach every JUMPDEST
/// and each pc has one entry.
pub(super) fn analyze(
    code: &[u8],
    jumpdests: &[usize],
    precise: bool,
    obligation: &mut dyn FnMut(usize) -> Result<Obligation>,
) -> Result<Analysis> {
    let dests: BTreeSet<usize> = jumpdests.iter().copied().collect();
    let mut slots: BTreeMap<usize, Slot> = BTreeMap::new();
    let mut obligations: BTreeMap<usize, Obligation> = BTreeMap::new();
    let mut queue: VecDeque<(usize, Facts)> = VecDeque::new();
    let mut any = false;
    // The calling context of a fact list: its possible return addresses.
    // The calling context of a fact list: its topmost `level` possible
    // return addresses.
    let context = |fs: &Facts, level: usize| -> Vec<Option<Vec<U256>>> {
        let mut seen = 0;
        let mut key: Vec<Option<Vec<U256>>> = fs
            .iter()
            .map(|a| {
                let set = a
                    .set
                    .clone()
                    .filter(|set| set.iter().all(|c| dest(&dests, *c).is_some()));
                if set.is_some() {
                    seen += 1;
                }
                set.filter(|_| seen <= level)
            })
            .collect();
        while key.last().is_some_and(Option::is_none) {
            key.pop();
        }
        key
    };
    let add =
        |slots: &mut BTreeMap<usize, Slot>, queue: &mut VecDeque<(usize, Facts)>, pc, fs: Facts| {
            let fs = if precise { canon(fs) } else { Vec::new() };
            let slot = slots.entry(pc).or_insert(Slot {
                level: usize::MAX,
                list: Vec::new(),
            });
            if slot.list.contains(&fs) {
                return;
            }
            let key = context(&fs, slot.level);
            if let Some(same) = slot.list.iter_mut().find(|g| context(g, slot.level) == key) {
                let j = join(same, &fs);
                if j != *same {
                    *same = j.clone();
                    queue.push_back((pc, j));
                }
                return;
            }
            slot.list.push(fs.clone());
            queue.push_back((pc, fs));
            // Too many contexts: keep fewer return addresses apart.
            while slot.list.len() > MAX_CONTEXTS {
                slot.level = match slot.level {
                    usize::MAX => 2,
                    n => n - 1,
                };
                let mut coarse: Vec<Facts> = Vec::new();
                for g in std::mem::take(&mut slot.list) {
                    let key = context(&g, slot.level);
                    match coarse.iter_mut().find(|h| context(h, slot.level) == key) {
                        Some(h) => *h = join(h, &g),
                        None => coarse.push(g),
                    }
                }
                slot.list = coarse;
                for g in &slot.list {
                    queue.push_back((pc, g.clone()));
                }
            }
        };
    add(&mut slots, &mut queue, 0, Vec::new());
    while let Some((pc, fs)) = queue.pop_front() {
        let current = slots.get(&pc).is_some_and(|slot| slot.list.contains(&fs));
        if !current {
            continue;
        }
        if let std::collections::btree_map::Entry::Vacant(e) = obligations.entry(pc) {
            e.insert(obligation(pc)?);
        }
        for edge in edges(pc, &obligations[&pc], &fs, code) {
            match edge {
                Edge::To(next, g) => add(&mut slots, &mut queue, next, g),
                Edge::Known(set, tail) => {
                    for c in set {
                        if let Some(c) = dest(&dests, c) {
                            add(&mut slots, &mut queue, c, tail.clone());
                        }
                    }
                }
                Edge::Any => {
                    if !any {
                        any = true;
                        for &d in jumpdests {
                            add(&mut slots, &mut queue, d, Vec::new());
                        }
                    }
                }
            }
        }
    }
    let mut entries: BTreeMap<usize, Vec<Facts>> = slots
        .into_iter()
        .map(|(pc, slot)| {
            let mut list = slot.list;
            list.sort();
            (pc, list)
        })
        .collect();
    // Keep only entries reachable from pc 0 (and the fact-free JUMPDEST entries
    // that unknown jumps reach); joins can leave earlier contexts unused.
    let analysis = Analysis {
        entries: entries.clone(),
        obligations,
        any,
    };
    let mut live: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut stack: Vec<(usize, usize)> = vec![(0, 0)];
    if any {
        for &d in jumpdests {
            if let Some((i, _)) = analysis.target(d, &[]) {
                stack.push((d, i));
            }
        }
    }
    while let Some((pc, i)) = stack.pop() {
        if !live.insert((pc, i)) {
            continue;
        }
        let fs = &analysis.entries[&pc][i];
        for edge in edges(pc, &analysis.obligations[&pc], fs, code) {
            let mut go = |next: usize, g: &[Abs]| {
                if let Some((j, _)) = analysis.target(next, g) {
                    stack.push((next, j));
                }
            };
            match edge {
                Edge::To(next, g) => go(next, &g),
                Edge::Known(set, tail) => {
                    for c in set {
                        if let Some(c) = dest(&dests, c) {
                            go(c, &tail);
                        }
                    }
                }
                Edge::Any => {}
            }
        }
    }
    for (pc, list) in entries.iter_mut() {
        let keep: Vec<Facts> = list
            .iter()
            .enumerate()
            .filter(|(i, _)| live.contains(&(*pc, *i)))
            .map(|(_, g)| g.clone())
            .collect();
        *list = keep;
    }
    entries.retain(|_, list| !list.is_empty());
    let Analysis {
        mut obligations,
        any,
        ..
    } = analysis;
    obligations.retain(|pc, _| entries.contains_key(pc));
    Ok(Analysis {
        entries,
        obligations,
        any,
    })
}

/// Join of every context at `pc`, for choosing windows before the final plan.
pub(super) fn joined(analysis: &Analysis, pc: usize) -> Facts {
    analysis
        .entries
        .get(&pc)
        .and_then(|list| list.iter().cloned().reduce(|a, b| join(&a, &b)))
        .unwrap_or_default()
}
