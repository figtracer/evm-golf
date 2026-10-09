//! Trusted exact-byte proof emission for a bounded pure instruction subset.
//!
//! Input bytes select no Lean syntax. The emitted kernel checks remain the
//! authority; symbolic normalization and finite stack-fault checks are filters.
use anyhow::{Result, bail, ensure};
use revm::primitives::U256;
use std::{collections::BTreeSet, fmt::Write as _};

use super::{Instruction, decode, prelude as model_prelude, push_value};

#[cfg(test)]
mod regression;

// Bound generated source independently of the existing admitted rule families.
const MAX_BYTES: usize = 64;
const MAX_OPS: usize = 16;
const MAX_REQUIRED: usize = 8;
const MAX_PEAK: usize = 2;
const STACK_LIMIT: usize = 1024;
const ALGEBRA: &str = "BitVec.and_assoc, BitVec.and_comm, GolfGenerated.and_left_comm, BitVec.and_self, BitVec.zero_add, BitVec.add_zero, BitVec.or_zero, BitVec.zero_or, BitVec.or_self, BitVec.xor_zero, BitVec.zero_xor, BitVec.xor_self, BitVec.not_not, BitVec.mul_zero, BitVec.zero_mul, BitVec.mul_one, BitVec.one_mul";

pub(super) struct WindowProof {
    pub source: String,
    pub names: Vec<String>,
    pub required: usize,
    pub delta: isize,
    pub peak: usize,
    pub before_ops: usize,
    pub after_ops: usize,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum Word {
    Constant(U256),
    Input(usize),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Xor(Box<Self>, Box<Self>),
    Not(Box<Self>),
    Add(Box<Self>, Box<Self>),
    Mul(Box<Self>, Box<Self>),
    Sub(Box<Self>, Box<Self>),
    Shl(Box<Self>, Box<Self>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Profile {
    required: usize,
    delta: isize,
    peak: usize,
    gas: u64,
}

struct Step {
    raw: Vec<Word>,
    normalized: Vec<Word>,
}

impl Word {
    fn lean(&self) -> String {
        match self {
            Self::Constant(value) => format!("(BitVec.ofNat 256 {value})"),
            Self::Input(index) => format!("a{index}"),
            Self::And(left, right) => format!("({} &&& {})", left.lean(), right.lean()),
            Self::Or(left, right) => format!("({} ||| {})", left.lean(), right.lean()),
            Self::Xor(left, right) => format!("({} ^^^ {})", left.lean(), right.lean()),
            Self::Not(word) => format!("(~~~{})", word.lean()),
            Self::Add(top, next) => format!("({} + {})", top.lean(), next.lean()),
            Self::Mul(top, next) => format!("({} * {})", top.lean(), next.lean()),
            Self::Sub(top, next) => format!("({} - {})", top.lean(), next.lean()),
            Self::Shl(value, shift) => format!("({} <<< ({}).toNat)", value.lean(), shift.lean()),
        }
    }

    fn folded(&self) -> Option<U256> {
        match self {
            Self::Or(left, right) | Self::Xor(left, right) => match (&**left, &**right) {
                (Self::Constant(a), Self::Constant(b)) => Some(if matches!(self, Self::Or(..)) {
                    *a | *b
                } else {
                    *a ^ *b
                }),
                _ => None,
            },
            Self::Not(word) => match &**word {
                Self::Constant(value) => Some(!*value),
                _ => None,
            },
            Self::Add(top, next) => match (&**top, &**next) {
                (Self::Constant(a), Self::Constant(b)) => Some(a.wrapping_add(*b)),
                _ => None,
            },
            Self::Mul(top, next) => match (&**top, &**next) {
                (Self::Constant(a), Self::Constant(b)) => Some(a.wrapping_mul(*b)),
                _ => None,
            },
            Self::Sub(top, next) => match (&**top, &**next) {
                (Self::Constant(a), Self::Constant(b)) => Some(a.wrapping_sub(*b)),
                _ => None,
            },
            Self::Shl(value, shift) => match (&**value, &**shift) {
                (Self::Constant(value), Self::Constant(shift)) => {
                    Some(if *shift >= U256::from(256) {
                        U256::ZERO
                    } else {
                        *value << shift.to::<usize>()
                    })
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn normalize(&self) -> Self {
        fn collect(word: &Word, terms: &mut BTreeSet<Word>) {
            match word {
                Word::And(left, right) => {
                    collect(left, terms);
                    collect(right, terms);
                }
                _ => {
                    terms.insert(word.clone());
                }
            }
        }
        match self {
            Self::Constant(_) | Self::Input(_) => self.clone(),
            Self::Add(top, next) => {
                let a = top.normalize();
                let b = next.normalize();
                if a == Self::Constant(U256::ZERO) {
                    b
                } else if b == Self::Constant(U256::ZERO) {
                    a
                } else {
                    let node = Self::Add(Box::new(a), Box::new(b));
                    node.folded().map(Self::Constant).unwrap_or(node)
                }
            }
            Self::Mul(top, next) => {
                let a = top.normalize();
                let b = next.normalize();
                if a == Self::Constant(U256::ZERO) || b == Self::Constant(U256::ZERO) {
                    Self::Constant(U256::ZERO)
                } else if a == Self::Constant(U256::ONE) {
                    b
                } else if b == Self::Constant(U256::ONE) {
                    a
                } else {
                    let node = Self::Mul(Box::new(a), Box::new(b));
                    node.folded().map(Self::Constant).unwrap_or(node)
                }
            }
            Self::Sub(top, next) | Self::Shl(top, next) => {
                let a = Box::new(top.normalize());
                let b = Box::new(next.normalize());
                let node = if matches!(self, Self::Sub(..)) {
                    Self::Sub(a, b)
                } else {
                    Self::Shl(a, b)
                };
                node.folded().map(Self::Constant).unwrap_or(node)
            }
            Self::Or(left, right) | Self::Xor(left, right) => {
                let a = left.normalize();
                let b = right.normalize();
                if a == Self::Constant(U256::ZERO) {
                    b
                } else if b == Self::Constant(U256::ZERO) {
                    a
                } else if a == b {
                    if matches!(self, Self::Or(..)) {
                        a
                    } else {
                        Self::Constant(U256::ZERO)
                    }
                } else {
                    let node = if matches!(self, Self::Or(..)) {
                        Self::Or(Box::new(a), Box::new(b))
                    } else {
                        Self::Xor(Box::new(a), Box::new(b))
                    };
                    node.folded().map(Self::Constant).unwrap_or(node)
                }
            }
            Self::Not(word) => {
                let word = word.normalize();
                if let Self::Not(inner) = word {
                    *inner
                } else {
                    let node = Self::Not(Box::new(word));
                    node.folded().map(Self::Constant).unwrap_or(node)
                }
            }
            Self::And(left, right) => {
                let mut terms = BTreeSet::new();
                collect(&left.normalize(), &mut terms);
                collect(&right.normalize(), &mut terms);
                terms
                    .into_iter()
                    .reduce(|a, b| Self::And(Box::new(a), Box::new(b)))
                    .unwrap()
            }
        }
    }
}

#[cfg(test)]
pub(super) fn certificate(before: &[u8], after: &[u8]) -> Result<WindowProof> {
    certificate_in(before, after, None)
}

// The only selectable namespace component is a trusted numeric dedup index.
pub(super) fn certificate_for_pair(
    before: &[u8],
    after: &[u8],
    index: usize,
) -> Result<WindowProof> {
    certificate_in(before, after, Some(index))
}

pub(super) fn batch_prelude() -> Result<String> {
    let mut source = prelude()?;
    source.push_str("\nnamespace GolfGenerated\n");
    source.push_str(AND_COMMUTATION);
    source.push_str("end GolfGenerated\n");
    source.push_str(FAULT_MODEL);
    Ok(source)
}

fn prelude() -> Result<String> {
    let mut source = model_prelude();
    for text in [
        include_str!("../../lean/Fragment.lean"),
        include_str!("../../lean/Stack.lean"),
        include_str!("../../lean/Gas.lean"),
        include_str!("../../lean/Composition.lean"),
        include_str!("../../lean/LayoutScanner.lean"),
        include_str!("../../lean/Layout.lean"),
        include_str!("../../lean/GenericWindowProfile.lean"),
    ] {
        writeln!(source, "\n{text}").unwrap();
    }
    Ok(source)
}

const AND_COMMUTATION: &str = "theorem and_left_comm (a b c : Golf.Word) : a &&& (b &&& c) = b &&& (a &&& c) := by\n rw [← BitVec.and_assoc, BitVec.and_comm a b, BitVec.and_assoc]\n";

struct Checked {
    old: Vec<Instruction>,
    new: Vec<Instruction>,
    a: Profile,
    b: Profile,
    old_steps: Vec<Step>,
    new_steps: Vec<Step>,
}

/// Check a byte pair without emitting Lean source: equal length and stack
/// profile, lower static gas, equal fault classes at every height, and equal
/// normalized symbolic outputs. Returns the required input word count.
pub(super) fn check(before: &[u8], after: &[u8]) -> Result<usize> {
    Ok(checked(before, after)?.a.required)
}

fn checked(before: &[u8], after: &[u8]) -> Result<Checked> {
    ensure!(before.len() == after.len(), "proposal changes byte length");
    let (old, a) = inspect(before)?;
    let (new, b) = inspect(after)?;
    ensure!(
        (a.required, a.delta, a.peak) == (b.required, b.delta, b.peak),
        "proposal changes stack profile"
    );
    ensure!(
        a.required <= MAX_REQUIRED && a.peak <= MAX_PEAK,
        "proposal exceeds generated-proof stack bounds"
    );
    ensure!(
        a.required + a.peak <= STACK_LIMIT,
        "proposal has no admissible stack height"
    );
    ensure!(b.gas < a.gas, "proposal does not reduce static gas");
    for height in 0..=STACK_LIMIT {
        ensure!(
            fault(&old, height) == fault(&new, height),
            "proposal changes stack fault at height {height}"
        );
    }
    let words: Vec<_> = (0..a.required).map(Word::Input).collect();
    let (old_steps, old_failure) = trace(&old, &words);
    let (new_steps, new_failure) = trace(&new, &words);
    ensure!(
        !old_failure && !new_failure,
        "inconsistent required stack derivation"
    );
    ensure!(
        old_steps.last().unwrap().normalized == new_steps.last().unwrap().normalized,
        "unsupported symbolic output equality"
    );
    Ok(Checked {
        old,
        new,
        a,
        b,
        old_steps,
        new_steps,
    })
}

fn certificate_in(before: &[u8], after: &[u8], index: Option<usize>) -> Result<WindowProof> {
    let Checked {
        old,
        new,
        a,
        b,
        old_steps,
        new_steps,
    } = checked(before, after)?;
    let output = &old_steps.last().unwrap().normalized;
    let namespace = index.map_or_else(
        || "GolfGenerated".to_owned(),
        |index| format!("GolfGenerated.Pair{index}"),
    );
    let mut source = if index.is_none() {
        prelude()?
    } else {
        String::new()
    };
    writeln!(source, "\nnamespace {namespace}").unwrap();
    if index.is_none() {
        source.push_str(AND_COMMUTATION);
    }
    let folds = emit_folds(&mut source, old_steps.iter().chain(&new_steps));
    emit_side(&mut source, "before", before, &old, a, &old_steps, &folds);
    emit_side(&mut source, "after", after, &new, b, &new_steps, &folds);
    emit_equal(&mut source, a);
    emit_wrappers(&mut source, a, output);
    writeln!(
        source,
        "def gas_improvement : GolfGas.Improvement before after where
 beforeCost := {}
 afterCost := {}
 beforeChecked := by decide +kernel
 afterChecked := by decide +kernel
 cheaper := by decide +kernel
theorem gas_refinement (stack : List Golf.Word) (gas : Nat) (x y : Golf.Word)
     (output : List Golf.Word) (budget : {} ≤ gas)
     (success : GolfBounded.run (before.length+1) before stack x y = some output) :
   GolfGas.run GolfGas.cancun (before.length+1) before stack gas x y = some (output, gas-{}) ∧
   GolfGas.run GolfGas.cancun (after.length+1) after stack gas x y = some (output, gas-{}) ∧
   gas-{} < gas-{} ∧ gas-{} ≤ gas :=
  gas_improvement.refines all_height stack gas x y output budget success",
        a.gas, b.gas, a.gas, a.gas, b.gas, a.gas, b.gas, b.gas
    )
    .unwrap();
    writeln!(source, "end {namespace}").unwrap();
    if index.is_none() {
        source.push_str(FAULT_MODEL);
    }
    // Explicit boundary heights plus the generic middle-height lemma cover all
    // 1,025 heights; equal lengths make one fuel bound serve both sides.
    let bound = before.len() + 1;
    writeln!(source,"\nnamespace {namespace}\ntheorem fault_classes : (List.range 1025).all (fun h => decide (GolfGeneratedFault.run (before.length+1) before h = GolfGeneratedFault.run (after.length+1) after h)) = true :=\n GolfGeneratedFault.classes_of_bounds before after {bound} (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)\nend {namespace}").unwrap();
    let names = [
        "before_profile",
        "after_profile",
        "before_success",
        "after_success",
        "all_height",
        "context",
        "fault_classes",
        "gas_improvement",
        "gas_refinement",
        "success",
        "underflow",
        "overflow",
    ]
    .map(|name| format!("{namespace}.{name}"))
    .to_vec();
    for name in &names {
        writeln!(source, "#print axioms {name}").unwrap();
    }
    Ok(WindowProof {
        source,
        names,
        required: a.required,
        delta: a.delta,
        peak: a.peak,
        before_ops: old.len(),
        after_ops: new.len(),
    })
}

fn inspect(code: &[u8]) -> Result<(Vec<Instruction>, Profile)> {
    ensure!(
        !code.is_empty() && code.len() <= MAX_BYTES,
        "proposal window must contain 1..={MAX_BYTES} bytes"
    );
    let ops = decode(code);
    ensure!(
        ops.len() <= MAX_OPS,
        "proposal exceeds {MAX_OPS} instructions"
    );
    let mut height = 0isize;
    let mut required = 0usize;
    let mut peak = 0usize;
    let mut gas = 0u64;
    for instruction in &ops {
        let op = instruction.bytes[0];
        let (need, delta, cost) = match op {
            0x5f..=0x7f => {
                ensure!(push_value(&instruction.bytes).is_some(), "truncated PUSH");
                (0, 1, if op == 0x5f { 2 } else { 3 })
            }
            0x01 | 0x03 | 0x16..=0x18 | 0x1b => (2, -1, 3),
            0x02 => (2, -1, 5),
            0x19 => (1, 0, 3),
            0x50 => (1, -1, 2),
            0x80..=0x8f => (isize::from(op - 0x7f), 1, 3),
            0x90..=0x9f => (isize::from(op - 0x8e), 0, 3),
            _ => bail!(
                "unsupported proposal opcode 0x{op:02x}; expected PUSH/AND/OR/XOR/NOT/POP/SUB/SHL/DUP/ADD/MUL/SWAP"
            ),
        };
        required = required.max((need - height).max(0) as usize);
        height += delta;
        peak = peak.max(height.max(0) as usize);
        gas += cost;
    }
    Ok((
        ops,
        Profile {
            required,
            delta: height,
            peak,
            gas,
        },
    ))
}

// Sufficient-gas stack guards only; the Lean abstraction is not a revm
// correspondence proof and does not establish out-of-gas precedence.
fn fault(ops: &[Instruction], mut height: usize) -> u8 {
    for instruction in ops {
        match instruction.bytes[0] {
            0x5f..=0x7f => {
                if height >= STACK_LIMIT {
                    return 2;
                }
                height += 1;
            }
            0x01..=0x03 | 0x16..=0x18 | 0x1b => {
                if height < 2 {
                    return 1;
                }
                height -= 1;
            }
            0x80..=0x8f => {
                // Pinned revm reports missing DUP input as overflow, not underflow.
                let depth = usize::from(instruction.bytes[0] - 0x7f);
                if height < depth || height >= STACK_LIMIT {
                    return 2;
                }
                height += 1;
            }
            0x90..=0x9f => {
                if height < usize::from(instruction.bytes[0] - 0x8e) {
                    return 1;
                }
            }
            0x19 => {
                if height < 1 {
                    return 1;
                }
            }
            0x50 => {
                if height < 1 {
                    return 1;
                }
                height -= 1;
            }
            _ => unreachable!("inspect rejects unsupported instructions"),
        }
    }
    0
}

fn trace(ops: &[Instruction], input: &[Word]) -> (Vec<Step>, bool) {
    let mut stack = input.to_vec();
    let mut steps = Vec::new();
    for instruction in ops {
        match instruction.bytes[0] {
            0x5f..=0x7f => stack.insert(0, Word::Constant(push_value(&instruction.bytes).unwrap())),
            0x80..=0x8f => {
                let index = usize::from(instruction.bytes[0] - 0x80);
                let Some(word) = stack.get(index).cloned() else {
                    return (steps, true);
                };
                stack.insert(0, word);
            }
            0x90..=0x9f => {
                let index = usize::from(instruction.bytes[0] - 0x8f);
                if index >= stack.len() {
                    return (steps, true);
                }
                stack.swap(0, index);
            }
            0x19 => {
                if stack.is_empty() {
                    return (steps, true);
                }
                stack[0] = Word::Not(Box::new(stack[0].clone()));
            }
            0x50 => {
                if stack.is_empty() {
                    return (steps, true);
                }
                stack.remove(0);
            }
            0x01..=0x03 | 0x16..=0x18 | 0x1b => {
                if stack.len() < 2 {
                    return (steps, true);
                }
                let a = stack.remove(0);
                let b = stack.remove(0);
                stack.insert(
                    0,
                    match instruction.bytes[0] {
                        0x01 => Word::Add(Box::new(a), Box::new(b)),
                        0x02 => Word::Mul(Box::new(a), Box::new(b)),
                        0x03 => Word::Sub(Box::new(a), Box::new(b)),
                        0x17 => Word::Or(Box::new(a), Box::new(b)),
                        0x18 => Word::Xor(Box::new(a), Box::new(b)),
                        0x1b => Word::Shl(Box::new(b), Box::new(a)),
                        _ => Word::And(Box::new(a), Box::new(b)),
                    },
                );
            }
            _ => unreachable!("inspect rejects unsupported instructions"),
        }
        let raw = stack.clone();
        stack = stack.iter().map(Word::normalize).collect();
        steps.push(Step {
            raw,
            normalized: stack.clone(),
        });
    }
    (steps, false)
}

// Exact closed arithmetic equalities are checked by the kernel, not trusted as
// results of host arithmetic. Numeric names and terms are generated from bytes.
fn emit_folds<'a>(out: &mut String, steps: impl Iterator<Item = &'a Step>) -> String {
    fn collect(word: &Word, nodes: &mut BTreeSet<Word>) {
        if word.folded().is_some() {
            nodes.insert(word.clone());
        }
        match word {
            Word::And(a, b)
            | Word::Or(a, b)
            | Word::Xor(a, b)
            | Word::Add(a, b)
            | Word::Mul(a, b)
            | Word::Sub(a, b)
            | Word::Shl(a, b) => {
                collect(a, nodes);
                collect(b, nodes);
            }
            Word::Not(word) => collect(word, nodes),
            _ => {}
        }
    }
    let mut nodes = BTreeSet::new();
    for step in steps {
        for word in &step.raw {
            collect(word, &mut nodes);
        }
    }
    let mut names = String::new();
    for (index, node) in nodes.iter().enumerate() {
        let value = node.folded().unwrap();
        writeln!(
            out,
            "theorem constant_{index} : {} = (BitVec.ofNat 256 {value}) := by",
            node.lean()
        )
        .unwrap();
        if matches!(node,Word::Shl(_,shift) if matches!(&**shift,Word::Constant(n) if *n >= U256::from(256)))
        {
            // Avoid evaluating 2^shift when the exact 256-bit shift is enormous.
            out.push_str(" apply BitVec.shiftLeft_eq_zero\n decide +kernel\n");
        } else {
            out.push_str(" decide +kernel\n");
        }
        write!(names, ", constant_{index}").unwrap();
    }
    names
}

fn stack(words: &[Word], tail: &str) -> String {
    let mut parts: Vec<_> = words.iter().map(Word::lean).collect();
    parts.push(tail.into());
    format!("({})", parts.join(" :: "))
}
fn parameters(count: usize) -> String {
    (0..count)
        .map(|i| format!("a{i}"))
        .collect::<Vec<_>>()
        .join(" ")
}
fn step_proof(step: &Step, tail: &str, folds: &str) -> String {
    if step.raw == step.normalized {
        "rfl".into()
    } else {
        format!(
            "change some {} = some {}; simp only [{ALGEBRA}{folds}]",
            stack(&step.raw, tail),
            stack(&step.normalized, tail)
        )
    }
}
fn complete(ops: &[Instruction]) -> String {
    ops.iter().rev().fold("GolfComposition.Complete.nil".into(),|rest,op|format!("(GolfComposition.Complete.step (op := {}) (immediate := {:?}) (by decide +kernel) {rest})",op.bytes[0],&op.bytes[1..]))
}

fn emit_side(
    out: &mut String,
    label: &str,
    code: &[u8],
    ops: &[Instruction],
    profile: Profile,
    steps: &[Step],
    folds: &str,
) {
    let n = profile.required;
    let peak = profile.peak;
    let params = parameters(n);
    let input: Vec<_> = (0..n).map(Word::Input).collect();
    let bound = STACK_LIMIT - peak - n;
    let fuel = code.len() + 1;
    writeln!(out,"def {label} : List Nat := {code:?}\ntheorem {label}_bytes : {label}.all (fun b => b < 256) = true := by decide +kernel\ntheorem {label}_complete : GolfComposition.Complete {label} {} := by\n exact {}\ntheorem {label}_profile : GolfGenericWindow.profile {label} = some ({n},{},{peak}) := by decide +kernel",ops.len(),complete(ops),profile.delta).unwrap();
    writeln!(out,"theorem {label}_success ({params} x y : Golf.Word) (tail : List Golf.Word) (height : tail.length ≤ {bound}) :\n GolfBounded.run {fuel} {label} {} x y = some {} := by\n unfold {label}",stack(&input,"tail"),stack(&steps.last().unwrap().normalized,"tail")).unwrap();
    for step in steps {
        writeln!(out," apply GolfBounded.step_success (next := {}) (height := by (try simp only [List.length_cons]) <;> omega) (step := by {})",stack(&step.normalized,"tail"),step_proof(step,"tail",folds)).unwrap();
    }
    out.push_str(" apply GolfBounded.empty_success\n try simp only [List.length_cons]\n omega\n");
    for height in 0..n {
        let short: Vec<_> = (0..height).map(Word::Input).collect();
        let (history, failed) = trace(ops, &short);
        assert!(failed);
        writeln!(out,"theorem {label}_short{height} ({} x y : Golf.Word) : GolfBounded.run {fuel} {label} {} x y = none := by\n unfold {label}",parameters(height),stack(&short,"[]")).unwrap();
        for step in history {
            writeln!(
                out,
                " apply GolfBounded.step_failure (next := {}) (step := by {})",
                stack(&step.normalized, "[]"),
                step_proof(&step, "[]", folds)
            )
            .unwrap();
        }
        out.push_str(" rfl\n");
    }
    writeln!(out,"theorem {label}_overflow ({params} x y : Golf.Word) (tail : List Golf.Word) (height : {} ≤ {}.length) : GolfBounded.run {fuel} {label} {} x y = none := by\n unfold {label}",STACK_LIMIT-peak+1,stack(&input,"tail"),stack(&input,"tail")).unwrap();
    if peak > 0 {
        for step in steps {
            writeln!(
                out,
                " apply GolfBounded.step_failure (next := {}) (step := by {})",
                stack(&step.normalized, "tail"),
                step_proof(step, "tail", folds)
            )
            .unwrap();
            if step.normalized.len() as isize - n as isize == peak as isize {
                break;
            }
        }
    }
    out.push_str(
        " apply GolfBounded.overflow_failure\n try simp only [List.length_cons] at *\n omega\n",
    );
}

fn emit_equal(out: &mut String, profile: Profile) {
    let n = profile.required;
    let peak = profile.peak;
    let mut indent = " ".to_owned();
    let mut tail = "stack".to_owned();
    out.push_str("theorem all_height (stack : List Golf.Word) (x y : Golf.Word) :\n GolfBounded.run (before.length+1) before stack x y = GolfBounded.run (after.length+1) after stack x y := by\n");
    for i in 0..n {
        writeln!(out,"{indent}cases {tail} with\n{indent}| nil => exact (before_short{i} {} x y).trans (after_short{i} {} x y).symm\n{indent}| cons a{i} tail{i} =>",parameters(i),parameters(i)).unwrap();
        indent.push_str("  ");
        tail = format!("tail{i}");
    }
    let params = parameters(n);
    let words: Vec<_> = (0..n).map(Word::Input).collect();
    writeln!(out,"{indent}by_cases height : {tail}.length ≤ {}\n{indent}· exact (before_success {params} x y {tail} height).trans (after_success {params} x y {tail} height).symm\n{indent}· have high : {} ≤ {}.length := by (try simp only [List.length_cons]) <;> omega\n{indent}  exact (before_overflow {params} x y {tail} high).trans (after_overflow {params} x y {tail} high).symm",STACK_LIMIT-peak-n,STACK_LIMIT-peak+1,stack(&words,&tail)).unwrap();
    out.push_str("theorem context : GolfComposition.ContextEquivalent before after := GolfComposition.context_of_equal before_complete after_complete all_height\n");
}

fn emit_wrappers(out: &mut String, profile: Profile, output: &[Word]) {
    let n = profile.required;
    let peak = profile.peak;
    let words: Vec<_> = (0..n).map(Word::Input).collect();
    if n == 0 {
        writeln!(
            out,
            "def output (stack : List Golf.Word) (_x _y : Golf.Word) : List Golf.Word := {}",
            stack(output, "stack")
        )
        .unwrap();
    } else {
        writeln!(out,"def output (stack : List Golf.Word) (_x _y : Golf.Word) : List Golf.Word :=\n match stack with\n | {} => {}\n | _ => []",stack(&words,"tail"),stack(output,"tail")).unwrap();
    }
    for name in ["success", "underflow", "overflow"] {
        let assumptions = match name {
            "success" => {
                format!("(required : {n} ≤ stack.length) (height : stack.length + {peak} ≤ 1024)")
            }
            "underflow" => format!("(height : stack.length < {n})"),
            _ => format!("(height : 1024 < stack.length + {peak})"),
        };
        let result = if name == "success" {
            "some (output stack x y)"
        } else {
            "none"
        };
        writeln!(out,"theorem {name} (stack : List Golf.Word) (x y : Golf.Word) {assumptions} :\n GolfBounded.run (before.length+1) before stack x y = {result} ∧\n GolfBounded.run (after.length+1) after stack x y = {result} := by").unwrap();
        let mut indent = " ".to_owned();
        let mut tail = "stack".to_owned();
        for i in 0..n {
            writeln!(out, "{indent}cases {tail} with\n{indent}| nil =>").unwrap();
            if name == "underflow" {
                writeln!(
                    out,
                    "{indent}  exact ⟨before_short{i} {} x y, after_short{i} {} x y⟩",
                    parameters(i),
                    parameters(i)
                )
                .unwrap();
            } else {
                writeln!(
                    out,
                    "{indent}  simp only [List.length_cons, List.length_nil] at *\n{indent}  omega"
                )
                .unwrap();
            }
            writeln!(out, "{indent}| cons a{i} tail{i} =>").unwrap();
            indent.push_str("  ");
            tail = format!("tail{i}");
        }
        let params = parameters(n);
        match name {
            "success" => {
                writeln!(out,"{indent}have bound : {tail}.length ≤ {} := by (try simp only [List.length_cons] at *) <;> omega\n{indent}exact ⟨before_success {params} x y {tail} bound, after_success {params} x y {tail} bound⟩",STACK_LIMIT-peak-n).unwrap();
            }
            "underflow" => {
                writeln!(
                    out,
                    "{indent}try simp only [List.length_cons] at *\n{indent}omega"
                )
                .unwrap();
            }
            _ => {
                writeln!(out,"{indent}have high : {} ≤ {}.length := by (try simp only [List.length_cons] at *) <;> omega\n{indent}exact ⟨before_overflow {params} x y {tail} high, after_overflow {params} x y {tail} high⟩",STACK_LIMIT-peak+1,stack(&words,&tail)).unwrap();
            }
        }
    }
}

const FAULT_MODEL: &str = r#"
namespace GolfGeneratedFault
inductive Result where | ok | underflow | overflow | unsupported deriving DecidableEq
-- Sufficient-gas stack guards, not a canonical revm correspondence theorem.
def run : Nat → List Nat → Nat → Result
 | 0, _, _ => .unsupported
 | fuel+1, code, height =>
   match code with
   | [] => .ok
   | op::rest =>
     if 95 ≤ op ∧ op ≤ 127 then
       let width := op-95
       if width > rest.length then .unsupported
       else if height ≥ 1024 then .overflow else run fuel (rest.drop width) (height+1)
     else if op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 22 ∨ op = 23 ∨ op = 24 ∨ op = 27 then
       if height < 2 then .underflow else run fuel rest (height-1)
     else if op = 80 then
       if height < 1 then .underflow else run fuel rest (height-1)
     else if op = 25 then
       if height < 1 then .underflow else run fuel rest height
     else if 128 ≤ op ∧ op ≤ 143 then
       if height < op-127 ∨ height ≥ 1024 then .overflow else run fuel rest (height+1)
     else if 144 ≤ op ∧ op ≤ 159 then
       if height < op-142 then .underflow else run fuel rest height
     else .unsupported

-- Away from both stack limits no guard can fire, so heights are interchangeable.
theorem run_congr : ∀ (fuel : Nat) (code : List Nat) (h h' : Nat),
    17 + fuel ≤ h → 17 + fuel ≤ h' → h + fuel < 1024 → h' + fuel < 1024 →
    run fuel code h = run fuel code h'
  | 0, _, _, _, _, _, _, _ => rfl
  | fuel+1, [], _, _, _, _, _, _ => rfl
  | fuel+1, op::rest, h, h', l, l', u, u' => by
    simp only [run]
    split
    · split
      · rfl
      · rw [if_neg (by omega), if_neg (by omega)]
        exact run_congr fuel _ _ _ (by omega) (by omega) (by omega) (by omega)
    · split
      · rw [if_neg (by omega), if_neg (by omega)]
        exact run_congr fuel _ _ _ (by omega) (by omega) (by omega) (by omega)
      · split
        · rw [if_neg (by omega), if_neg (by omega)]
          exact run_congr fuel _ _ _ (by omega) (by omega) (by omega) (by omega)
        · split
          · rw [if_neg (by omega), if_neg (by omega)]
            exact run_congr fuel _ _ _ (by omega) (by omega) (by omega) (by omega)
          · split
            · rw [if_neg (by omega), if_neg (by omega)]
              exact run_congr fuel _ _ _ (by omega) (by omega) (by omega) (by omega)
            · split
              · rw [if_neg (by omega), if_neg (by omega)]
                exact run_congr fuel _ _ _ (by omega) (by omega) (by omega) (by omega)
              · rfl

-- Equal fault classes at all 1,025 heights from the low and high boundary
-- heights alone; every middle height behaves like the first middle height.
theorem classes_of_bounds (before after : List Nat) (bound : Nat)
    (beforeBound : before.length + 1 ≤ bound) (afterBound : after.length + 1 ≤ bound)
    (room : 17 + 2 * bound < 1024)
    (low : (List.range (18 + bound)).all (fun h => decide
      (run (before.length+1) before h = run (after.length+1) after h)) = true)
    (high : (List.range (bound + 1)).all (fun i => decide
      (run (before.length+1) before (1024-i) = run (after.length+1) after (1024-i))) = true) :
    (List.range 1025).all (fun h => decide
      (run (before.length+1) before h = run (after.length+1) after h)) = true := by
  rw [List.all_eq_true] at low high ⊢
  intro h member
  rw [List.mem_range] at member
  by_cases small : h < 18 + bound
  · exact low h (List.mem_range.mpr small)
  · by_cases large : 1024 ≤ h + bound
    · have checked := high (1024 - h) (List.mem_range.mpr (by omega))
      rwa [show 1024 - (1024 - h) = h by omega] at checked
    · have middle := low (17 + bound) (List.mem_range.mpr (by omega))
      rw [run_congr (before.length+1) before h (17 + bound) (by omega) (by omega) (by omega) (by omega),
        run_congr (after.length+1) after h (17 + bound) (by omega) (by omega) (by omega) (by omega)]
      exact middle
end GolfGeneratedFault
"#;

#[cfg(test)]
mod tests {
    use super::*;
    use revm::primitives::hex;

    #[test]
    fn generated_windows_derive_profiles_and_fixed_roots() {
        for (before, after, required, delta, peak) in [
            ("600116600116", "610001165f50", 1, 0, 1),
            ("600150600250", "630000000050", 0, 0, 1),
            ("60ff1660ff16", "6100ff165f50", 1, 0, 1),
            ("600160081b", "6101005f50", 0, 1, 2),
            ("6001600203", "6100015f50", 0, 1, 2),
            ("6001506002501616", "6300000000501616", 3, -2, 1),
            ("600160025050600350", "6400000000005f5050", 0, 0, 2),
        ] {
            let proof =
                certificate(&hex::decode(before).unwrap(), &hex::decode(after).unwrap()).unwrap();
            assert_eq!(
                (proof.required, proof.delta, proof.peak),
                (required, delta, peak)
            );
            assert_eq!(proof.names.len(), 12);
            assert!(proof.source.contains("theorem success"));
            assert!(proof.source.contains("theorem underflow"));
            assert!(proof.source.contains("theorem overflow"));
        }
    }

    #[test]
    fn generated_windows_reject_unsupported_or_invalid_data() {
        for (before, after) in [
            ("", ""),
            ("600116600116", "610002165f50"),
            ("600116600116", "506300000000"),
            ("600116600116", "610001165f60"),
            ("600116600116", "610001fe5f50"),
            ("600116600116", "806001165050"),
            ("600116600116", "600116"),
        ] {
            assert!(
                certificate(&hex::decode(before).unwrap(), &hex::decode(after).unwrap()).is_err()
            );
        }
        assert!(certificate(&[0x5f; 65], &[0x5f; 65]).is_err());
        assert!(certificate(&[0x5f; 17], &[0x5f; 17]).is_err());
    }
}
