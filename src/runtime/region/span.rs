//! Generated canonical finite-prefix certificates.

use anyhow::{Context as _, Result, bail, ensure};
use revm::primitives::{U256, hex, keccak256};
use serde::Serialize;
use std::{fmt::Write as _, fs, path::Path};

use super::{MASK_AFTER, MASK_BEFORE, MAX_RUNTIME_BYTES, decoded_facts, decoded_operation, images};
use crate::{
    proof,
    runtime::{decode, push_value},
};

const DECODE: &str = include_str!("../../../lean/upstream/templates/SpanDecode.lean.in");
const TRACE: &str = include_str!("../../../lean/upstream/templates/SpanTrace.lean.in");
const PROOF: &str = include_str!("../../../lean/upstream/templates/SpanProof.lean.in");

/// Conditions of a finite internal prefix; surrounding execution is not certified.
#[derive(Debug, Serialize)]
pub struct SpanCertificate {
    pub claim: &'static str,
    pub original_keccak256: String,
    pub candidate_keccak256: String,
    pub entry_pc: usize,
    pub exit_pc: usize,
    pub source_instruction_count: usize,
    pub candidate_instruction_count: usize,
    pub source_gas_minimum: u64,
    pub candidate_gas_cost: u64,
    pub gas_surplus_increase: u64,
    pub required_input_stack_words: usize,
    pub maximum_input_stack_words: usize,
    pub output_stack_delta: isize,
    pub execution_count_offset_increase: usize,
    pub power_rewrites: usize,
    pub mask_rewrites: usize,
    pub interpreter_fuel: String,
    pub state_relation: &'static str,
    pub unproved: [&'static str; 5],
    pub lean_version: String,
}

#[derive(Debug)]
enum SegmentKind {
    Same { op: u8, value: U256, width: usize },
    Power { width: usize, exponent: usize },
    Mask,
}

#[derive(Debug)]
struct Segment {
    pc: usize,
    kind: SegmentKind,
}

#[derive(Debug, Default)]
struct Profile {
    required: usize,
    peak: usize,
    delta: isize,
    gas: u64,
    count: usize,
}

#[derive(Debug)]
struct Span {
    entry: usize,
    exit: usize,
    segments: Vec<Segment>,
    source: Profile,
    candidate: Profile,
    required: usize,
    maximum: usize,
    powers: usize,
    masks: usize,
}

impl Span {
    fn select(original: &[u8], candidate: &[u8], entry: usize, exit: usize) -> Result<Self> {
        ensure!(
            original.len() <= MAX_RUNTIME_BYTES && candidate.len() <= MAX_RUNTIME_BYTES,
            "runtime exceeds EIP-170 size limit"
        );
        ensure!(
            original.len() == candidate.len(),
            "span certificates require fixed layout"
        );
        ensure!(
            entry < exit && exit <= original.len(),
            "span requires entry PC < exit PC within both images"
        );
        for code in [original, candidate] {
            let instructions = decode(code);
            ensure!(
                instructions.iter().any(|i| i.pc == entry),
                "entry PC is inside a PUSH immediate"
            );
            ensure!(
                exit == code.len() || instructions.iter().any(|i| i.pc == exit),
                "exit PC is inside a PUSH immediate"
            );
        }
        let mut segments = Vec::new();
        let mut pc = entry;
        let mut powers = 0;
        let mut masks = 0;
        while pc < exit {
            let old = &original[pc..exit];
            let new = &candidate[pc..exit];
            if old.starts_with(&MASK_BEFORE) && new.starts_with(&MASK_AFTER) {
                segments.push(Segment {
                    pc,
                    kind: SegmentKind::Mask,
                });
                masks += 1;
                pc += MASK_BEFORE.len();
                continue;
            }
            let op = old[0];
            let width = if (0x60..=0x7f).contains(&op) {
                usize::from(op - 0x5f)
            } else {
                0
            };
            let bytes = old.get(..width + 1).context("truncated source PUSH")?;
            let value = if width > 0 {
                push_value(bytes).context("truncated source PUSH")?
            } else {
                U256::ZERO
            };
            if width > 0
                && value != U256::ZERO
                && value & (value - U256::from(1)) == U256::ZERO
                && old.get(width + 1) == Some(&0x02)
                && new.first() == Some(&op)
                && new.get(width + 1) == Some(&0x1b)
            {
                let exponent = value.bit_len() - 1;
                if push_value(&new[..width + 1]) == Some(U256::from(exponent)) {
                    segments.push(Segment {
                        pc,
                        kind: SegmentKind::Power { width, exponent },
                    });
                    powers += 1;
                    pc += width + 2;
                    continue;
                }
            }
            ensure!(
                matches!(op, 0x01 | 0x02 | 0x1b | 0x5f..=0x7f | 0x80 | 0x90),
                "unsupported canonical span opcode 0x{op:02x} at PC {pc}"
            );
            ensure!(
                new.get(..width + 1) == Some(bytes),
                "unsupported changed instruction at PC {pc}"
            );
            segments.push(Segment {
                pc,
                kind: SegmentKind::Same { op, value, width },
            });
            pc += width + 1;
        }
        let source = profile(&original[entry..exit])?;
        let candidate_profile = profile(&candidate[entry..exit])?;
        ensure!(
            source.delta == candidate_profile.delta,
            "span stack deltas differ"
        );
        let required = source.required.max(candidate_profile.required);
        let maximum = 1024usize
            .checked_sub(source.peak.max(candidate_profile.peak))
            .context("span exceeds stack limit")?;
        ensure!(required <= maximum, "span has no valid input stack height");
        Ok(Self {
            entry,
            exit,
            segments,
            source,
            candidate: candidate_profile,
            required,
            maximum,
            powers,
            masks,
        })
    }

    fn sources(&self, original: &[u8], candidate: &[u8]) -> [(&'static str, String); 4] {
        let facts = decoded_facts(
            &original[self.entry..self.exit],
            &candidate[self.entry..self.exit],
            self.entry,
            None,
        );
        let decode = DECODE
            .replace("$image_module", "Images")
            .replace("$namespace", "GolfCertificates.Span")
            .replace("$decoded_facts", &facts);
        [
            (
                "Images.lean",
                images(original, candidate, self.entry, self.exit - self.entry),
            ),
            ("Decode.lean", decode),
            ("SpanTrace.lean", self.proof(true, original, candidate)),
            ("RegionProof.lean", self.proof(false, original, candidate)),
        ]
    }

    fn proof(&self, generic: bool, original: &[u8], candidate: &[u8]) -> String {
        let mut decode_binders = String::new();
        let mut decode_arguments = Vec::new();
        for (side, code) in [("original", original), ("candidate", candidate)] {
            for instruction in decode(&code[self.entry..self.exit]) {
                let pc = self.entry + instruction.pc;
                let (opcode, argument) = decoded_operation(&instruction.bytes);
                let name = format!("{side}At{pc}");
                writeln!(decode_binders, "    ({name} : decode {side}Code (UInt256.ofNat {pc}) = some (({opcode} : Operation .EVM), {argument}))").unwrap();
                decode_arguments.push(name);
            }
        }
        let code_binder = if generic {
            "(originalCode : ByteArray)"
        } else {
            ""
        };
        let code_argument = if generic { "originalCode " } else { "" };
        let inputs: Vec<String> = (0..self.required).map(|i| format!("a{i}")).collect();
        let args = inputs.join(" ");
        let binders = if inputs.is_empty() {
            String::new()
        } else {
            format!("({args} : UInt256)")
        };
        let input_stack = lean_stack(&inputs);
        let mut words = inputs;
        let mut definitions = String::new();
        let mut word_index = 0usize;
        let mut gas_proof = String::from(
            " have g0 : s.gasAvailable.toNat = s.gasAvailable.toNat - 0 := by omega\n",
        );
        let mut preparations = String::new();
        let mut constructors = String::new();
        let mut spent = 0u64;
        let mut source_left = self.source.count;
        let mut candidate_left = self.candidate.count;
        let mut powers_left = self.powers;
        let mut masks_left = self.masks;
        let state = |i: usize| {
            if i == 0 {
                "s".to_owned()
            } else {
                format!("stage{i} {code_argument}s {args} tail")
            }
        };
        let final_state = state(self.segments.len());
        let stage_names = (1..=self.segments.len())
            .map(|i| format!("stage{i}"))
            .collect::<Vec<_>>()
            .join(",");
        let reductions = format!(
            "{stage_names},snapshot,finalStack,mulPowerPost,binaryPost,pushedWidth,withCode"
        );
        for (i, segment) in self.segments.iter().enumerate() {
            let prev = state(i);
            let next = state(i + 1);
            let initial_words = words.clone();
            let current_stack = lean_stack(&words);
            let (body, cost, old_steps, new_steps) = match segment.kind {
                SegmentKind::Mask => {
                    let a = words.remove(0);
                    let tail = lean_stack(&words);
                    words.insert(0, format!("(low &&& ({a}))"));
                    words.insert(0, "high".into());
                    (
                        format!("snapshot ({prev}) (finalStack ({a}) ({tail})) 18 12"),
                        36,
                        12,
                        9,
                    )
                }
                SegmentKind::Power { width, exponent } => {
                    let a = words.remove(0);
                    let tail = lean_stack(&words);
                    words.insert(
                        0,
                        format!("(UInt256.mul (UInt256.ofNat (2^{exponent})) ({a}))"),
                    );
                    (
                        format!(
                            "mulPowerPost ({prev}) originalCode {width} {exponent} ({a}) ({tail})"
                        ),
                        8,
                        2,
                        2,
                    )
                }
                SegmentKind::Same { op, value, width } => match op {
                    0x60..=0x7f => {
                        words.insert(0, format!("(UInt256.ofNat {value})"));
                        (
                            format!("pushedWidth ({prev}) (UInt256.ofNat {value}) {width}"),
                            3,
                            1,
                            1,
                        )
                    }
                    0x5f => {
                        words.insert(0, "(UInt256.ofNat 0)".into());
                        (
                            format!("binaryPost ({prev}) (UInt256.ofNat 0) ({prev}).stack 2"),
                            2,
                            1,
                            1,
                        )
                    }
                    0x80 => {
                        let a = words[0].clone();
                        words.insert(0, a.clone());
                        (
                            format!("binaryPost ({prev}) ({a}) ({current_stack}) 3"),
                            3,
                            1,
                            1,
                        )
                    }
                    0x90 => {
                        words.swap(0, 1);
                        (
                            format!(
                                "binaryPost ({prev}) ({}) ({}) 3",
                                words[0],
                                lean_stack(&words[1..])
                            ),
                            3,
                            1,
                            1,
                        )
                    }
                    _ => {
                        let a = words.remove(0);
                        let b = words.remove(0);
                        let result = match op {
                            0x01 => format!("UInt256.add ({a}) ({b})"),
                            0x02 => format!("UInt256.mul ({a}) ({b})"),
                            0x1b => format!("UInt256.shiftLeft ({b}) ({a})"),
                            _ => unreachable!(),
                        };
                        let cost = if op == 2 { 5 } else { 3 };
                        let body = format!(
                            "binaryPost ({prev}) ({result}) ({}) {cost}",
                            lean_stack(&words)
                        );
                        words.insert(0, format!("({result})"));
                        (body, cost, 1, 1)
                    }
                },
            };
            // Name computed words so DUP/ADD chains share prior expressions instead
            // of expanding their textual representation exponentially.
            for word in &mut words {
                if !initial_words.contains(word) {
                    writeln!(
                        definitions,
                        "def value{word_index} {binders} : UInt256 := {word}"
                    )
                    .unwrap();
                    *word = format!("(value{word_index} {args})");
                    word_index += 1;
                }
            }
            writeln!(definitions, "def stage{} {code_binder} (s : EVM.State) {binders} (tail : List UInt256) : EVM.State :=\n {body}", i+1).unwrap();
            spent += cost;
            writeln!(
                gas_proof,
                " have g{} : ({next}).gasAvailable.toNat = s.gasAvailable.toNat - {spent} := by",
                i + 1
            )
            .unwrap();
            match segment.kind {
                SegmentKind::Mask => writeln!(gas_proof, "  change (spend ({prev}).gasAvailable 12).toNat = _\n  rw [spend_nat _ 12 (by rw [g{i}]; omega),g{i}] <;> omega").unwrap(),
                SegmentKind::Power { .. } => writeln!(gas_proof, "  change (({prev}).gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5).toNat = _\n  have h := word_sub_toNat ({prev}).gasAvailable 3 (by decide) (by rw [g{i}]; omega)\n  rw [word_sub_toNat _ 5 (by decide) (by rw [h,g{i}]; omega),h,g{i}] <;> omega").unwrap(),
                SegmentKind::Same { .. } => writeln!(gas_proof, "  change (({prev}).gasAvailable - UInt256.ofNat {cost}).toNat = _\n  rw [word_sub_toNat _ {cost} (by decide) (by rw [g{i}]; omega),g{i}] <;> omega").unwrap(),
            }
            let pc = segment.pc;
            if i == 0 {
                writeln!(preparations, " have pc0 : s.pc = UInt256.ofNat {pc} := pc\n have stack0 : s.stack = {current_stack} := stack").unwrap();
            } else {
                let previous = i - 1;
                let local = format!(
                    "stage{i},snapshot,finalStack,mulPowerPost,binaryPost,pushedWidth,withCode"
                );
                writeln!(preparations, " have pc{i} : ({prev}).pc = UInt256.ofNat {pc} := by\n  simp only [{local},pc{previous}] <;> rfl\n have stack{i} : ({prev}).stack = {current_stack} := by\n  simp only [{local},stack{previous}] <;> rfl").unwrap();
            }
            source_left -= old_steps;
            candidate_left -= new_steps;
            match segment.kind {
                SegmentKind::Mask => {
                    masks_left -= 1;
                    for (side, typ, offsets) in [
                        (
                            "original",
                            "BeforeDecoded",
                            &[0, 2, 4, 6, 7, 8, 9, 11, 13, 15, 16, 17][..],
                        ),
                        (
                            "candidate",
                            "AfterDecoded",
                            &[0, 2, 4, 6, 7, 8, 9, 15, 17][..],
                        ),
                    ] {
                        writeln!(preparations," have {side}{i} : {typ} (withCode ({prev}) {side}Code) := by\n  constructor").unwrap();
                        for offset in offsets {
                            writeln!(
                                preparations,
                                "  · simpa only [withCode,pc{i}] using {side}At{}",
                                pc + offset
                            )
                            .unwrap();
                        }
                    }
                    writeln!(constructors," apply MixedTrace.mask ({prev}) ({final_state}) (fuel+{source_left}) (fuel+{candidate_left}) {powers_left} {masks_left} ({}) ({}) original{i} candidate{i} stack{i}\n · rw [g{i}]; omega\n · try simp only [List.length_cons]\n   omega",initial_words[0],lean_stack(&initial_words[1..])).unwrap();
                }
                SegmentKind::Power { width, exponent } => {
                    powers_left -= 1;
                    for (side, typ) in [("original", "MulPowerAt"), ("candidate", "ShiftPowerAt")] {
                        writeln!(preparations," have {side}{i} : {typ} {side}Code ({prev}).pc .PUSH{width} {width} {exponent} := by\n  constructor\n  · simpa only [pc{i}] using {side}At{pc}\n  · simpa only [pc{i}] using {side}At{}",pc+width+1).unwrap();
                    }
                    writeln!(constructors," apply MixedTrace.power ({prev}) ({final_state}) (fuel+{source_left}) (fuel+{candidate_left}) {powers_left} {masks_left} .PUSH{width} {width} {exponent} ({}) ({}) (by decide) (by decide) original{i} candidate{i} stack{i}\n · rw [g{i}]; omega\n · simp only [stack{i},List.length_cons]; omega",initial_words[0],lean_stack(&initial_words[1..])).unwrap();
                }
                SegmentKind::Same { op, value, width } => {
                    let (operation, argument, allowed, constructor, step) = if width > 0 {
                        (
                            format!("(.Push .PUSH{width})"),
                            format!("(some (UInt256.ofNat {value},{width}))"),
                            format!("(NonterminalStackOp.push .PUSH{width} (by decide))"),
                            "same",
                            format!(
                                "step_push ({prev}) .PUSH{width} (UInt256.ofNat {value}) {width} (fuel+{source_left}) 3 (by decide)"
                            ),
                        )
                    } else {
                        let (name, constructor) = match op {
                            1 => ("add", "extended"),
                            2 => ("mul", "same"),
                            0x1b => ("shl", "same"),
                            0x5f => ("push0", "extended"),
                            0x80 => ("dup1", "extended"),
                            0x90 => ("swap1", "extended"),
                            _ => unreachable!(),
                        };
                        let args = match op {
                            0x5f => String::new(),
                            0x80 => format!(
                                " ({}) ({}) stack{i}",
                                initial_words[0],
                                lean_stack(&initial_words[1..])
                            ),
                            _ => format!(
                                " ({}) ({}) ({}) stack{i}",
                                initial_words[1],
                                initial_words[0],
                                lean_stack(&initial_words[2..])
                            ),
                        };
                        (
                            format!(".{}", name.to_uppercase()),
                            "none".into(),
                            format!(".{name}"),
                            constructor,
                            format!("step_{name} ({prev}) (fuel+{source_left}) {cost} none{args}"),
                        )
                    };
                    for side in ["original", "candidate"] {
                        writeln!(preparations," have {side}{i} : decode {side}Code ({prev}).pc = some ({operation},{argument}) := by\n  simpa only [pc{i}] using {side}At{pc}").unwrap();
                    }
                    let (need, outputs) = match op {
                        0x5f..=0x7f => (0, 1),
                        0x80 => (1, 2),
                        0x90 => (2, 2),
                        _ => (2, 1),
                    };
                    writeln!(preparations," have bounds{i} : FullXBounds ({prev}) {operation} := by\n  constructor\n  · change {cost} ≤ ({prev}).gasAvailable.toNat\n    rw [g{i}]; omega\n  · change {need} ≤ ({prev}).stack.length\n    simp only [stack{i},List.length_cons]; omega\n  · change ({prev}).stack.length - {need} + {outputs} ≤ 1024\n    simp only [stack{i},List.length_cons]; omega\n have step{i} : EVM.step ((fuel+{source_left})+1) (C' ({prev}) {operation}) (some ({operation},{argument})) ({prev}) = .ok ({next}) := by\n  change EVM.step ((fuel+{source_left})+1) {cost} (some ({operation},{argument})) ({prev}) = .ok ({next})\n  exact {step}").unwrap();
                    writeln!(constructors," apply MixedTrace.{constructor} ({prev}) ({next}) ({final_state}) (fuel+{source_left}) (fuel+{candidate_left}) {powers_left} {masks_left} {operation} {argument} {allowed} original{i} candidate{i} bounds{i} step{i}").unwrap();
                }
            }
        }
        constructors.push_str(" exact MixedTrace.done _\n");
        let trace = format!("{gas_proof}{preparations}{constructors}");
        let replacements = [
            ("$namespace", "GolfCertificates.Span".into()),
            ("$trace_module", "SpanTrace".into()),
            ("$decode_binders", decode_binders),
            ("$decode_arguments", decode_arguments.join(" ")),
            ("$decode_module", "Decode".into()),
            ("$input_binders", binders),
            ("$input_arguments", args),
            ("$input_stack", input_stack),
            ("$entry_pc", self.entry.to_string()),
            ("$exit_pc", self.exit.to_string()),
            ("$source_steps", self.source.count.to_string()),
            ("$candidate_steps", self.candidate.count.to_string()),
            ("$source_gas", self.source.gas.to_string()),
            ("$maximum_tail", (self.maximum - self.required).to_string()),
            ("$powers", self.powers.to_string()),
            ("$masks", self.masks.to_string()),
            ("$source_final", final_state),
            ("$output_stack", lean_stack(&words)),
            ("$state_definitions", definitions),
            (
                "$gas_proof",
                format!("{gas_proof} exact g{}", self.segments.len()),
            ),
            ("$trace_proof", trace),
            (
                "$stack_proof",
                format!(" simp only [{reductions},stack] <;> rfl"),
            ),
            (
                "$count_proof",
                format!(" simp only [{reductions}] <;> omega"),
            ),
            ("$pc_proof", format!(" simp only [{reductions},pc] <;> rfl")),
        ];
        let mut proof = if generic { TRACE } else { PROOF }.to_owned();
        for (key, value) in replacements {
            proof = proof.replace(key, &value);
        }
        proof
    }
}

/// Certify a selected straight-line prefix with generated canonical EVM proofs.
/// The exclusive exit PC is a boundary, not an executed instruction.
pub fn certify_span(
    original: &[u8],
    candidate: &[u8],
    entry_pc: usize,
    exit_pc: usize,
    out: &Path,
) -> Result<SpanCertificate> {
    let span = Span::select(original, candidate, entry_pc, exit_pc)?;
    fs::create_dir(out)
        .with_context(|| format!("use a new output directory: {}", out.display()))?;
    fs::write(out.join("original.hex"), hex::encode(original) + "\n")?;
    fs::write(out.join("candidate.hex"), hex::encode(candidate) + "\n")?;
    for (name, source) in span.sources(original, candidate) {
        fs::write(out.join(name), source)?;
    }
    let lean_version = proof::verify_region(out, proof::RegionKind::Span)?;
    let report = SpanCertificate {
        claim: "conditional internal-span residual interpreter calls",
        original_keccak256: keccak256(original).to_string(),
        candidate_keccak256: keccak256(candidate).to_string(),
        entry_pc,
        exit_pc,
        source_instruction_count: span.source.count,
        candidate_instruction_count: span.candidate.count,
        source_gas_minimum: span.source.gas,
        candidate_gas_cost: span.candidate.gas,
        gas_surplus_increase: span.source.gas - span.candidate.gas,
        required_input_stack_words: span.required,
        maximum_input_stack_words: span.maximum,
        output_stack_delta: span.source.delta,
        execution_count_offset_increase: span.source.count - span.candidate.count,
        power_rewrites: span.powers,
        mask_rewrites: span.masks,
        interpreter_fuel: format!(
            "for every natural fuel, source X(fuel+{}) and candidate X(fuel+{}) reduce to their own X(fuel+1) at the exit",
            span.source.count + 1,
            span.candidate.count + 1
        ),
        state_relation: "arbitrary nonnegative incoming gas surplus and execution-count offset; related current/original account maps differing only in designated deployed code; both execution-code links; all other frame fields preserved",
        unproved: [
            "entry reachability",
            "suffix outcomes",
            "whole-contract and all-gas equivalence",
            "canonical transaction entry",
            "revm correspondence",
        ],
        lean_version,
    };
    fs::write(
        out.join("result.json"),
        serde_json::to_string_pretty(&report)? + "\n",
    )?;
    Ok(report)
}

fn lean_stack(words: &[String]) -> String {
    words.iter().rev().fold("tail".to_owned(), |tail, word| {
        format!("({word}) :: {tail}")
    })
}

fn profile(code: &[u8]) -> Result<Profile> {
    let mut result = Profile::default();
    for instruction in decode(code) {
        let op = instruction.bytes[0];
        let (need, delta, cost) = match op {
            0x5f..=0x7f => {
                ensure!(push_value(&instruction.bytes).is_some(), "truncated PUSH");
                (0, 1, if op == 0x5f { 2 } else { 3 })
            }
            1 | 3 | 0x16 | 0x1b => (2, -1, 3),
            2 => (2, -1, 5),
            0x19 => (1, 0, 3),
            0x80 => (1, 1, 3),
            0x90 => (2, 0, 3),
            _ => bail!("unsupported canonical span opcode 0x{op:02x}"),
        };
        result.required = result.required.max((need - result.delta).max(0) as usize);
        result.delta += delta;
        result.peak = result.peak.max(result.delta.max(0) as usize);
        result.gas += cost;
        result.count += 1;
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mixed_profiles_include_both_orders_and_repeated_growth() {
        let power = [0x60, 0x20, 2];
        let shifted = [0x60, 5, 0x1b];
        for (before, after) in [
            (
                [MASK_BEFORE.as_slice(), &power].concat(),
                [MASK_AFTER.as_slice(), &shifted].concat(),
            ),
            (
                [power.as_slice(), &MASK_BEFORE].concat(),
                [shifted.as_slice(), &MASK_AFTER].concat(),
            ),
        ] {
            let span = Span::select(&before, &after, 0, 21).unwrap();
            assert_eq!(
                (
                    span.source.gas,
                    span.candidate.gas,
                    span.source.count,
                    span.candidate.count
                ),
                (44, 33, 14, 11)
            );
            assert_eq!(
                (span.required, span.maximum, span.source.delta),
                (1, 1021, 1)
            );
            let repeated = Span::select(&before.repeat(2), &after.repeat(2), 0, 42).unwrap();
            assert_eq!(
                (
                    repeated.source.gas,
                    repeated.candidate.gas,
                    repeated.required,
                    repeated.maximum
                ),
                (88, 66, 1, 1020)
            );
        }
    }

    #[test]
    fn unchanged_profiles_cover_zero_inputs_and_stack_shrink() {
        let push = [0x60, 1, 0x60, 2, 1];
        let span = Span::select(&push, &push, 0, push.len()).unwrap();
        assert_eq!(
            (
                span.required,
                span.maximum,
                span.source.delta,
                span.source.gas
            ),
            (0, 1022, 1, 9)
        );
        let shrink = [2, 0x1b, 1];
        let span = Span::select(&shrink, &shrink, 0, shrink.len()).unwrap();
        assert_eq!(
            (
                span.required,
                span.maximum,
                span.source.delta,
                span.source.gas
            ),
            (4, 1024, -3, 11)
        );
    }

    #[test]
    fn selection_rejects_partial_or_unsupported_spans() {
        for (old, new, start, end) in [
            (&[0x60, 1, 0][..], &[0x60, 1, 0][..], 1, 2),
            (&[0x60, 1, 0], &[0x60, 1, 0], 0, 1),
            (&[0x61, 1], &[0x61, 1], 0, 2),
            (&[0x5a], &[0x5a], 0, 1),
            (&[0x60, 1], &[0x60, 2], 0, 2),
            (&[0x5f, 0x60, 1], &[0x60, 0, 1], 1, 3),
        ] {
            assert!(Span::select(old, new, start, end).is_err());
        }
        assert!(Span::select(&vec![0x5f; 1025], &vec![0x5f; 1025], 0, 1025).is_err());
    }

    #[test]
    fn repeated_dup_add_does_not_expand_symbolic_values_exponentially() {
        let render = |count| {
            let bytes = [0x80, 0x01].repeat(count);
            Span::select(&bytes, &bytes, 0, bytes.len())
                .unwrap()
                .proof(true, &bytes, &bytes)
        };
        let small = render(32);
        let large = render(64);
        // Doubling the trace must preserve linear-size text, including stack/PC proofs.
        assert!(large.len() < small.len() * 3);
    }

    #[test]
    fn wide_power_and_zero_exponent_preserve_immediates() {
        let mut old = vec![0x7f, 0x80];
        old.extend([0; 31]);
        old.push(2);
        let mut new = vec![0x7f];
        new.extend([0; 31]);
        new.extend([255, 0x1b]);
        let span = Span::select(&old, &new, 0, 34).unwrap();
        assert_eq!(span.powers, 1);
        let sources = span.sources(&old, &new);
        assert!(sources[1].1.contains("PUSH32"));
        assert!(
            sources[1]
                .1
                .contains(&U256::from_be_slice(&old[1..33]).to_string())
        );
        assert_eq!(
            Span::select(&[0x60, 1, 2], &[0x60, 0, 0x1b], 0, 3)
                .unwrap()
                .powers,
            1
        );
    }
}
