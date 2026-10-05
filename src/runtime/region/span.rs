//! Generated canonical finite-prefix certificates.

use anyhow::{Context as _, Result, bail, ensure};
use revm::primitives::{U256, hex, keccak256};
use serde::Serialize;
use std::{fmt::Write as _, fs, path::Path};

use super::{
    ImageRoutes, MASK_AFTER, MASK_BEFORE, MAX_RUNTIME_BYTES, RenderedImages, decoded_operation,
    render_images, routed_decoded_facts,
};
use crate::{
    proof,
    runtime::{decode, push_value},
};

mod memory;
pub use memory::{
    MemorySpanCertificate, MemorySpanJumpCertificate, SelectedSpanCertificate,
    SelectedSpanJumpCertificate, TerminalCertificate, certify_selected_span,
    certify_selected_span_from_call_entry, certify_selected_span_through_halt,
    certify_selected_span_through_jump,
};

// Canonical instruction count bounds per-leaf proof work; rewrite atoms stay whole.
// Local mixed/swap checks fit the existing module cap at this representation size.
const CHUNK_INSTRUCTIONS: usize = 32;

const DECODE: &str = include_str!("../../../lean/upstream/templates/SpanDecode.lean.in");

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

/// A selected prefix followed by its literal-destination JUMP under the checked scanner.
#[derive(Debug, Serialize)]
pub struct SpanJumpCertificate {
    #[serde(flatten)]
    pub span: SpanCertificate,
    pub jump_pc: usize,
    pub pushed_destination: usize,
    pub scanner_scope: &'static str,
}

#[derive(Clone, Debug)]
enum SegmentKind {
    Same { op: u8, value: U256, width: usize },
    Power { width: usize, exponent: usize },
    Mask,
}

#[derive(Clone, Debug)]
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
                matches!(
                    op,
                    0x01 | 0x02 | 0x03 | 0x10 | 0x15 | 0x16 | 0x17 | 0x19 | 0x1b | 0x5f..=0x7f | 0x80 | 0x90..=0x9f
                ),
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

    fn chunks(&self, original: &[u8], candidate: &[u8], budget: usize) -> Result<Vec<Self>> {
        ensure!(budget > 0, "empty chunk representation budget");
        let mut chunks = Vec::new();
        let mut ranges = Vec::new();
        let mut first = 0;
        let mut instructions = 0;
        for (index, segment) in self.segments.iter().enumerate() {
            let count = match segment.kind {
                SegmentKind::Mask => 12,
                SegmentKind::Power { .. } => 2,
                SegmentKind::Same { .. } => 1,
            };
            if instructions + count > budget && index > first {
                ranges.push((first, index));
                first = index;
                instructions = 0;
            }
            instructions += count;
        }
        ranges.push((first, self.segments.len()));
        for (first, end_index) in ranges {
            let segments = &self.segments[first..end_index];
            let entry = segments[0].pc;
            let exit = self
                .segments
                .get(end_index)
                .map_or(self.exit, |next| next.pc);
            let source = profile(&original[entry..exit])?;
            let candidate_profile = profile(&candidate[entry..exit])?;
            let required = source.required.max(candidate_profile.required);
            let maximum = 1024 - source.peak.max(candidate_profile.peak);
            chunks.push(Self {
                entry,
                exit,
                required,
                maximum,
                powers: segments
                    .iter()
                    .filter(|segment| matches!(segment.kind, SegmentKind::Power { .. }))
                    .count(),
                masks: segments
                    .iter()
                    .filter(|segment| matches!(segment.kind, SegmentKind::Mask))
                    .count(),
                segments: segments.to_vec(),
                source,
                candidate: candidate_profile,
            });
        }
        Ok(chunks)
    }

    fn leaf_sources(
        &self,
        original: &[u8],
        candidate: &[u8],
        index: usize,
        image_leaves: &[super::ImageLeaf],
    ) -> Vec<(String, String)> {
        let mut sources = Vec::new();
        let entry = self.entry;
        let exit = self.exit;
        sources.push((
            format!("TraceLeaf{index}.lean"),
            self.render_proof(original, candidate, index),
        ));
        let mut facts = routed_decoded_facts(original, candidate, entry, exit, image_leaves);
        for (side, code) in [("original", original), ("candidate", candidate)] {
            let names = decode(&code[entry..exit])
                .iter()
                .map(|instruction| format!("{side}At{}", entry + instruction.pc))
                .collect::<Vec<_>>();
            let proof = if names.len() == 1 {
                names[0].clone()
            } else {
                format!("⟨{}⟩", names.join(", "))
            };
            let typ = if side == "original" {
                "Original"
            } else {
                "Candidate"
            };
            writeln!(facts,"theorem {side}Decoded : GolfSpanTrace{index}.{typ}Decoded {side}Code := {proof}\n#print axioms {side}Decoded").unwrap();
        }
        let decoded = format!(
            "import TraceLeaf{index}\nimport OpcodeDecode\n{}",
            DECODE
                .replace("$image_module", "Images")
                .replace("$namespace", &format!("GolfSpanDecode{index}"))
                .replace("$decoded_facts", &facts)
        );
        sources.push((format!("DecodeLeaf{index}.lean"), decoded));
        let bound = include_str!("../../../lean/upstream/templates/ChunkBind.lean.in")
            .replace("$decode_module", &format!("DecodeLeaf{index}"))
            .replace("$namespace", &format!("GolfSpanBind{index}"))
            .replace("$trace_namespace", &format!("GolfSpanTrace{index}"))
            .replace("$decode_namespace", &format!("GolfSpanDecode{index}"));
        sources.push((format!("BindLeaf{index}.lean"), bound));
        sources
    }

    fn chunk_sources(
        &self,
        original: &[u8],
        candidate: &[u8],
        budget: usize,
        rendered: RenderedImages,
    ) -> Result<(proof::SpanPlan, Vec<(String, String)>)> {
        let mut sources = vec![("Images.lean".to_owned(), rendered.source)];
        let mut leaves = Vec::new();
        for (index, leaf) in self
            .chunks(original, candidate, budget)?
            .into_iter()
            .enumerate()
        {
            sources.extend(leaf.leaf_sources(original, candidate, index, &rendered.leaves));
            leaves.push(proof::SpanNode::Leaf(index));
        }
        let mut plan = proof::SpanPlan {
            leaf_count: leaves.len(),
            compositions: Vec::new(),
        };
        while leaves.len() > 1 {
            let mut parents = Vec::new();
            for pair in leaves.chunks(2) {
                if pair.len() == 1 {
                    parents.push(pair[0]);
                    continue;
                }
                let index = plan.compositions.len();
                plan.compositions.push((pair[0], pair[1]));
                let (left_module, left_summary) = chunk_node(pair[0]);
                let (right_module, right_summary) = chunk_node(pair[1]);
                let parent = include_str!("../../../lean/upstream/templates/ChunkCompose.lean.in")
                    .replace("$namespace", &format!("GolfSpanCompose{index}"))
                    .replace("$left_module", &left_module)
                    .replace("$right_module", &right_module)
                    .replace("$left_summary", &left_summary)
                    .replace("$right_summary", &right_summary);
                sources.push((format!("Compose{index}.lean"), parent));
                parents.push(proof::SpanNode::Compose(index));
            }
            leaves = parents;
        }
        let (module, summary) = chunk_node(leaves[0]);
        let mut root = include_str!("../../../lean/upstream/templates/ChunkProof.lean.in")
            .replace("$root_module", &module)
            .replace("$root_summary", &summary);
        for (key, value) in [
            ("$entry_pc", self.entry),
            ("$exit_pc", self.exit),
            ("$source_steps", self.source.count),
            ("$candidate_steps", self.candidate.count),
            ("$source_gas", self.source.gas as usize),
            ("$required", self.required),
            ("$maximum", self.maximum),
            ("$powers", self.powers),
            ("$masks", self.masks),
        ] {
            root = root.replace(key, &value.to_string());
        }
        sources.push(("RegionProof.lean".to_owned(), root));
        Ok((plan, sources))
    }

    fn render_proof(&self, original: &[u8], candidate: &[u8], index: usize) -> String {
        let mut bundled_types = Vec::new();
        let mut destructure = String::new();
        for (side, code) in [("original", original), ("candidate", candidate)] {
            let mut types = Vec::new();
            let mut names = Vec::new();
            for instruction in decode(&code[self.entry..self.exit]) {
                let pc = self.entry + instruction.pc;
                let (opcode, argument) = decoded_operation(&instruction.bytes);
                let name = format!("{side}At{pc}");
                types.push(format!("decode {side}Code (UInt256.ofNat {pc}) = some (({opcode} : Operation .EVM), {argument})"));
                names.push(name.clone());
            }
            bundled_types.push(types.join(" ∧ "));
            if names.len() == 1 {
                writeln!(destructure, " have {} := {side}Decoded", names[0]).unwrap();
            } else {
                writeln!(
                    destructure,
                    " rcases {side}Decoded with ⟨{}⟩",
                    names.join(", ")
                )
                .unwrap();
            }
        }
        let code_binder = "(originalCode : ByteArray)";
        let code_argument = "originalCode ";
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
                    0x90..=0x9f => {
                        words.swap(0, usize::from(op - 0x8f));
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
                    0x15 | 0x19 => {
                        let a = words.remove(0);
                        let operation = if op == 0x15 { "isZero" } else { "lnot" };
                        let result = format!("UInt256.{operation} ({a})");
                        let body =
                            format!("binaryPost ({prev}) ({result}) ({}) 3", lean_stack(&words));
                        words.insert(0, format!("({result})"));
                        (body, 3, 1, 1)
                    }
                    _ => {
                        let a = words.remove(0);
                        let b = words.remove(0);
                        let result = match op {
                            0x01 => format!("UInt256.add ({a}) ({b})"),
                            0x02 => format!("UInt256.mul ({a}) ({b})"),
                            0x03 => format!("UInt256.sub ({a}) ({b})"),
                            0x10 => format!("UInt256.lt ({a}) ({b})"),
                            0x16 => format!("({a}) &&& ({b})"),
                            0x17 => format!("({a}) ||| ({b})"),
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
            let previous_spent = spent;
            let total_gas = self.source.gas;
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
                SegmentKind::Same { .. } => writeln!(gas_proof, "  change (({prev}).gasAvailable - UInt256.ofNat {cost}).toNat = _\n  exact GolfPureBounds.remaining_sub s.gasAvailable ({prev}).gasAvailable {previous_spent} {cost} {total_gas} (by decide) (by decide) gas g{i}").unwrap(),
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
            if matches!(segment.kind, SegmentKind::Mask) {
                masks_left -= 1;
            }
            if matches!(segment.kind, SegmentKind::Power { .. }) {
                powers_left -= 1;
            }
            let source_fuel = format!("sourceTail+{source_left}");
            let target_fuel = format!("targetTail+{candidate_left}");
            let powers = format!("(suffixPowers+{powers_left})");
            let masks = format!("(suffixMasks+{masks_left})");
            let trace_final = "final";
            match segment.kind {
                SegmentKind::Mask => {
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
                    writeln!(constructors," apply MixedTrace.mask ({prev}) {trace_final} ({source_fuel}) ({target_fuel}) {powers} {masks} ({}) ({}) original{i} candidate{i} stack{i}\n · rw [g{i}]; omega\n · try simp only [List.length_cons]\n   omega",initial_words[0],lean_stack(&initial_words[1..])).unwrap();
                }
                SegmentKind::Power { width, exponent } => {
                    for (side, typ) in [("original", "MulPowerAt"), ("candidate", "ShiftPowerAt")] {
                        writeln!(preparations," have {side}{i} : {typ} {side}Code ({prev}).pc .PUSH{width} {width} {exponent} := by\n  constructor\n  · simpa only [pc{i}] using {side}At{pc}\n  · simpa only [pc{i}] using {side}At{}",pc+width+1).unwrap();
                    }
                    writeln!(constructors," apply MixedTrace.power ({prev}) {trace_final} ({source_fuel}) ({target_fuel}) {powers} {masks} .PUSH{width} {width} {exponent} ({}) ({}) (by decide) (by decide) original{i} candidate{i} stack{i}\n · rw [g{i}]; omega\n · simp only [stack{i},List.length_cons]; omega",initial_words[0],lean_stack(&initial_words[1..])).unwrap();
                }
                SegmentKind::Same { op, value, width } => {
                    let (operation, argument, allowed, constructor, step) = if width > 0 {
                        (
                            format!("(.Push .PUSH{width})"),
                            format!("(some (UInt256.ofNat {value},{width}))"),
                            format!("(NonterminalStackOp.push .PUSH{width} (by decide))"),
                            "same",
                            format!(
                                "GolfPureBounds.canonical_step_push ({prev}) .PUSH{width} (UInt256.ofNat {value}) {width} ({source_fuel}) (by decide)"
                            ),
                        )
                    } else if (0x91..=0x9f).contains(&op) {
                        let depth = usize::from(op - 0x8f);
                        let middle = initial_words[1..depth].join(", ");
                        (
                            format!(".SWAP{depth}"),
                            "none".into(),
                            format!("(CanonicalMaskWindow.ExtraOp.exchange .SWAP{depth})"),
                            "extra",
                            format!(
                                "GolfPureBounds.canonical_step_exchange ({prev}) .SWAP{depth} ({source_fuel}) none ({}) ({}) [{middle}] ({}) (by rfl) stack{i}",
                                initial_words[0],
                                initial_words[depth],
                                lean_stack(&initial_words[depth + 1..])
                            ),
                        )
                    } else {
                        let (name, constructor) = match op {
                            1 => ("add", "extended"),
                            2 => ("mul", "same"),
                            3 => ("sub", "extra"),
                            0x10 => ("lt", "extra"),
                            0x15 => ("iszero", "extra"),
                            0x16 => ("and", "extra"),
                            0x17 => ("or", "extra"),
                            0x19 => ("not", "extra"),
                            0x1b => ("shl", "same"),
                            0x5f => ("push0", "extended"),
                            0x80 => ("dup1", "extended"),
                            0x90 => ("swap1", "extended"),
                            _ => unreachable!(),
                        };
                        let args = match op {
                            0x5f => String::new(),
                            0x15 | 0x19 | 0x80 => format!(
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
                            if op == 0x17 {
                                ".bor".into()
                            } else {
                                format!(".{name}")
                            },
                            constructor,
                            format!(
                                "GolfPureBounds.canonical_step_{name} ({prev}) ({source_fuel}) none{args}"
                            ),
                        )
                    };
                    for side in ["original", "candidate"] {
                        writeln!(preparations," have {side}{i} : decode {side}Code ({prev}).pc = some ({operation},{argument}) := by\n  simpa only [pc{i}] using {side}At{pc}").unwrap();
                    }
                    let bounds = if width > 0 {
                        format!("GolfPureBounds.bounds_push ({prev}) .PUSH{width} (by decide)")
                    } else if (0x91..=0x9f).contains(&op) {
                        format!("GolfSwapFamily.bounds ({prev}) .SWAP{}", op - 0x8f)
                    } else {
                        let name = match op {
                            0x5f => "push0",
                            0x80 => "dup1",
                            0x90 => "swap1",
                            1 => "add",
                            2 => "mul",
                            3 => "sub",
                            0x10 => "lt",
                            0x15 => "iszero",
                            0x16 => "and",
                            0x17 => "or",
                            0x19 => "not",
                            0x1b => "shl",
                            _ => unreachable!(),
                        };
                        format!("GolfPureBounds.bounds_{name} ({prev})")
                    };
                    let input_bound = if (0x91..=0x9f).contains(&op) {
                        format!(
                            "change {} ≤ ({prev}).stack.length; ",
                            usize::from(op - 0x8f) + 1
                        )
                    } else {
                        String::new()
                    };
                    writeln!(preparations, " have bounds{i} : FullXBounds ({prev}) {operation} := {bounds}\n  (GolfPureBounds.remaining_enough _ _ {previous_spent} {cost} {total_gas} (by decide) gas g{i})\n  (by {input_bound}simp only [stack{i},List.length_cons]; omega)\n  (by simp only [stack{i},List.length_cons]; omega)\n have step{i} : EVM.step (({source_fuel})+1) (C' ({prev}) {operation}) (some ({operation},{argument})) ({prev}) = .ok ({next}) := {step}").unwrap();
                    writeln!(constructors," apply MixedTrace.{constructor} ({prev}) ({next}) {trace_final} ({source_fuel}) ({target_fuel}) {powers} {masks} {operation} {argument} {allowed} original{i} candidate{i} bounds{i} step{i}").unwrap();
                }
            }
        }
        constructors.push_str(" simpa only [Nat.add_zero, Nat.zero_add] using rest\n");
        let trace = format!(
            " intro residual sourceTail targetTail suffixPowers suffixMasks final rest\n simp only [Nat.add_comm {} suffixPowers, Nat.add_comm {} suffixMasks]\n{gas_proof}{preparations}{constructors}",
            self.powers, self.masks
        );
        let projections = |base: &str| {
            (0..self.required)
                .map(|i| format!("(({base}[{i}]?).getD (UInt256.ofNat 0))"))
                .collect::<Vec<_>>()
                .join(" ")
        };
        let projected_final = format!(
            "stage{} originalCode s {} (s.stack.drop {})",
            self.segments.len(),
            projections("s.stack"),
            self.required
        );
        let projected_output =
            lean_stack(&words).replace("tail", &format!("(xs.drop {})", self.required));
        let mut projected_output = projected_output;
        for i in (0..self.required).rev() {
            projected_output = projected_output.replace(
                &format!("a{i}"),
                &format!("((xs[{i}]?).getD (UInt256.ofNat 0))"),
            );
        }
        let mut summary_cases = format!(
            "    generalize stackShape : s.stack = {} at low high\n",
            if self.required == 0 { "tail" } else { "xs" }
        );
        let mut indent = String::from("    ");
        for i in 0..self.required {
            let next = if i + 1 == self.required { "tail" } else { "xs" };
            writeln!(summary_cases, "{indent}cases xs with\n{indent}| nil => simp only [List.length_nil, List.length_cons] at low; omega\n{indent}| cons a{i} {next} =>").unwrap();
            indent.push_str("  ");
        }
        let height_proof = if self.required == 0 {
            "exact high"
        } else {
            "simp only [List.length_cons] at high; omega"
        };
        writeln!(summary_cases, "{indent}have stack : s.stack = {input_stack} := stackShape\n{indent}have height : tail.length ≤ {} := by {height_proof}\n{indent}rw [post_on_stack originalCode candidateCode s {args} tail stack]\n{indent}exact valid_trace originalCode candidateCode originalDecoded candidateDecoded s {args} tail pc stack gas height", self.maximum-self.required).unwrap();
        let replacements = [
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
        let mut proof =
            include_str!("../../../lean/upstream/templates/ChunkTrace.lean.in").to_owned();
        proof = proof.replace("$maximum_tail", &(self.maximum - self.required).to_string());
        {
            let projection_arguments = projections("s.stack");
            for (key, value) in [
                ("$namespace", format!("GolfSpanTrace{index}")),
                ("$original_decoded_type", bundled_types[0].clone()),
                ("$candidate_decoded_type", bundled_types[1].clone()),
                ("$decode_destructure", destructure),
                ("$projection_arguments", projection_arguments),
                ("$projected_final", projected_final),
                ("$projected_output", projected_output),
                ("$summary_cases", summary_cases),
                ("$required", self.required.to_string()),
                ("$maximum", self.maximum.to_string()),
                (
                    "$produced",
                    (self.required as isize + self.source.delta).to_string(),
                ),
            ] {
                proof = proof.replace(key, &value);
            }
        }
        for (key, value) in replacements {
            proof = proof.replace(key, &value);
        }
        proof
    }
}

fn chunk_node(node: proof::SpanNode) -> (String, String) {
    match node {
        proof::SpanNode::Leaf(index) => (
            format!("BindLeaf{index}"),
            format!("GolfSpanBind{index}.summary"),
        ),
        proof::SpanNode::Compose(index) => (
            format!("Compose{index}"),
            format!("GolfSpanCompose{index}.summary"),
        ),
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
    let rendered = render_images(
        original,
        candidate,
        entry_pc,
        exit_pc - entry_pc,
        ImageRoutes::Window,
    );
    let (plan, sources) = span.chunk_sources(original, candidate, CHUNK_INSTRUCTIONS, rendered)?;
    for (name, source) in sources {
        fs::write(out.join(name), source)?;
    }
    let lean_version = proof::verify_region(out, proof::RegionKind::ChunkedSpan(&plan))?;
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

/// Execute a supported span and its immediately following literal-destination JUMP.
/// `exit_pc` identifies JUMP; the destination instruction is not executed.
pub fn certify_span_through_jump(
    original: &[u8],
    candidate: &[u8],
    entry_pc: usize,
    exit_pc: usize,
    out: &Path,
) -> Result<SpanJumpCertificate> {
    let span = Span::select(original, candidate, entry_pc, exit_pc)?;
    ensure!(
        original.get(exit_pc) == Some(&0x56) && candidate.get(exit_pc) == Some(&0x56),
        "span exit must be JUMP in both images"
    );
    let destination = match span.segments.last().map(|segment| &segment.kind) {
        Some(SegmentKind::Same {
            op: 0x5f..=0x7f,
            value,
            ..
        }) => *value,
        _ => bail!("through-jump span must end in an unchanged literal PUSH0..32"),
    };
    ensure!(
        destination < U256::from(original.len()),
        "jump destination is outside the full images"
    );
    let destination = destination.to::<usize>();
    let rendered = render_images(
        original,
        candidate,
        entry_pc,
        exit_pc - entry_pc,
        ImageRoutes::All,
    );
    // This checks the complete PUSH-aware destination boundary in both full images.
    let membership = super::jump::membership_sources(original, candidate, destination, &rendered)?;
    let jump_decodes =
        routed_decoded_facts(original, candidate, exit_pc, exit_pc + 1, &rendered.leaves)
            .replace("GolfOpcodeDecode.decode_jump", "jump_decode");
    let (plan, mut sources) =
        span.chunk_sources(original, candidate, CHUNK_INSTRUCTIONS, rendered)?;
    let root_node = plan
        .compositions
        .len()
        .checked_sub(1)
        .map_or(proof::SpanNode::Leaf(0), proof::SpanNode::Compose);
    let (_, summary) = chunk_node(root_node);
    let mut terminal = include_str!("../../../lean/upstream/templates/SpanJump.lean.in")
        .replace("$root_summary", &summary)
        .replace("$jump_decodes", &jump_decodes);
    for (key, value) in [
        ("$entry_pc", entry_pc),
        ("$jump_pc", exit_pc),
        ("$destination", destination),
        ("$source_steps", span.source.count),
        ("$target_steps", span.candidate.count),
        ("$total_gas", (span.source.gas + 8) as usize),
        ("$required", span.required),
        ("$maximum", span.maximum),
        ("$powers", span.powers),
        ("$masks", span.masks),
    ] {
        terminal = terminal.replace(key, &value.to_string());
    }
    let mut jump_plan = proof::JumpPlan {
        modules: membership
            .iter()
            .map(|(name, _, roots)| (name.clone(), roots.clone()))
            .collect(),
    };
    jump_plan.modules.push((
        "SpanJumpProof".to_owned(),
        vec![
            "GolfCertificates.SpanJump.source_count".to_owned(),
            "GolfCertificates.SpanJump.source_gas".to_owned(),
            "GolfCertificates.SpanJump.span_jump_boundary".to_owned(),
        ],
    ));
    sources.extend(
        membership
            .into_iter()
            .map(|(name, source, _)| (format!("{name}.lean"), source)),
    );
    sources.push(("SpanJumpProof.lean".to_owned(), terminal));
    proof::check_jump_output(out)?;
    if let Some(parent) = out.parent().filter(|path| !path.as_os_str().is_empty()) {
        fs::create_dir_all(parent)?;
    }
    fs::create_dir(out)
        .with_context(|| format!("use a new output directory: {}", out.display()))?;
    fs::write(out.join("original.hex"), hex::encode(original) + "\n")?;
    fs::write(out.join("candidate.hex"), hex::encode(candidate) + "\n")?;
    for (name, source) in sources {
        fs::write(out.join(name), source)?;
    }
    let lean_version = proof::verify_region(out, proof::RegionKind::SpanJump(&plan, &jump_plan))?;
    let report = SpanJumpCertificate {
        jump_pc: exit_pc,
        pushed_destination: destination,
        scanner_scope: "checked-scanner semantics; equivalence with the original opaque upstream scanner is unproved",
        span: SpanCertificate {
            claim: "conditional checked-scanner internal span through JUMP",
            original_keccak256: keccak256(original).to_string(),
            candidate_keccak256: keccak256(candidate).to_string(),
            entry_pc,
            exit_pc: destination,
            source_instruction_count: span.source.count + 1,
            candidate_instruction_count: span.candidate.count + 1,
            source_gas_minimum: span.source.gas + 8,
            candidate_gas_cost: span.candidate.gas + 8,
            gas_surplus_increase: span.source.gas - span.candidate.gas,
            required_input_stack_words: span.required,
            maximum_input_stack_words: span.maximum,
            output_stack_delta: span.source.delta - 1,
            execution_count_offset_increase: span.source.count - span.candidate.count,
            power_rewrites: span.powers,
            mask_rewrites: span.masks,
            interpreter_fuel: format!(
                "for every natural fuel, source X(fuel+{}) and candidate X(fuel+{}) reduce to their own X(fuel+1) at the landing PC; its JUMPDEST is not executed",
                span.source.count + 2,
                span.candidate.count + 2
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
        },
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
            1 | 3 | 0x10 | 0x16 | 0x17 | 0x1b => (2, -1, 3),
            2 => (2, -1, 5),
            0x52 => (2, -2, 3),
            0x15 | 0x19 => (1, 0, 3),
            0x80 => (1, 1, 3),
            0x90..=0x9f => (isize::from(op - 0x8f) + 1, 0, 3),
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
    fn every_swap_depth_preserves_full_symbolic_stack_and_tail() {
        for depth in 1u8..=16 {
            let code = [0x8f + depth];
            let span = Span::select(&code, &code, 0, 1).unwrap();
            assert_eq!(span.required, usize::from(depth) + 1);
            assert_eq!(span.maximum, 1024);
            assert_eq!(
                (span.source.delta, span.source.peak, span.source.gas),
                (0, 0, 3)
            );
            let source = span.render_proof(&code, &code, 0);
            // Endpoint permutation oracle: every intervening word remains in order.
            let indices = std::iter::once(depth)
                .chain(1..depth)
                .chain(std::iter::once(0));
            let expected = indices
                .map(|index| format!("(a{index}) :: "))
                .collect::<String>()
                + "tail";
            let stack_theorem = source
                .split("theorem source_stack")
                .nth(1)
                .unwrap()
                .split("theorem source_count")
                .next()
                .unwrap();
            assert!(
                stack_theorem.contains(&format!(".stack = {expected} := by")),
                "SWAP{depth}"
            );
            if depth == 1 {
                assert!(source.contains("canonical_step_swap1"));
            } else {
                assert!(source.contains(&format!("ExtraOp.exchange .SWAP{depth}")));
                assert!(source.contains(&format!("GolfSwapFamily.bounds (s) .SWAP{depth}")));
            }
        }
        // SWAP2 followed by OR must retain the original top below the merged word.
        let code = [0x91, 0x17];
        let span = Span::select(&code, &code, 0, 2).unwrap();
        assert_eq!(
            (
                span.required,
                span.maximum,
                span.source.delta,
                span.source.gas
            ),
            (3, 1024, -1, 6)
        );
        let source = span.render_proof(&code, &code, 0);
        assert!(source.contains("def value0 (a0 a1 a2 : UInt256) : UInt256 := ((a2) ||| (a1))"));
        assert!(source.contains(".stack = ((value0 a0 a1 a2)) :: (a0) :: tail := by"));
        assert!(source.contains("canonical_step_or"));
        assert!(source.contains("powers := 0") && source.contains("masks := 0"));
    }

    #[test]
    fn comparisons_preserve_canonical_operand_order_and_stack_profiles() {
        let lt = Span::select(&[0x10], &[0x10], 0, 1).unwrap();
        assert_eq!(
            (lt.required, lt.maximum, lt.source.delta, lt.source.gas),
            (2, 1024, -1, 3)
        );
        let source = lt.render_proof(&[0x10], &[0x10], 0);
        assert!(source.contains("UInt256.lt (a0) (a1)"));
        assert!(source.contains("canonical_step_lt"));
        let zero = Span::select(&[0x15], &[0x15], 0, 1).unwrap();
        assert_eq!(
            (
                zero.required,
                zero.maximum,
                zero.source.delta,
                zero.source.gas
            ),
            (1, 1024, 0, 3)
        );
        let source = zero.render_proof(&[0x15], &[0x15], 0);
        assert!(source.contains("UInt256.isZero (a0)"));
        assert!(source.contains("canonical_step_iszero"));
        assert!(Span::select(&[0x10], &[0x15], 0, 1).is_err());
        for unsupported in [0x11, 0x1c] {
            assert!(Span::select(&[unsupported], &[unsupported], 0, 1).is_err());
        }
    }

    #[test]
    fn comparisons_revm_controls_cover_order_zero_and_word_edges() {
        use crate::runtime::{Case, execute};
        use revm::context::result::{ExecutionResult, HaltReason};
        let run = |code: &[u8]| {
            execute(
                code,
                &Case {
                    calldata: String::new(),
                    gas_limit: 200_000,
                    value: String::new(),
                    storage: Default::default(),
                },
            )
            .unwrap()
            .result
        };
        for (ops, stack, expected) in [
            (vec![0x10], vec![U256::from(2), U256::from(7)], 1),
            (vec![0x10], vec![U256::from(7), U256::from(2)], 0),
            (vec![0x10], vec![U256::MAX, U256::MAX], 0),
            (vec![0x10], vec![U256::ZERO, U256::MAX], 1),
            (vec![0x10], vec![U256::MAX, U256::ZERO], 0),
            (vec![0x15], vec![U256::ZERO], 1),
            (vec![0x15], vec![U256::from(1)], 0),
            (vec![0x15], vec![U256::MAX], 0),
            (vec![0x10, 0x15], vec![U256::from(2), U256::from(7)], 0),
        ] {
            let mut code = Vec::new();
            // A surviving caller tail catches accidental extra stack consumption.
            for word in std::iter::once(&U256::from(42)).chain(stack.iter().rev()) {
                code.push(0x7f);
                code.extend(word.to_be_bytes::<32>());
            }
            code.extend(ops);
            code.extend([0x5f, 0x52, 0x60, 32, 0x52, 0x60, 64, 0x5f, 0xf3]);
            let result = run(&code);
            assert!(result.is_success(), "{result:?}");
            let output = result.output().unwrap();
            assert_eq!(&output[..32], &U256::from(expected).to_be_bytes::<32>());
            assert_eq!(&output[32..], &U256::from(42).to_be_bytes::<32>());
        }
        for code in [vec![0x10], vec![0x5f, 0x10], vec![0x15]] {
            assert!(matches!(
                run(&code),
                ExecutionResult::Halt {
                    reason: HaltReason::StackUnderflow,
                    ..
                }
            ));
        }
    }

    #[test]
    fn swap_and_or_revm_controls_check_all_words_and_fault_boundaries() {
        use crate::runtime::{Case, execute};
        use revm::context::result::{ExecutionResult, HaltReason};
        let run = |code: &[u8]| {
            execute(
                code,
                &Case {
                    calldata: String::new(),
                    gas_limit: 200_000,
                    value: String::new(),
                    storage: Default::default(),
                },
            )
            .unwrap()
            .result
        };
        let returned_stack = |ops: &[u8], stack: &[U256], output_words: usize| {
            let mut code = Vec::new();
            for word in stack.iter().rev() {
                code.push(0x7f);
                code.extend(word.to_be_bytes::<32>());
            }
            code.extend_from_slice(ops);
            for i in 0..output_words {
                code.push(0x61);
                code.extend(((i * 32) as u16).to_be_bytes());
                code.push(0x52);
            }
            code.push(0x61);
            code.extend(((output_words * 32) as u16).to_be_bytes());
            code.extend([0x5f, 0xf3]);
            let result = run(&code);
            assert!(result.is_success(), "{result:?}");
            result
                .output()
                .unwrap()
                .as_chunks::<32>()
                .0
                .iter()
                .map(|word| U256::from_be_bytes(*word))
                .collect::<Vec<_>>()
        };
        for depth in 1usize..=16 {
            let opcode = 0x8f + depth as u8;
            let stack = (1..=depth + 4).map(U256::from).collect::<Vec<_>>();
            let expected = std::iter::once(stack[depth])
                .chain(stack[1..depth].iter().copied())
                .chain(std::iter::once(stack[0]))
                .chain(stack[depth + 1..].iter().copied())
                .collect::<Vec<_>>();
            assert_eq!(returned_stack(&[opcode], &stack, stack.len()), expected);
            for height in 0..=depth {
                let mut code = vec![0x5f; height];
                code.extend([opcode, 0]);
                assert!(
                    matches!(
                        run(&code),
                        ExecutionResult::Halt {
                            reason: HaltReason::StackUnderflow,
                            ..
                        }
                    ),
                    "SWAP{depth} height{height}"
                );
            }
            let mut code = vec![0x5f; 1024];
            code.extend([opcode, 0]);
            assert!(run(&code).is_success(), "SWAP{depth} at the stack limit");
        }
        for (a, b, c) in [
            (U256::from(0x11), U256::from(0x0f), U256::from(0xf0)),
            (U256::MAX, U256::ZERO, U256::from(1) << 255),
            (U256::ZERO, U256::MAX, U256::MAX),
        ] {
            let tail = [U256::from(0x1234), U256::from(0x5678)];
            let stack = [a, b, c, tail[0], tail[1]];
            assert_eq!(
                returned_stack(&[0x91, 0x17], &stack, 4),
                [b | c, a, tail[0], tail[1]]
            );
        }
        for height in 0..2 {
            let mut code = vec![0x5f; height];
            code.extend([0x17, 0]);
            assert!(matches!(
                run(&code),
                ExecutionResult::Halt {
                    reason: HaltReason::StackUnderflow,
                    ..
                }
            ));
        }
        let mut code = vec![0x5f; 1024];
        code.extend([0x17, 0]);
        assert!(run(&code).is_success(), "OR shrinks a full stack");
    }

    #[test]
    fn through_jump_rejects_invalid_inputs_before_output_writes() {
        let oversized = format!("7f{}565b", "ff".repeat(32));
        for (name, before, after, entry, exit, expected) in [
            (
                "nonliteral",
                "60018056",
                "60018056",
                0,
                3,
                "must end in an unchanged literal PUSH0..32",
            ),
            (
                "different-literal",
                "6003565b",
                "6004565b",
                0,
                2,
                "unsupported changed instruction",
            ),
            (
                "not-jump",
                "6003005b",
                "6003005b",
                0,
                2,
                "exit must be JUMP in both images",
            ),
            (
                "oversized-push32",
                oversized.as_str(),
                oversized.as_str(),
                0,
                33,
                "destination is outside the full images",
            ),
            (
                "payload-destination",
                "605b600156",
                "605b600156",
                2,
                4,
                "destination is inside PUSH data",
            ),
        ] {
            let temp = tempfile::tempdir().unwrap();
            let out = temp.path().join(name);
            let before = hex::decode(before).unwrap();
            let after = hex::decode(after).unwrap();
            let error = certify_span_through_jump(&before, &after, entry, exit, &out).unwrap_err();
            assert!(error.to_string().contains(expected), "{name}: {error:#}");
            assert!(!out.exists(), "{name} wrote an output directory");
            assert_eq!(fs::read_dir(temp.path()).unwrap().count(), 0);
        }
    }

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
    fn extra_operations_preserve_unary_and_binary_stack_requirements() {
        for (code, expected) in [
            (vec![0x19], (1, 1024, 0, 3)),
            (vec![0x03, 0x16, 0x19], (3, 1024, -2, 9)),
            (
                vec![0x60, 7, 0x60, 2, 0x03, 0x19, 0x60, 15, 0x16],
                (0, 1022, 1, 18),
            ),
        ] {
            let span = Span::select(&code, &code, 0, code.len()).unwrap();
            assert_eq!(
                (
                    span.required,
                    span.maximum,
                    span.source.delta,
                    span.source.gas
                ),
                expected
            );
            assert_eq!(span.powers, 0);
            assert_eq!(span.masks, 0);
        }
        assert!(Span::select(&[0x19], &[0x16], 0, 1).is_err());
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
                .render_proof(&bytes, &bytes, 0)
        };
        let small = render(32);
        let large = render(64);
        // Doubling the trace must preserve linear-size text, including stack/PC proofs.
        assert!(large.len() < small.len() * 3);
    }

    #[test]
    fn mixed_chunks_bound_instruction_work_without_splitting_rewrites() {
        let mut old = MASK_BEFORE.to_vec();
        old.extend([0x60, 32, 2, 1]);
        let mut new = MASK_AFTER.to_vec();
        new.extend([0x60, 5, 0x1b, 1]);
        let old = old.repeat(11);
        let new = new.repeat(11);
        let span = Span::select(&old, &new, 0, old.len()).unwrap();
        let chunks = span.chunks(&old, &new, CHUNK_INSTRUCTIONS).unwrap();
        assert!(chunks.len() > 1);
        let mut pc = span.entry;
        let mut source_steps = 0;
        let mut candidate_steps = 0;
        let mut masks = 0;
        let mut powers = 0;
        for chunk in chunks {
            assert_eq!(chunk.entry, pc);
            assert!(chunk.source.count <= CHUNK_INSTRUCTIONS);
            assert!(chunk.candidate.count <= chunk.source.count);
            for segment in &chunk.segments {
                let width = match segment.kind {
                    SegmentKind::Mask => MASK_BEFORE.len(),
                    SegmentKind::Power { width, .. } => width + 2,
                    SegmentKind::Same { width, .. } => width + 1,
                };
                assert!(segment.pc + width <= chunk.exit);
            }
            source_steps += chunk.source.count;
            candidate_steps += chunk.candidate.count;
            masks += chunk.masks;
            powers += chunk.powers;
            pc = chunk.exit;
        }
        assert_eq!(pc, span.exit);
        assert_eq!(
            (source_steps, candidate_steps),
            (span.source.count, span.candidate.count)
        );
        assert_eq!((masks, powers), (11, 11));
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
        let (_, sources) = span
            .chunk_sources(
                &old,
                &new,
                32,
                render_images(
                    &old,
                    &new,
                    span.entry,
                    span.exit - span.entry,
                    ImageRoutes::Window,
                ),
            )
            .unwrap();
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
