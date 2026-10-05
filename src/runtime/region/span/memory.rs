//! State-dependent certificates assembled from the existing pure span generator.

use super::*;
use crate::proof::{MemoryPlan, PathLeafKind, SpanNode};

const OPTIONS: &str =
    "set_option Elab.async false\nset_option maxRecDepth 4096\nset_option maxHeartbeats 2000000\n";

/// A selected span keeps the existing pure report or exposes dynamic memory costs.
#[derive(Debug, Serialize)]
#[serde(untagged)]
pub enum SelectedSpanCertificate {
    Pure(SpanCertificate),
    Memory(MemorySpanCertificate),
}

/// Conditional internal-path proof; base gas excludes canonical memory expansion.
#[derive(Debug, Serialize)]
pub struct MemorySpanCertificate {
    pub claim: &'static str,
    pub original_keccak256: String,
    pub candidate_keccak256: String,
    pub entry_pc: usize,
    pub exit_pc: usize,
    pub source_instruction_count: usize,
    pub candidate_instruction_count: usize,
    pub source_base_gas: u64,
    pub candidate_base_gas: u64,
    pub gas_requirement: &'static str,
    pub gas_surplus_increase: u64,
    pub required_input_stack_words: usize,
    pub maximum_input_stack_words: usize,
    pub output_stack_delta: isize,
    pub execution_count_offset_increase: usize,
    pub power_rewrites: usize,
    pub mask_rewrites: usize,
    pub memory_operations: usize,
    pub proof_root: &'static str,
    pub unproved: [&'static str; 5],
    pub lean_version: String,
}

/// A selected path followed by its statically known JUMP.
#[derive(Debug, Serialize)]
#[serde(untagged)]
pub enum SelectedSpanJumpCertificate {
    Pure(SpanJumpCertificate),
    Memory(MemorySpanJumpCertificate),
}

#[derive(Debug, Serialize)]
pub struct MemorySpanJumpCertificate {
    #[serde(flatten)]
    pub span: MemorySpanCertificate,
    pub jump_pc: usize,
    pub pushed_destination: usize,
    pub scanner_scope: &'static str,
}

#[derive(Debug)]
enum Part {
    Pure(Span),
    Store(usize),
}

#[derive(Debug)]
struct MemoryPath {
    entry: usize,
    exit: usize,
    parts: Vec<Part>,
    source: Profile,
    candidate: Profile,
    required: usize,
    maximum: usize,
    powers: usize,
    masks: usize,
    stores: usize,
}

impl MemoryPath {
    fn select(original: &[u8], candidate: &[u8], entry: usize, exit: usize) -> Result<Self> {
        ensure!(
            original.len() <= MAX_RUNTIME_BYTES && candidate.len() <= MAX_RUNTIME_BYTES,
            "runtime exceeds EIP-170 size limit"
        );
        ensure!(
            original.len() == candidate.len(),
            "memory spans require fixed layout"
        );
        ensure!(
            entry < exit && exit <= original.len(),
            "span requires entry PC < exit PC within both images"
        );
        let old = decode(original);
        let new = decode(candidate);
        for instructions in [&old, &new] {
            ensure!(
                instructions.iter().any(|i| i.pc == entry),
                "entry PC is inside a PUSH immediate"
            );
            ensure!(
                exit == original.len() || instructions.iter().any(|i| i.pc == exit),
                "exit PC is inside a PUSH immediate"
            );
        }
        let mut parts = Vec::new();
        let mut start = entry;
        let mut stores = 0;
        let mut powers = 0;
        let mut masks = 0;
        for instruction in old
            .iter()
            .filter(|i| entry <= i.pc && i.pc < exit && i.bytes[0] == 0x52)
        {
            let pc = instruction.pc;
            ensure!(
                new.binary_search_by_key(&pc, |i| i.pc)
                    .is_ok_and(|index| new[index].bytes == [0x52]),
                "MSTORE must be unchanged and aligned in both images"
            );
            if start < pc {
                let span = Span::select(original, candidate, start, pc)?;
                powers += span.powers;
                masks += span.masks;
                parts.push(Part::Pure(span));
            }
            parts.push(Part::Store(pc));
            stores += 1;
            start = pc + 1;
        }
        if start < exit {
            let span = Span::select(original, candidate, start, exit)?;
            powers += span.powers;
            masks += span.masks;
            parts.push(Part::Pure(span));
        }
        let source = profile(&original[entry..exit])?;
        let target = profile(&candidate[entry..exit])?;
        let required = source.required.max(target.required);
        let peak = source.peak.max(target.peak);
        ensure!(
            peak <= 1024 && required <= 1024 - peak,
            "memory span has no admissible stack height"
        );
        Ok(Self {
            entry,
            exit,
            parts,
            required,
            maximum: 1024 - peak,
            source,
            candidate: target,
            powers,
            masks,
            stores,
        })
    }

    fn sources(
        &self,
        original: &[u8],
        candidate: &[u8],
        rendered: RenderedImages,
    ) -> Result<(MemoryPlan, Vec<(String, String)>)> {
        let mut sources = vec![("Images.lean".to_owned(), rendered.source)];
        let mut plan = MemoryPlan {
            leaves: Vec::new(),
            compositions: Vec::new(),
        };
        for part in &self.parts {
            match part {
                Part::Pure(span) => {
                    for leaf in span.chunks(original, candidate, CHUNK_INSTRUCTIONS)? {
                        let index = plan.leaves.len();
                        sources.extend(leaf.leaf_sources(
                            original,
                            candidate,
                            index,
                            &rendered.leaves,
                        ));
                        sources.push((format!("PathLeaf{index}.lean"), format!(
                            "import BindLeaf{index}\nimport PathSummary\n{OPTIONS}open EvmYul GolfCertificates\nnamespace GolfPathLeaf{index}\ndef summary : GolfPathSummary.Summary originalCode candidateCode :=\n GolfPathSummary.ofPure GolfSpanBind{index}.summary\n#print axioms summary\nend GolfPathLeaf{index}\n")));
                        plan.leaves.push(PathLeafKind::Pure);
                    }
                }
                Part::Store(pc) => {
                    let index = plan.leaves.len();
                    let facts =
                        routed_decoded_facts(original, candidate, *pc, pc + 1, &rendered.leaves)
                            .replace("GolfOpcodeDecode.decode_mstore", "decode_mstore");
                    sources.push((format!("PathLeaf{index}.lean"), format!(
                        "import Images\nimport PathSummary\n{OPTIONS}open EvmYul EvmYul.EVM GolfUpstream GolfCertificates\nnamespace GolfPathLeaf{index}\nprivate theorem decode_mstore (code : ByteArray) (pc : UInt256)\n (fetched : code.get? pc.toNat = some (UInt8.ofNat 82)) :\n decode code pc = some ((Operation.MSTORE : Operation .EVM), none) := by\n unfold decode\n rw [fetched]\n rfl\n{facts}\ndef summary : GolfPathSummary.Summary originalCode candidateCode :=\n GolfPathSummary.mstore (UInt256.ofNat {pc}) originalAt{pc} candidateAt{pc}\n#print axioms summary\nend GolfPathLeaf{index}\n")));
                    plan.leaves.push(PathLeafKind::Store);
                }
            }
        }
        let mut nodes = (0..plan.leaves.len())
            .map(SpanNode::Leaf)
            .collect::<Vec<_>>();
        while nodes.len() > 1 {
            let mut parents = Vec::new();
            for pair in nodes.chunks(2) {
                if pair.len() == 1 {
                    parents.push(pair[0]);
                    continue;
                }
                let index = plan.compositions.len();
                plan.compositions.push((pair[0], pair[1]));
                let (left, left_summary) = path_node(pair[0]);
                let (right, right_summary) = path_node(pair[1]);
                sources.push((format!("PathCompose{index}.lean"), format!(
                    "import {left}\nimport {right}\n{OPTIONS}open EvmYul GolfCertificates\nnamespace GolfPathCompose{index}\ndef summary : GolfPathSummary.Summary originalCode candidateCode :=\n GolfPathSummary.compose {left_summary} {right_summary} (by decide) (by decide) (by decide)\n#print axioms summary\nend GolfPathCompose{index}\n")));
                parents.push(SpanNode::Compose(index));
            }
            nodes = parents;
        }
        let (module, summary) = path_node(nodes[0]);
        let mut root = include_str!("../../../../lean/upstream/templates/MemoryPathProof.lean.in")
            .replace("$root_module", &module)
            .replace("$root_summary", &summary);
        for (key, value) in [
            ("$entry_pc", self.entry),
            ("$exit_pc", self.exit),
            ("$source_steps", self.source.count),
            ("$candidate_steps", self.candidate.count),
            ("$required", self.required),
            ("$maximum", self.maximum),
            ("$powers", self.powers),
            ("$masks", self.masks),
        ] {
            root = root.replace(key, &value.to_string());
        }
        sources.push(("MemoryRegionProof.lean".to_owned(), root));
        Ok((plan, sources))
    }

    fn report(
        &self,
        original: &[u8],
        candidate: &[u8],
        lean_version: String,
    ) -> MemorySpanCertificate {
        MemorySpanCertificate {
            claim: "conditional internal memory-span residual interpreter calls",
            original_keccak256: keccak256(original).to_string(),
            candidate_keccak256: keccak256(candidate).to_string(),
            entry_pc: self.entry,
            exit_pc: self.exit,
            source_instruction_count: self.source.count,
            candidate_instruction_count: self.candidate.count,
            source_base_gas: self.source.gas,
            candidate_base_gas: self.candidate.gas,
            gas_requirement: "initial gas >= GolfCertificates.Memory.sourceCost(initial state): source base gas plus canonical expansion at each actual MSTORE stage",
            gas_surplus_increase: self.source.gas - self.candidate.gas,
            required_input_stack_words: self.required,
            maximum_input_stack_words: self.maximum,
            output_stack_delta: self.source.delta,
            execution_count_offset_increase: self.source.count - self.candidate.count,
            power_rewrites: self.powers,
            mask_rewrites: self.masks,
            memory_operations: self.stores,
            proof_root: "GolfCertificates.Memory.memory_boundary",
            unproved: [
                "entry reachability",
                "suffix outcomes",
                "whole-contract and all-gas equivalence",
                "canonical transaction entry",
                "revm correspondence",
            ],
            lean_version,
        }
    }
}

fn path_node(node: SpanNode) -> (String, String) {
    match node {
        SpanNode::Leaf(i) => (format!("PathLeaf{i}"), format!("GolfPathLeaf{i}.summary")),
        SpanNode::Compose(i) => (
            format!("PathCompose{i}"),
            format!("GolfPathCompose{i}.summary"),
        ),
    }
}

/// Select the proof from decoded instructions while retaining pure span reports.
pub fn certify_selected_span(
    original: &[u8],
    candidate: &[u8],
    entry: usize,
    exit: usize,
    out: &Path,
) -> Result<SelectedSpanCertificate> {
    ensure!(
        original.len() <= MAX_RUNTIME_BYTES && candidate.len() <= MAX_RUNTIME_BYTES,
        "runtime exceeds EIP-170 size limit"
    );
    if !decode(original)
        .iter()
        .any(|i| entry <= i.pc && i.pc < exit && i.bytes[0] == 0x52)
    {
        return certify_span(original, candidate, entry, exit, out)
            .map(SelectedSpanCertificate::Pure);
    }
    let path = MemoryPath::select(original, candidate, entry, exit)?;
    let rendered = render_images(
        original,
        candidate,
        entry,
        exit - entry,
        ImageRoutes::Window,
    );
    let (plan, sources) = path.sources(original, candidate, rendered)?;
    proof::check_region_output(out)?;
    fs::create_dir(out)
        .with_context(|| format!("use a new output directory: {}", out.display()))?;
    fs::write(out.join("original.hex"), hex::encode(original) + "\n")?;
    fs::write(out.join("candidate.hex"), hex::encode(candidate) + "\n")?;
    for (name, source) in sources {
        fs::write(out.join(name), source)?;
    }
    let lean_version = proof::verify_region(out, proof::RegionKind::MemorySpan(&plan))?;
    let report = path.report(original, candidate, lean_version);
    fs::write(
        out.join("result.json"),
        serde_json::to_string_pretty(&report)? + "\n",
    )?;
    Ok(SelectedSpanCertificate::Memory(report))
}

/// Execute a selected pure or memory path and its immediately following static JUMP.
pub fn certify_selected_span_through_jump(
    original: &[u8],
    candidate: &[u8],
    entry: usize,
    exit: usize,
    out: &Path,
) -> Result<SelectedSpanJumpCertificate> {
    ensure!(
        original.len() <= MAX_RUNTIME_BYTES && candidate.len() <= MAX_RUNTIME_BYTES,
        "runtime exceeds EIP-170 size limit"
    );
    if !decode(original)
        .iter()
        .any(|i| entry <= i.pc && i.pc < exit && i.bytes[0] == 0x52)
    {
        return certify_span_through_jump(original, candidate, entry, exit, out)
            .map(SelectedSpanJumpCertificate::Pure);
    }
    let path = MemoryPath::select(original, candidate, entry, exit)?;
    ensure!(
        original.get(exit) == Some(&0x56) && candidate.get(exit) == Some(&0x56),
        "span exit must be JUMP in both images"
    );
    let destination = match path.parts.last() {
        Some(Part::Pure(span)) => match span.segments.last().map(|segment| &segment.kind) {
            Some(SegmentKind::Same {
                op: 0x5f..=0x7f,
                value,
                ..
            }) => *value,
            _ => bail!("through-jump span must end in an unchanged literal PUSH0..32"),
        },
        _ => bail!("through-jump span must end in an unchanged literal PUSH0..32"),
    };
    ensure!(
        destination < U256::from(original.len()),
        "jump destination is outside the full images"
    );
    let destination = destination.to::<usize>();
    let rendered = render_images(original, candidate, entry, exit - entry, ImageRoutes::All);
    let membership =
        super::super::jump::membership_sources(original, candidate, destination, &rendered)?;
    let jump_decodes = routed_decoded_facts(original, candidate, exit, exit + 1, &rendered.leaves)
        .replace("GolfOpcodeDecode.decode_jump", "jump_decode");
    let (plan, mut sources) = path.sources(original, candidate, rendered)?;
    let root_node = plan
        .compositions
        .len()
        .checked_sub(1)
        .map_or(SpanNode::Leaf(0), SpanNode::Compose);
    let (_, summary) = path_node(root_node);
    let mut terminal = include_str!("../../../../lean/upstream/templates/MemoryJump.lean.in")
        .replace("$root_summary", &summary)
        .replace("$jump_decodes", &jump_decodes);
    for (key, value) in [
        ("$entry_pc", entry),
        ("$jump_pc", exit),
        ("$destination", destination),
        ("$source_steps", path.source.count),
        ("$target_steps", path.candidate.count),
        ("$required", path.required),
        ("$maximum", path.maximum),
        ("$powers", path.powers),
        ("$masks", path.masks),
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
        "MemoryJumpProof".to_owned(),
        vec![
            "GolfCertificates.MemoryJump.source_count".to_owned(),
            "GolfCertificates.MemoryJump.source_gas".to_owned(),
            "GolfCertificates.MemoryJump.memory_jump_boundary".to_owned(),
        ],
    ));
    sources.extend(
        membership
            .into_iter()
            .map(|(name, source, _)| (format!("{name}.lean"), source)),
    );
    sources.push(("MemoryJumpProof.lean".to_owned(), terminal));
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
    let lean_version = proof::verify_region(out, proof::RegionKind::MemoryJump(&plan, &jump_plan))?;
    let mut span = path.report(original, candidate, lean_version);
    span.claim = "conditional checked-scanner internal memory span through JUMP";
    span.exit_pc = destination;
    span.source_instruction_count += 1;
    span.candidate_instruction_count += 1;
    span.source_base_gas += 8;
    span.candidate_base_gas += 8;
    span.output_stack_delta -= 1;
    span.gas_requirement = "initial gas >= GolfCertificates.MemoryJump.sourceCost(initial state): source base gas plus canonical expansion at each actual MSTORE stage";
    span.proof_root = "GolfCertificates.MemoryJump.memory_jump_boundary";
    let report = MemorySpanJumpCertificate {
        span,
        jump_pc: exit,
        pushed_destination: destination,
        scanner_scope: "checked-scanner semantics; equivalence with the original opaque upstream scanner is unproved",
    };
    fs::write(
        out.join("result.json"),
        serde_json::to_string_pretty(&report)? + "\n",
    )?;
    Ok(SelectedSpanJumpCertificate::Memory(report))
}

/// Successful execution of an explicit terminal instruction after a supported span.
#[derive(Debug, Serialize)]
pub struct TerminalCertificate {
    #[serde(flatten)]
    pub span: MemorySpanCertificate,
    pub terminal_pc: usize,
    pub terminal: &'static str,
    pub output_condition: &'static str,
}

/// Execute STOP, RETURN or REVERT with explicit input-state and memory operand conditions.
pub fn certify_selected_span_through_halt(
    original: &[u8],
    candidate: &[u8],
    entry: usize,
    exit: usize,
    out: &Path,
) -> Result<TerminalCertificate> {
    certify_terminal(original, candidate, entry, exit, out, false)
}

/// Execute canonical Ξ from its actual fresh state, with no incoming stack.
pub fn certify_selected_span_from_call_entry(
    original: &[u8],
    candidate: &[u8],
    entry: usize,
    exit: usize,
    out: &Path,
) -> Result<TerminalCertificate> {
    ensure!(entry == 0, "call-entry certificates require entry PC zero");
    certify_terminal(original, candidate, entry, exit, out, true)
}

fn certify_terminal(
    original: &[u8],
    candidate: &[u8],
    entry: usize,
    exit: usize,
    out: &Path,
    from_call_entry: bool,
) -> Result<TerminalCertificate> {
    let path = MemoryPath::select(original, candidate, entry, exit)?;
    let (kind, name, template, consumed) = match (original.get(exit), candidate.get(exit)) {
        (Some(0x00), Some(0x00)) => (
            proof::TerminalKind::Stop,
            "STOP",
            include_str!("../../../../lean/upstream/templates/TerminalStop.lean.in"),
            0usize,
        ),
        (Some(0xf3), Some(0xf3)) => (
            proof::TerminalKind::Return,
            "RETURN",
            include_str!("../../../../lean/upstream/templates/TerminalReturn.lean.in"),
            2usize,
        ),
        (Some(0xfd), Some(0xfd)) => (
            proof::TerminalKind::Revert,
            "REVERT",
            include_str!("../../../../lean/upstream/templates/TerminalRevert.lean.in"),
            2usize,
        ),
        _ => bail!("span exit must be the same explicit STOP, RETURN or REVERT in both images"),
    };
    // RETURN and REVERT can consume surviving caller words, not just words produced by the span.
    let required = path
        .required
        .max((consumed as isize - path.source.delta).max(0) as usize);
    ensure!(
        required <= path.maximum,
        "terminal has no admissible stack height"
    );
    ensure!(
        !from_call_entry || required == 0,
        "call-entry terminal requires an admissible empty input stack"
    );
    // Include the terminal byte in the routed window, while selecting the body only to exit.
    let rendered = render_images(
        original,
        candidate,
        entry,
        exit - entry + 1,
        ImageRoutes::Window,
    );
    let decodes = routed_decoded_facts(original, candidate, exit, exit + 1, &rendered.leaves)
        .replace(
            &format!("GolfOpcodeDecode.decode_{}", name.to_ascii_lowercase()),
            "terminal_decode",
        );
    let (plan, mut sources) = path.sources(original, candidate, rendered)?;
    let root_node = plan
        .compositions
        .len()
        .checked_sub(1)
        .map_or(SpanNode::Leaf(0), SpanNode::Compose);
    let (_, summary) = path_node(root_node);
    let terminal = template
        .replace("$root_summary", &summary)
        .replace("$terminal_decodes", &decodes)
        .replace("$exit_pc", &exit.to_string())
        .replace("$source_steps", &path.source.count.to_string())
        .replace("$required", &required.to_string());
    sources.push(("TerminalProof.lean".to_owned(), terminal));
    if from_call_entry {
        let template = match kind {
            proof::TerminalKind::Stop => {
                include_str!("../../../../lean/upstream/templates/CallEntryStop.lean.in")
            }
            proof::TerminalKind::Return => {
                include_str!("../../../../lean/upstream/templates/CallEntryReturn.lean.in")
            }
            proof::TerminalKind::Revert => {
                include_str!("../../../../lean/upstream/templates/CallEntryRevert.lean.in")
            }
        };
        let source = template
            .replace("$root_summary", &summary)
            .replace("$source_steps", &path.source.count.to_string())
            .replace("$target_steps", &path.candidate.count.to_string())
            .replace("$surplus", &(2 * path.powers + 9 * path.masks).to_string())
            .replace("$skipped", &(3 * path.masks).to_string());
        sources.push(("CallEntryProof.lean".to_owned(), source));
    }
    proof::check_region_output(out)?;
    if let Some(parent) = out.parent().filter(|p| !p.as_os_str().is_empty()) {
        fs::create_dir_all(parent)?;
    }
    fs::create_dir(out)
        .with_context(|| format!("use a new output directory: {}", out.display()))?;
    fs::write(out.join("original.hex"), hex::encode(original) + "\n")?;
    fs::write(out.join("candidate.hex"), hex::encode(candidate) + "\n")?;
    for (name, source) in sources {
        fs::write(out.join(name), source)?;
    }
    let mode = if from_call_entry {
        proof::RegionKind::CallEntry(&plan, kind)
    } else {
        proof::RegionKind::Terminal(&plan, kind)
    };
    let lean_version = proof::verify_region(out, mode)?;
    let mut span = path.report(original, candidate, lean_version);
    span.claim = "conditional paired canonical success and equal output after an internal span";
    span.source_instruction_count += 1;
    span.candidate_instruction_count += 1;
    span.exit_pc = exit + usize::from(consumed != 0);
    span.output_stack_delta -= consumed as isize;
    span.required_input_stack_words = required;
    span.gas_requirement = if consumed == 0 {
        "initial gas >= GolfCertificates.Terminal.sourceCost(initial state): source body cost including canonical MSTORE expansion"
    } else {
        "initial gas >= GolfCertificates.Terminal.sourceCost(initial state): source body cost plus RETURN expansion evaluated after the body"
    };
    span.proof_root = "GolfCertificates.Terminal.terminal_success";
    span.unproved = [
        "entry reachability",
        "arbitrary contextual equivalence",
        "whole-contract and all-gas equivalence",
        "canonical transaction entry",
        "revm correspondence",
    ];
    if from_call_entry {
        span.claim = "conditional paired canonical Ξ call-entry success and equal output from empty initial stack and memory";
        span.proof_root = "GolfCertificates.CallEntry.call_entry_success";
        span.gas_requirement = "initial gas >= GolfCertificates.Terminal.sourceCost(canonical fresh source state), including actual memory expansion";
        span.unproved = [
            "message-call dispatch",
            "arbitrary contextual equivalence",
            "whole-contract and all-gas equivalence",
            "canonical transaction entry",
            "revm correspondence",
        ];
    }
    if matches!(kind, proof::TerminalKind::Revert) {
        span.claim = if from_call_entry {
            "conditional paired canonical Ξ call-entry revert with equal output and related remaining gas"
        } else {
            "conditional paired canonical revert with equal output and related remaining gas after an internal span"
        };
        span.proof_root = if from_call_entry {
            "GolfCertificates.CallEntry.call_entry_revert"
        } else {
            "GolfCertificates.Terminal.terminal_revert"
        };
        span.gas_requirement = "initial gas >= GolfCertificates.Terminal.sourceCost(initial source state): source body cost plus REVERT expansion evaluated after the body";
    }
    let report = TerminalCertificate {
        span,
        terminal_pc: exit,
        terminal: name,
        output_condition: if matches!(kind, proof::TerminalKind::Revert) && from_call_entry {
            "canonical fresh PC0/empty stack/memory; related linked current/original maps; operands, physical bound and size<2^64 checked from stackMap[]; equal canonical memory output and related remaining gas; no caller or transaction rollback claim"
        } else if matches!(kind, proof::TerminalKind::Revert) {
            "body stackMap equals address :: size :: tail, has at most 1024 words, and size.toNat<2^64; equal canonical padded memory output and related remaining gas; exit_pc describes the internal step, not a returned state; no rollback claim"
        } else if from_call_entry && consumed == 0 {
            "shared environment; related current/original account maps with owner/code witnesses in both; canonical fresh PC0/empty stack/memory; empty canonical output"
        } else if from_call_entry {
            "shared environment; related current/original account maps with owner/code witnesses in both; canonical fresh PC0/empty stack/memory; RETURN operands, physical bound and size<2^64 discharged from certified stackMap[]"
        } else if consumed == 0 {
            "empty canonical output; physical output stack bound discharged"
        } else {
            "body stackMap equals address :: size :: tail, has at most 1024 words, and size.toNat < 2^64; output is canonical padded memory at the body endpoint"
        },
    };
    fs::write(
        out.join("result.json"),
        serde_json::to_string_pretty(&report)? + "\n",
    )?;
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn call_entry_requires_zero_pc_and_terminal_admissible_empty_stack() {
        for (code, entry, exit, expected) in [
            (vec![0x5f, 0x5f, 0], 1, 2, "entry PC zero"),
            (vec![0x60, 2, 2, 0], 0, 3, "empty input stack"),
            // The body needs no input, but RETURN still needs a second operand.
            (vec![0x5f, 0xf3], 0, 1, "empty input stack"),
            (vec![0x5f, 0xfd], 0, 1, "empty input stack"),
        ] {
            let temp = tempfile::tempdir().unwrap();
            let out = temp.path().join("new-parent").join("result");
            let error =
                certify_selected_span_from_call_entry(&code, &code, entry, exit, &out).unwrap_err();
            assert!(error.to_string().contains(expected), "{error:#}");
            assert_eq!(fs::read_dir(temp.path()).unwrap().count(), 0);
        }
    }

    #[test]
    fn halt_preflight_rejects_invalid_terminals_without_output() {
        for (before, after, exit) in [
            (vec![0x5f, 0x56], vec![0x5f, 0x56], 1),
            (vec![0x5f, 0x00], vec![0x5f, 0xf3], 1),
            (vec![0x60, 0xf3, 0x00], vec![0x60, 0xf3, 0x00], 1),
            (vec![0x5f], vec![0x5f], 1),
            (vec![0x5f, 0x5f, 0xfd], vec![0x5f, 0x5f, 0xf3], 2),
            (vec![0x60, 0xfd, 0], vec![0x60, 0xfd, 0], 1),
        ] {
            let temp = tempfile::tempdir().unwrap();
            let out = temp.path().join("new-parent").join("result");
            assert!(certify_selected_span_through_halt(&before, &after, 0, exit, &out).is_err());
            assert_eq!(fs::read_dir(temp.path()).unwrap().count(), 0);
        }
    }

    #[test]
    fn terminal_body_reuses_pure_and_memory_profiles() {
        let pure = [0x60, 7, 0x60, 32, 2, 0];
        let shifted = [0x60, 7, 0x60, 5, 0x1b, 0];
        let path = MemoryPath::select(&pure, &shifted, 0, 5).unwrap();
        assert_eq!((path.stores, path.powers, path.required), (0, 1, 0));
        assert_eq!(
            (path.source.count, path.source.gas, path.candidate.gas),
            (3, 11, 9)
        );
        let code = [0x60, 7, 0x5f, 0x52, 0x60, 32, 0x5f, 0xf3];
        let path = MemoryPath::select(&code, &code, 0, 7).unwrap();
        assert_eq!((path.stores, path.required, path.source.delta), (1, 0, 2));
        // A RETURN can also consume caller words surviving an unchanged pure span.
        let code = [0x90, 0xf3];
        let path = MemoryPath::select(&code, &code, 0, 1).unwrap();
        assert_eq!(
            (path.required, path.source.delta, path.maximum),
            (2, 0, 1024)
        );
    }

    #[test]
    fn revert_rejects_changed_output_bytes_before_writing() {
        let before = [0x60, 7, 0x5f, 0x52, 0x60, 32, 0x5f, 0xfd];
        let mut after = before;
        after[1] = 8;
        let temp = tempfile::tempdir().unwrap();
        let out = temp.path().join("new-parent").join("result");
        assert!(certify_selected_span_through_halt(&before, &after, 0, 7, &out).is_err());
        assert_eq!(fs::read_dir(temp.path()).unwrap().count(), 0);
    }

    #[test]
    fn invalid_memory_jump_rejects_without_creating_parents() {
        for (name, code, exit, expected) in [
            (
                "missing-jump",
                vec![0x52, 0x60, 4, 0, 0x5b],
                3,
                "exit must be JUMP",
            ),
            (
                "final-store",
                vec![0x52, 0x56, 0x5b],
                1,
                "unchanged literal PUSH",
            ),
            (
                "final-swap",
                vec![0x52, 0x60, 5, 0x90, 0x56, 0x5b],
                4,
                "unchanged literal PUSH",
            ),
            (
                "outside",
                vec![0x52, 0x60, 99, 0x56, 0x5b],
                3,
                "outside the full images",
            ),
            (
                "not-destination",
                vec![0x52, 0x60, 0, 0x56, 0x5b],
                3,
                "must contain JUMPDEST",
            ),
            (
                "payload",
                vec![0x52, 0x60, 6, 0x56, 0x61, 0, 0x5b],
                3,
                "inside PUSH data",
            ),
        ] {
            let temp = tempfile::tempdir().unwrap();
            let out = temp.path().join("missing-parent").join(name);
            let error =
                certify_selected_span_through_jump(&code, &code, 0, exit, &out).unwrap_err();
            assert!(error.to_string().contains(expected), "{name}: {error:#}");
            assert_eq!(
                fs::read_dir(temp.path()).unwrap().count(),
                0,
                "{name} wrote before rejection"
            );
        }
    }

    #[test]
    fn memory_jump_generation_keeps_dynamic_cost_and_distinct_mask_counts() {
        let mut original = [&[0x52][..], &MASK_BEFORE, &[0x60, 0, 0x56, 0x5b]].concat();
        let mut candidate = [&[0x52][..], &MASK_AFTER, &[0x60, 0, 0x56, 0x5b]].concat();
        let destination = original.len() - 1;
        let exit = destination - 1;
        original[exit - 1] = destination as u8;
        candidate[exit - 1] = destination as u8;
        let path = MemoryPath::select(&original, &candidate, 0, exit).unwrap();
        let rendered = render_images(&original, &candidate, 0, exit, ImageRoutes::All);
        let memberships = super::super::super::jump::membership_sources(
            &original,
            &candidate,
            destination,
            &rendered,
        )
        .unwrap();
        assert_eq!(memberships.last().unwrap().0, "JumpMembership");
        let (plan, sources) = path.sources(&original, &candidate, rendered).unwrap();
        assert_eq!(plan.leaves.len(), 2);
        assert_eq!(
            sources
                .iter()
                .filter(|(name, _)| name == "Images.lean")
                .count(),
            1
        );
        assert!(
            sources
                .iter()
                .any(|(name, source)| name == "MemoryRegionProof.lean"
                    && source.contains(".cost s")
                    && !source.contains('$'))
        );
        let report = path.report(&original, &candidate, "uncompiled test".to_owned());
        assert_eq!(
            (
                report.source_instruction_count + 1,
                report.candidate_instruction_count + 1
            ),
            (15, 12)
        );
        assert_eq!(
            (report.source_base_gas + 8, report.candidate_base_gas + 8),
            (50, 41)
        );
        assert_eq!(
            (
                report.gas_surplus_increase,
                report.execution_count_offset_increase
            ),
            (9, 3)
        );
        assert_eq!(report.output_stack_delta - 1, -1);
        assert!(report.gas_requirement.contains("canonical expansion"));
    }

    #[test]
    fn decoded_stores_partition_without_empty_pure_parts() {
        for (code, expected, required, delta, gas) in [
            (vec![0x52], vec![Some(0)], 2, -2, 3),
            (vec![0x52, 0x5f], vec![Some(0), None], 2, -1, 5),
            (vec![0x5f, 0x52], vec![None, Some(1)], 1, -1, 5),
            (vec![0x52, 0x52], vec![Some(0), Some(1)], 4, -4, 6),
            (
                vec![0x52, 0x5f, 0x52],
                vec![Some(0), None, Some(2)],
                3,
                -3,
                8,
            ),
        ] {
            let path = MemoryPath::select(&code, &code, 0, code.len()).unwrap();
            let actual = path
                .parts
                .iter()
                .map(|part| match part {
                    Part::Store(pc) => Some(*pc),
                    Part::Pure(span) => {
                        assert!(span.entry < span.exit);
                        None
                    }
                })
                .collect::<Vec<_>>();
            assert_eq!(actual, expected);
            assert_eq!(path.required, required);
            assert_eq!(path.maximum, 1024 - path.source.peak);
            assert_eq!((path.source.delta, path.source.gas), (delta, gas));
            assert_eq!(
                path.stores,
                expected.iter().filter(|pc| pc.is_some()).count()
            );
        }
    }

    #[test]
    fn push_payload_is_not_a_store_or_a_valid_split_boundary() {
        let payload_only = [0x60, 0x52];
        let path = MemoryPath::select(&payload_only, &payload_only, 0, 2).unwrap();
        assert_eq!(path.stores, 0);
        assert!(matches!(&path.parts[..], [Part::Pure(_)]));
        let code = [0x60, 0x52, 0x52];
        let path = MemoryPath::select(&code, &code, 0, 3).unwrap();
        assert_eq!(path.stores, 1);
        assert_eq!(path.required, 1);
        assert_eq!(
            (path.source.count, path.source.gas, path.source.delta),
            (2, 6, -1)
        );
        assert!(
            matches!(&path.parts[..], [Part::Pure(span), Part::Store(2)] if span.entry == 0 && span.exit == 2)
        );
        let error = MemoryPath::select(&code, &code, 1, 3).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("entry PC is inside a PUSH immediate")
        );
        let error = MemoryPath::select(&code, &code, 0, 1).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("exit PC is inside a PUSH immediate")
        );
    }

    #[test]
    fn invalid_memory_paths_reject_before_any_output_writes() {
        let too_many_stores = vec![0x52; 513];
        for (name, original, candidate, entry, exit, expected) in [
            ("width", vec![0x52], vec![0x52, 0], 0, 1, "fixed layout"),
            (
                "changed-store",
                vec![0x52],
                vec![0x50],
                0,
                1,
                "MSTORE must be unchanged",
            ),
            (
                "candidate-payload",
                vec![0x5f, 0x52],
                vec![0x60, 0x52],
                0,
                2,
                "MSTORE must be unchanged",
            ),
            (
                "candidate-exit",
                vec![0x52, 0x5f, 0x5f],
                vec![0x52, 0x60, 0x01],
                0,
                2,
                "exit PC is inside a PUSH immediate",
            ),
            (
                "height",
                too_many_stores.clone(),
                too_many_stores,
                0,
                513,
                "no admissible stack height",
            ),
            (
                "truncated",
                vec![0x52, 0x61, 0x01],
                vec![0x52, 0x61, 0x01],
                0,
                3,
                "truncated source PUSH",
            ),
        ] {
            let temp = tempfile::tempdir().unwrap();
            let out = temp.path().join(name);
            let error =
                certify_selected_span(&original, &candidate, entry, exit, &out).unwrap_err();
            assert!(error.to_string().contains(expected), "{name}: {error:#}");
            assert!(!out.exists(), "{name} wrote output before rejection");
            assert_eq!(fs::read_dir(temp.path()).unwrap().count(), 0);
        }
    }

    #[test]
    fn store_then_mask_preserves_distinct_step_and_base_gas_metadata() {
        let original = [&[0x52][..], &MASK_BEFORE].concat();
        let candidate = [&[0x52][..], &MASK_AFTER].concat();
        let path = MemoryPath::select(&original, &candidate, 0, original.len()).unwrap();
        assert!(
            matches!(&path.parts[..], [Part::Store(0), Part::Pure(span)] if span.entry == 1 && span.masks == 1)
        );
        assert_eq!((path.stores, path.masks, path.powers), (1, 1, 0));
        assert_eq!((path.source.count, path.candidate.count), (13, 10));
        assert_eq!((path.source.gas, path.candidate.gas), (39, 30));
        // The store removes two words before the mask's peak of three extra words.
        assert_eq!(
            (path.required, path.maximum, path.source.delta),
            (3, 1023, -1)
        );
    }
}
