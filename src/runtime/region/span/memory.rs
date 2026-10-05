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
        ensure!(stores > 0, "memory path must contain MSTORE");
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
    ) -> Result<(MemoryPlan, Vec<(String, String)>)> {
        let rendered = render_images(
            original,
            candidate,
            self.entry,
            self.exit - self.entry,
            ImageRoutes::Window,
        );
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
    let (plan, sources) = path.sources(original, candidate)?;
    proof::check_region_output(out)?;
    fs::create_dir(out)
        .with_context(|| format!("use a new output directory: {}", out.display()))?;
    fs::write(out.join("original.hex"), hex::encode(original) + "\n")?;
    fs::write(out.join("candidate.hex"), hex::encode(candidate) + "\n")?;
    for (name, source) in sources {
        fs::write(out.join(name), source)?;
    }
    let lean_version = proof::verify_region(out, proof::RegionKind::MemorySpan(&plan))?;
    let report = MemorySpanCertificate {
        claim: "conditional internal memory-span residual interpreter calls",
        original_keccak256: keccak256(original).to_string(),
        candidate_keccak256: keccak256(candidate).to_string(),
        entry_pc: entry,
        exit_pc: exit,
        source_instruction_count: path.source.count,
        candidate_instruction_count: path.candidate.count,
        source_base_gas: path.source.gas,
        candidate_base_gas: path.candidate.gas,
        gas_requirement: "initial gas >= GolfCertificates.Memory.sourceCost(initial state): source base gas plus canonical expansion at each actual MSTORE stage",
        gas_surplus_increase: path.source.gas - path.candidate.gas,
        required_input_stack_words: path.required,
        maximum_input_stack_words: path.maximum,
        output_stack_delta: path.source.delta,
        execution_count_offset_increase: path.source.count - path.candidate.count,
        power_rewrites: path.powers,
        mask_rewrites: path.masks,
        memory_operations: path.stores,
        proof_root: "GolfCertificates.Memory.memory_boundary",
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
    Ok(SelectedSpanCertificate::Memory(report))
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let error = MemoryPath::select(&payload_only, &payload_only, 0, 2).unwrap_err();
        assert!(error.to_string().contains("must contain MSTORE"));
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
