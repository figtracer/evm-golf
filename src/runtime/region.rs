//! Conditional internal-region certificates against pinned upstream EVM semantics.

use anyhow::{Context as _, Result, ensure};
use revm::primitives::{U256, hex, keccak256};
use serde::Serialize;
use std::{fmt::Write as _, fs, path::Path};

mod jump;
mod span;
pub use span::{
    MemorySpanCertificate, MemorySpanJumpCertificate, SelectedSpanCertificate,
    SelectedSpanJumpCertificate, SpanCertificate, SpanJumpCertificate, TerminalCertificate,
    certify_selected_span, certify_selected_span_from_call_entry,
    certify_selected_span_through_halt, certify_selected_span_through_jump, certify_span,
    certify_span_through_jump,
};

use super::MAX_RUNTIME_BYTES;
use crate::proof;

const IMAGES: &str = include_str!("../../lean/upstream/templates/Images.lean.in");
const DECODE: &str = include_str!("../../lean/upstream/templates/Decode.lean.in");
// Bounded leaves and balanced appends avoid kernel stack overflow on full EIP-170
// images. This changes proof representation, not the accepted input size.
const IMAGE_CHUNK_BYTES: usize = 256;
const MASK_DECODE: &str = include_str!("../../lean/upstream/templates/MaskDecode.lean.in");
const MASK_REGION: &str = include_str!("../../lean/upstream/templates/MaskRegionProof.lean.in");
const MASK_BEFORE: [u8; 18] = [
    0x60, 1, 0x60, 1, 0x60, 0xe0, 0x1b, 3, 0x16, 0x60, 1, 0x60, 1, 0x60, 0xe0, 0x1b, 3, 0x19,
];
const MASK_AFTER: [u8; 18] = [
    0x60, 1, 0x60, 1, 0x60, 0xe0, 0x1b, 3, 0x16, 0x64, 0, 0xff, 0xff, 0xff, 0xff, 0x60, 0xe0, 0x1b,
];
const REGION: &str = include_str!("../../lean/upstream/templates/RegionProof.lean.in");
const JUMP_REGION: &str = include_str!("../../lean/upstream/templates/JumpRegionProof.lean.in");

/// Conditions and scope of the generated theorem, not a whole-contract verdict.
#[derive(Debug, Serialize)]
pub struct RegionCertificate {
    pub claim: &'static str,
    pub original_keccak256: String,
    pub candidate_keccak256: String,
    pub entry_pc: usize,
    pub exit_pc: usize,
    pub pushed_destination: u16,
    pub source_gas_minimum: u64,
    pub gas_surplus_increase: u64,
    pub input_stack: &'static str,
    pub maximum_tail_length: usize,
    pub output_stack: String,
    pub interpreter_fuel: &'static str,
    pub state_relation: &'static str,
    pub unproved: [&'static str; 5],
    pub lean_version: String,
}

struct Region {
    entry_pc: usize,
    destination: u16,
}

impl Region {
    fn select(original: &[u8], candidate: &[u8], entry_pc: usize) -> Result<Self> {
        ensure!(
            original.len() <= MAX_RUNTIME_BYTES && candidate.len() <= MAX_RUNTIME_BYTES,
            "runtime exceeds EIP-170 size limit"
        );
        ensure!(
            original.len() == candidate.len(),
            "region certificates require fixed layout"
        );
        let end = entry_pc.checked_add(12).context("region PC overflow")?;
        let before = original
            .get(entry_pc..end)
            .context("truncated source region")?;
        let after = candidate
            .get(entry_pc..end)
            .context("truncated candidate region")?;
        ensure!(
            before[..9] == [0x60, 0x20, 0x02, 0x01, 0x90, 0x5f, 0x80, 0x80, 0x61]
                && before[11] == 0x56,
            "unsupported source region: expected PUSH1 32; MUL; ADD; SWAP1; PUSH0; DUP1; DUP1; PUSH2; JUMP"
        );
        ensure!(
            after[..3] == [0x60, 0x05, 0x1b] && after[3..] == before[3..],
            "unsupported candidate region: expected PUSH1 5; SHL and unchanged region remainder"
        );
        Ok(Self {
            entry_pc,
            destination: u16::from_be_bytes([before[9], before[10]]),
        })
    }

    fn sources(
        &self,
        original: &[u8],
        candidate: &[u8],
        images: String,
    ) -> [(&'static str, String); 3] {
        let facts = decoded_facts(
            &original[self.entry_pc..self.entry_pc + 12],
            &candidate[self.entry_pc..self.entry_pc + 12],
            self.entry_pc,
            Some(&[
                "PushDecoded",
                "OpDecoded",
                "AddDecoded",
                "SwapDecoded",
                "ZeroDecoded",
                "DupADecoded",
                "DupBDecoded",
                "TargetDecoded",
                "JumpDecoded",
            ]),
        );
        let decode = DECODE
            .replace("$image_module", "Images")
            .replace("$namespace", "GolfCertificates.Region")
            .replace("$entry_pc", &self.entry_pc.to_string())
            .replace("$decoded_facts", &facts);
        let region = REGION
            .replace("$decode_module", "Decode")
            .replace("$namespace", "GolfCertificates.Region")
            .replace("$entry_pc", &self.entry_pc.to_string())
            .replace("$exit_pc", &(self.entry_pc + 11).to_string())
            .replace("$destination", &self.destination.to_string());
        [
            ("Images.lean", images),
            ("Decode.lean", decode),
            ("RegionProof.lean", region),
        ]
    }
}

/// Check the selected eight-instruction prefix, ending before JUMP.
///
/// The surrounding bytecode may differ; it is embedded independently on both
/// sides and is not covered by this region's conclusion. No reachability,
/// transaction replay, jump execution, or whole-runtime equivalence is implied.
pub fn certify(
    original: &[u8],
    candidate: &[u8],
    entry_pc: usize,
    out: &Path,
) -> Result<RegionCertificate> {
    let region = Region::select(original, candidate, entry_pc)?;
    fs::create_dir(out)
        .with_context(|| format!("use a new output directory: {}", out.display()))?;
    fs::write(out.join("original.hex"), hex::encode(original) + "\n")?;
    fs::write(out.join("candidate.hex"), hex::encode(candidate) + "\n")?;
    for (name, source) in region.sources(
        original,
        candidate,
        images(original, candidate, entry_pc, 12),
    ) {
        fs::write(out.join(name), source)?;
    }
    let lean_version = proof::verify_region(out, proof::RegionKind::Power)?;
    let report = RegionCertificate {
        claim: "conditional internal-region residual interpreter calls",
        original_keccak256: keccak256(original).to_string(),
        candidate_keccak256: keccak256(candidate).to_string(),
        entry_pc,
        exit_pc: entry_pc + 11,
        pushed_destination: region.destination,
        source_gas_minimum: 25,
        gas_surplus_increase: 2,
        input_stack: "a :: b :: c :: tail (top first; arbitrary 256-bit words)",
        maximum_tail_length: 1018,
        output_stack: format!(
            "{} :: 0 :: 0 :: 0 :: c :: (32*a+b modulo 2^256) :: tail",
            region.destination
        ),
        interpreter_fuel: "for every natural fuel, each X(fuel+9) reduces to its own X(fuel+1) at the exit",
        state_relation: "arbitrary nonnegative incoming gas surplus; related current/original account maps differing only in designated deployed code; both execution-code links; all other frame fields preserved",
        unproved: [
            "entry reachability",
            "exit JUMP execution",
            "suffix outcomes",
            "whole-contract equivalence",
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

/// Check the exact power region through its trailing JUMP under checked-scanner semantics.
///
/// Both complete images must have an instruction boundary at the entry and a
/// valid JUMPDEST at the pushed destination. The destination is not executed;
/// entry reachability and suffix equivalence remain outside the certificate.
pub fn certify_through_jump(
    original: &[u8],
    candidate: &[u8],
    entry_pc: usize,
    out: &Path,
) -> Result<RegionCertificate> {
    let region = Region::select(original, candidate, entry_pc)?;
    for (side, code) in [("source", original), ("candidate", candidate)] {
        ensure!(
            super::decode(code)
                .iter()
                .any(|instruction| instruction.pc == entry_pc),
            "{side} entry PC is not an instruction boundary"
        );
    }
    let rendered = render_images(original, candidate, entry_pc, 12, ImageRoutes::All);
    let membership = jump::membership_sources(
        original,
        candidate,
        usize::from(region.destination),
        &rendered,
    )?;
    let mut plan = proof::JumpPlan {
        modules: membership
            .iter()
            .map(|(name, _, roots)| (name.clone(), roots.clone()))
            .collect(),
    };
    plan.modules.push((
        "JumpRegionProof".to_owned(),
        vec![
            "GolfCertificates.Jump.source_count".to_owned(),
            "GolfCertificates.Jump.source_gas".to_owned(),
            "GolfCertificates.Jump.compiler_jump_boundary".to_owned(),
        ],
    ));
    proof::check_jump_output(out)?;
    if let Some(parent) = out.parent().filter(|path| !path.as_os_str().is_empty()) {
        fs::create_dir_all(parent)?;
    }
    fs::create_dir(out)
        .with_context(|| format!("use a new output directory: {}", out.display()))?;
    fs::write(out.join("original.hex"), hex::encode(original) + "\n")?;
    fs::write(out.join("candidate.hex"), hex::encode(candidate) + "\n")?;
    for (name, source) in region.sources(original, candidate, rendered.source) {
        fs::write(out.join(name), source)?;
    }
    for (name, source, _) in membership {
        fs::write(out.join(format!("{name}.lean")), source)?;
    }
    let source = JUMP_REGION
        .replace("$entry_pc", &entry_pc.to_string())
        .replace("$exit_pc", &(entry_pc + 11).to_string())
        .replace("$destination", &region.destination.to_string());
    fs::write(out.join("JumpRegionProof.lean"), source)?;
    let lean_version = proof::verify_region(out, proof::RegionKind::PowerJump(&plan))?;
    let report = RegionCertificate {
        claim: "conditional checked-scanner internal path through JUMP",
        original_keccak256: keccak256(original).to_string(),
        candidate_keccak256: keccak256(candidate).to_string(),
        entry_pc,
        exit_pc: usize::from(region.destination),
        pushed_destination: region.destination,
        source_gas_minimum: 33,
        gas_surplus_increase: 2,
        input_stack: "a :: b :: c :: tail (top first; arbitrary 256-bit words)",
        maximum_tail_length: 1018,
        output_stack: "0 :: 0 :: 0 :: c :: (32*a+b modulo 2^256) :: tail".to_owned(),
        interpreter_fuel: "for every natural fuel, each X(fuel+10) reduces to its own X(fuel+1) at the destination",
        state_relation: "arbitrary nonnegative incoming gas surplus; related current/original account maps differing only in designated deployed code; both execution-code links; all other frame fields preserved",
        unproved: [
            "entry reachability",
            "suffix outcomes",
            "whole-contract equivalence",
            "revm correspondence",
            "equivalence with the original opaque upstream scanner",
        ],
        lean_version,
    };
    fs::write(
        out.join("result.json"),
        serde_json::to_string_pretty(&report)? + "\n",
    )?;
    Ok(report)
}

/// Conditions for the canonical twelve-to-nine-instruction mask replacement.
#[derive(Debug, Serialize)]
pub struct MaskRegionCertificate {
    pub claim: &'static str,
    pub original_keccak256: String,
    pub candidate_keccak256: String,
    pub entry_pc: usize,
    pub exit_pc: usize,
    pub source_instruction_count: usize,
    pub candidate_instruction_count: usize,
    pub execution_count_offset_increase: usize,
    pub source_gas_minimum: u64,
    pub candidate_gas_cost: u64,
    pub gas_surplus_increase: u64,
    pub input_stack: &'static str,
    pub maximum_tail_length: usize,
    pub output_stack: &'static str,
    pub interpreter_fuel: &'static str,
    pub state_relation: &'static str,
    pub unproved: [&'static str; 5],
    pub lean_version: String,
}

/// The legacy certificate remains unwrapped and retains its exact JSON fields.
#[derive(Debug, Serialize)]
#[serde(untagged)]
pub enum SelectedRegionCertificate {
    Power(RegionCertificate),
    Mask(MaskRegionCertificate),
}

#[derive(Clone)]
struct ImageNode {
    bytes: String,
    code: String,
    roundtrip: String,
    size: String,
    len: usize,
    children: Option<Box<(ImageNode, ImageNode)>>,
}

struct ImageLeaf {
    side: &'static str,
    base: usize,
    len: usize,
    code: String,
    route: String,
    size: String,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ImageRoutes {
    None,
    Window,
    All,
}

struct RenderedImages {
    source: String,
    leaves: Vec<ImageLeaf>,
    window_start: usize,
    window_end: usize,
    parts: Vec<(&'static str, &'static str, ImageNode)>,
}

struct MaskRegion {
    entry_pc: usize,
}

impl MaskRegion {
    fn select(original: &[u8], candidate: &[u8], entry_pc: usize) -> Result<Self> {
        ensure!(
            original.len() <= MAX_RUNTIME_BYTES && candidate.len() <= MAX_RUNTIME_BYTES,
            "runtime exceeds EIP-170 size limit"
        );
        ensure!(
            original.len() == candidate.len(),
            "region certificates require fixed layout"
        );
        let end = entry_pc
            .checked_add(MASK_BEFORE.len())
            .context("region PC overflow")?;
        ensure!(
            original.get(entry_pc..end) == Some(MASK_BEFORE.as_slice()),
            "unsupported source mask region"
        );
        ensure!(
            candidate.get(entry_pc..end) == Some(MASK_AFTER.as_slice()),
            "unsupported candidate mask region"
        );
        Ok(Self { entry_pc })
    }

    fn sources(&self, original: &[u8], candidate: &[u8]) -> [(&'static str, String); 3] {
        let images = images(original, candidate, self.entry_pc, MASK_BEFORE.len());
        let facts = decoded_facts(
            &MASK_BEFORE,
            &MASK_AFTER,
            self.entry_pc,
            Some(&[
                "Decoded0",
                "Decoded1",
                "Decoded2",
                "Decoded3",
                "Decoded4",
                "Decoded5",
                "Decoded6",
                "Decoded7",
                "Decoded8",
                "Decoded9",
                "Decoded10",
                "Decoded11",
            ]),
        );
        let decode = MASK_DECODE
            .replace("$image_module", "Images")
            .replace("$namespace", "GolfCertificates.Mask")
            .replace("$entry_pc", &self.entry_pc.to_string())
            .replace("$decoded_facts", &facts);
        let region = MASK_REGION
            .replace("$decode_module", "Decode")
            .replace("$namespace", "GolfCertificates.Mask")
            .replace("$entry_pc", &self.entry_pc.to_string())
            .replace("$exit_pc", &(self.entry_pc + MASK_BEFORE.len()).to_string());
        [
            ("Images.lean", images),
            ("Decode.lean", decode),
            ("RegionProof.lean", region),
        ]
    }
}

fn images(original: &[u8], candidate: &[u8], entry_pc: usize, window_len: usize) -> String {
    render_images(original, candidate, entry_pc, window_len, ImageRoutes::None).source
}

fn render_images(
    original: &[u8],
    candidate: &[u8],
    entry_pc: usize,
    window_len: usize,
    routes: ImageRoutes,
) -> RenderedImages {
    let mut definitions = String::new();
    let mut leaves = Vec::new();
    let mut parts = Vec::new();
    for (side, data) in [("original", original), ("candidate", candidate)] {
        let mut route_nodes = Vec::new();
        for (part, block) in [
            ("Prefix", &data[..entry_pc]),
            ("Window", &data[entry_pc..entry_pc + window_len]),
            ("Suffix", &data[entry_pc + window_len..]),
        ] {
            let chunks = if block.is_empty() {
                vec![block]
            } else {
                block.chunks(IMAGE_CHUNK_BYTES).collect()
            };
            let mut nodes = Vec::new();
            for (index, chunk) in chunks.iter().enumerate() {
                let name = format!("{side}{part}Chunk{index}");
                writeln!(definitions, "def {name} : List Nat := {chunk:?}\ndef {name}Code : ByteArray := GolfArtifactBytes.encode {name}\ntheorem {name}Roundtrip : {name}Code.data.toList.map UInt8.toNat = {name} := GolfArtifactBytes.bytes_encode {name} (GolfArtifactBytes.range_of_all {name} (by decide +kernel))\ntheorem {name}Size : {name}Code.data.size = {} := rfl", chunk.len()).unwrap();
                nodes.push(ImageNode {
                    bytes: name.clone(),
                    code: format!("{name}Code"),
                    roundtrip: format!("{name}Roundtrip"),
                    size: format!("{name}Size"),
                    len: chunk.len(),
                    children: None,
                });
            }
            let node = image_tree(&mut definitions, &format!("{side}{part}"), &nodes, &mut 0);
            writeln!(definitions, "def {side}{part}Bytes : List Nat := {}\ndef {side}{part} : ByteArray := {}\ntheorem {side}{part}Roundtrip : {side}{part}.data.toList.map UInt8.toNat = {side}{part}Bytes := {}\ntheorem {side}{part}Size : {side}{part}.data.size = {} := {}\ntheorem {side}{part}ByteSize : {side}{part}.size = {} := {side}{part}Size", node.bytes, node.code, node.roundtrip, block.len(), node.size, block.len()).unwrap();
            if routes == ImageRoutes::All && part != "Window" {
                parts.push((side, part, node.clone()));
            }
            if routes == ImageRoutes::All || (routes == ImageRoutes::Window && part == "Window") {
                let base = match part {
                    "Prefix" => 0,
                    "Window" => entry_pc,
                    "Suffix" => entry_pc + window_len,
                    _ => unreachable!(),
                };
                route_nodes.push((part, base, node));
            }
        }
        let pc = entry_pc;
        writeln!(definitions, "def {side} : List Nat := {side}PrefixBytes ++ {side}WindowBytes ++ {side}SuffixBytes\ndef {side}Code : ByteArray := ⟨{side}Prefix.data ++ {side}Window.data ++ {side}Suffix.data⟩\ntheorem {side}Roundtrip : GolfArtifactBytes.bytes {side}Code = {side} := by\n simp only [GolfArtifactBytes.bytes, {side}Code, {side}, Array.toList_append, List.map_append, {side}PrefixRoundtrip, {side}WindowRoundtrip, {side}SuffixRoundtrip]\ntheorem {side}Size : {side}Code.size = {} := by\n change ({side}Prefix.data ++ {side}Window.data ++ {side}Suffix.data).size = {}\n rw [Array.size_append, Array.size_append, {side}PrefixSize, {side}WindowSize, {side}SuffixSize]\ntheorem {side}WindowFetch (i : Nat) (bound : i < {window_len}) :\n {side}Code.data[{pc}+i]? = {side}Window.data[i]? := by\n change (({side}Prefix.data ++ {side}Window.data) ++ {side}Suffix.data)[{pc}+i]? = _\n rw [Array.append_assoc]\n rw [Array.getElem?_append_right (by rw [{side}PrefixSize]; omega), {side}PrefixSize]\n simp only [Nat.add_sub_cancel_left]\n rw [Array.getElem?_append_left (by rw [{side}WindowSize]; exact bound)]", data.len(), data.len()).unwrap();
        for (part, base, node) in route_nodes {
            match part {
                "Window" => {
                    writeln!(definitions, "theorem {side}WindowRoute : GolfByteRouting.Route {side}Code {entry_pc} {side}Window := by\n constructor\n · rw [{side}Size, {side}WindowByteSize] <;> decide\n · intro i hi\n   exact {side}WindowFetch i (by simpa only [{side}WindowByteSize] using hi)").unwrap();
                }
                "Prefix" => {
                    writeln!(definitions, "theorem {side}PrefixRoute : GolfByteRouting.Route {side}Code 0 {side}Prefix := by\n have outer : GolfByteRouting.Route {side}Code 0 ⟨{side}Prefix.data ++ {side}Window.data⟩ := GolfByteRouting.left _ _\n exact GolfByteRouting.trans _ _ _ 0 0 outer (GolfByteRouting.left _ _)").unwrap();
                }
                "Suffix" => {
                    writeln!(definitions, "theorem {side}SuffixRoute : GolfByteRouting.Route {side}Code {base} {side}Suffix := by\n have h := GolfByteRouting.right (ByteArray.mk ({side}Prefix.data ++ {side}Window.data)) {side}Suffix\n simpa only [ByteArray.size, Array.size_append, {side}PrefixSize, {side}WindowSize] using h").unwrap();
                }
                _ => unreachable!(),
            }
            writeln!(
                definitions,
                "theorem {}Route : GolfByteRouting.Route {side}Code {base} {} := {side}{part}Route",
                node.code, node.code
            )
            .unwrap();
            emit_routes(&mut definitions, side, base, &node, &mut leaves);
        }
    }
    let mut source = IMAGES
        .replace("$namespace", "GolfCertificates")
        .replace("$image_definitions", &definitions);
    if routes != ImageRoutes::None {
        source.insert_str(0, "import ByteRouting\n");
    }
    if routes == ImageRoutes::All {
        source = source.replace("maxRecDepth 131072", "maxRecDepth 4096");
    }
    RenderedImages {
        source,
        leaves,
        window_start: entry_pc,
        window_end: entry_pc + window_len,
        parts,
    }
}

fn decoded_facts(
    original: &[u8],
    candidate: &[u8],
    entry_pc: usize,
    names: Option<&[&str]>,
) -> String {
    let window_len = original.len();
    let mut facts = String::from("open CanonicalFetch\n");
    for (side, code) in [("original", original), ("candidate", candidate)] {
        for (index, instruction) in super::decode(code).iter().enumerate() {
            let op = instruction.bytes[0];
            let width = instruction.bytes.len() - 1;
            let (opcode, argument) = decoded_operation(&instruction.bytes);
            let value = U256::from_be_slice(&instruction.bytes[1..]);
            let pc = entry_pc;
            let offset = instruction.pc;
            let absolute = pc + offset;
            let name =
                names.map_or_else(|| format!("At{absolute}"), |names| names[index].to_owned());
            writeln!(facts, "theorem {side}Opcode{index} : {side}Code.get? {absolute} = some (UInt8.ofNat {op}) := by\n rw [byte_get]\n calc\n  {side}Code.data[{absolute}]? = {side}Window.data[{offset}]? := {side}WindowFetch {offset} (by decide)\n  _ = some (UInt8.ofNat {op}) := by decide +kernel\ntheorem {side}{name} : decode {side}Code (UInt256.ofNat {absolute}) = some (({opcode} : Operation .EVM), {argument}) := by\n unfold decode\n rw [show (UInt256.ofNat {absolute}).toNat = {absolute} by decide, {side}Opcode{index}]").unwrap();
            if width == 0 {
                facts.push_str(" rfl\n");
            } else {
                writeln!(facts, " change some (({opcode} : Operation .EVM), some (uInt256OfByteArray ({side}Code.extract' {} {}), {width})) = some (({opcode} : Operation .EVM), some (UInt256.ofNat {value}, {width}))\n rw [slice_of_window {side}Code {side}Window {pc} {window_len} {} {width}\n   {side}WindowByteSize (by rw [{side}Size] <;> decide) (by decide) (by decide) {side}WindowFetch]\n decide +kernel", absolute+1, absolute+1+width, offset+1).unwrap();
            }
        }
    }
    facts
}

// Decode against bounded routed image leaves, including complete PUSH immediates
// that straddle a physical leaf boundary. Every fetch still names the full code.
fn routed_decoded_facts(
    original: &[u8],
    candidate: &[u8],
    entry: usize,
    exit: usize,
    leaves: &[ImageLeaf],
) -> String {
    let mut facts = String::from("open CanonicalFetch GolfCertificates\n");
    for (side, code) in [("original", original), ("candidate", candidate)] {
        for instruction in super::decode(&code[entry..exit]) {
            let pc = entry + instruction.pc;
            let index = leaves
                .iter()
                .position(|leaf| leaf.side == side && leaf.base <= pc && pc < leaf.base + leaf.len)
                .expect("instruction belongs to the selected image window");
            let leaf = &leaves[index];
            let (window, route, size, len) = if pc + instruction.bytes.len() <= leaf.base + leaf.len
            {
                (
                    leaf.code.clone(),
                    leaf.route.clone(),
                    leaf.size.clone(),
                    leaf.len,
                )
            } else {
                let next = &leaves[index + 1];
                assert_eq!(next.side, side);
                assert_eq!(next.base, leaf.base + leaf.len);
                assert!(pc + instruction.bytes.len() <= next.base + next.len);
                let name = format!("{side}Cross{pc}");
                let len = leaf.len + next.len;
                writeln!(facts, "def {name} : ByteArray := ⟨{}.data ++ {}.data⟩\ntheorem {name}Size : {name}.size = {len} := by\n change ({}.data ++ {}.data).size = {len}\n rw [Array.size_append, {}, {}]\ntheorem {name}Route : GolfByteRouting.Route {side}Code {} {name} := by\n apply GolfByteRouting.adjacent\n · exact {}\n · simpa only [{}] using {}", leaf.code, next.code, leaf.code, next.code, leaf.size, next.size, leaf.base, leaf.route, leaf.size, next.route).unwrap();
                (
                    name.clone(),
                    format!("{name}Route"),
                    format!("{name}Size"),
                    len,
                )
            };
            let byte_size = format!("{side}RoutedSize{pc}");
            writeln!(
                facts,
                "theorem {byte_size} : {window}.size = {len} := {size}"
            )
            .unwrap();
            let size = byte_size;
            let offset = pc - leaf.base;
            let op = instruction.bytes[0];
            let width = instruction.bytes.len() - 1;
            let (opcode, argument) = decoded_operation(&instruction.bytes);
            writeln!(facts, "theorem {side}Opcode{pc} : {side}Code.get? {pc} = some (UInt8.ofNat {op}) := by\n rw [byte_get]\n calc\n  {side}Code.data[{pc}]? = {window}.data[{offset}]? := {route}.fetch {offset} (by rw [{size}]; decide)\n  _ = some (UInt8.ofNat {op}) := by decide +kernel\ntheorem {side}At{pc} : decode {side}Code (UInt256.ofNat {pc}) = some (({opcode} : Operation .EVM), {argument}) := by").unwrap();
            if width == 0 {
                let helper = opcode
                    .strip_prefix("Operation.")
                    .expect("non-push operation name")
                    .to_ascii_lowercase();
                writeln!(facts, " exact GolfOpcodeDecode.decode_{helper} {side}Code (UInt256.ofNat {pc})\n  (by simpa only [show (UInt256.ofNat {pc}).toNat = {pc} by decide] using {side}Opcode{pc})").unwrap();
            } else {
                writeln!(facts, " rw [GolfOpcodeDecode.decode_push{width} {side}Code (UInt256.ofNat {pc})\n  (by simpa only [show (UInt256.ofNat {pc}).toNat = {pc} by decide] using {side}Opcode{pc})]").unwrap();
                let value = U256::from_be_slice(&instruction.bytes[1..]);
                writeln!(facts, " change some (({opcode} : Operation .EVM), some (uInt256OfByteArray ({side}Code.extract' {} {}), {width})) = some (({opcode} : Operation .EVM), some (UInt256.ofNat {value}, {width}))\n rw [slice_of_window {side}Code {window} {} {len} {} {width}\n   {size} (by rw [{side}Size] <;> decide) (by decide) (by decide)\n   (fun i hi => {route}.fetch i (by simpa only [{size}] using hi))]\n decide +kernel", pc+1, pc+1+width, leaf.base, offset+1).unwrap();
            }
        }
    }
    facts
}

fn decoded_operation(bytes: &[u8]) -> (String, String) {
    let width = bytes.len() - 1;
    let opcode = match bytes[0] {
        0x60..=0x7f => format!("Operation.Push .PUSH{width}"),
        op @ 0x90..=0x9f => format!("Operation.SWAP{}", op - 0x8f),
        op => match op {
            0x00 => "Operation.STOP",
            0xf3 => "Operation.RETURN",
            0x02 => "Operation.MUL",
            0x01 => "Operation.ADD",
            0x5f => "Operation.PUSH0",
            0x80 => "Operation.DUP1",
            0x56 => "Operation.JUMP",
            0x52 => "Operation.MSTORE",
            0x1b => "Operation.SHL",
            0x03 => "Operation.SUB",
            0x16 => "Operation.AND",
            0x17 => "Operation.OR",
            0x19 => "Operation.NOT",
            0x10 => "Operation.LT",
            0x1c => "Operation.SHR",
            0x15 => "Operation.ISZERO",
            _ => unreachable!("trusted region template contains only supported opcodes"),
        }
        .to_owned(),
    };
    let argument = if width == 0 {
        "none".to_owned()
    } else {
        format!(
            "some (UInt256.ofNat {}, {width})",
            U256::from_be_slice(&bytes[1..])
        )
    };
    (opcode, argument)
}

fn emit_routes(
    out: &mut String,
    side: &'static str,
    base: usize,
    node: &ImageNode,
    leaves: &mut Vec<ImageLeaf>,
) {
    let route = format!("{}Route", node.code);
    if let Some(children) = &node.children {
        let (left, right) = children.as_ref();
        writeln!(out, "theorem {}Route : GolfByteRouting.Route {side}Code {base} {} := by\n simpa only [Nat.add_zero] using GolfByteRouting.trans {side}Code {} {} {base} 0 {route} (GolfByteRouting.left {} {})", left.code, left.code, node.code, left.code, left.code, right.code).unwrap();
        writeln!(out, "theorem {}Route : GolfByteRouting.Route {side}Code {} {} := by\n have size : {}.size = {} := {}\n simpa only [size] using GolfByteRouting.trans {side}Code {} {} {base} {}.size {route} (GolfByteRouting.right {} {})", right.code, base + left.len, right.code, left.code, left.len, left.size, node.code, right.code, left.code, left.code, right.code).unwrap();
        emit_routes(out, side, base, left, leaves);
        emit_routes(out, side, base + left.len, right, leaves);
    } else {
        leaves.push(ImageLeaf {
            side,
            base,
            len: node.len,
            code: node.code.clone(),
            route,
            size: node.size.clone(),
        });
    }
}

// Each node references its children's proved byte representation and size;
// concrete full arrays never need to normalize to find a matching child lemma.
fn image_tree(
    definitions: &mut String,
    prefix: &str,
    children: &[ImageNode],
    next: &mut usize,
) -> ImageNode {
    if let [child] = children {
        return child.clone();
    }
    let middle = children.len() / 2;
    let left = image_tree(definitions, prefix, &children[..middle], next);
    let right = image_tree(definitions, prefix, &children[middle..], next);
    let name = format!("{prefix}Node{next}");
    *next += 1;
    let len = left.len + right.len;
    writeln!(definitions, "def {name}Bytes : List Nat := {} ++ {}\ndef {name}Code : ByteArray := ⟨{}.data ++ {}.data⟩\ntheorem {name}Roundtrip : {name}Code.data.toList.map UInt8.toNat = {name}Bytes := GolfImageNodes.roundtrip_append {} {} {} {} {} {}\ntheorem {name}Size : {name}Code.data.size = {len} := GolfImageNodes.size_append {} {} {} {} {} {}", left.bytes, right.bytes, left.code, right.code, left.code, right.code, left.bytes, right.bytes, left.roundtrip, right.roundtrip, left.code, right.code, left.len, right.len, left.size, right.size).unwrap();
    ImageNode {
        bytes: format!("{name}Bytes"),
        code: format!("{name}Code"),
        roundtrip: format!("{name}Roundtrip"),
        size: format!("{name}Size"),
        len,
        children: Some(Box::new((left, right))),
    }
}

/// Select one supported literal rewrite and certify its internal canonical region.
/// This accepts no proof text and makes no claim about surrounding instructions.
pub fn certify_selected(
    original: &[u8],
    candidate: &[u8],
    entry_pc: usize,
    out: &Path,
) -> Result<SelectedRegionCertificate> {
    let is_mask = entry_pc
        .checked_add(MASK_BEFORE.len())
        .and_then(|end| original.get(entry_pc..end))
        == Some(MASK_BEFORE.as_slice());
    if !is_mask {
        return certify(original, candidate, entry_pc, out).map(SelectedRegionCertificate::Power);
    }
    let region = MaskRegion::select(original, candidate, entry_pc)?;
    fs::create_dir(out)
        .with_context(|| format!("use a new output directory: {}", out.display()))?;
    fs::write(out.join("original.hex"), hex::encode(original) + "\n")?;
    fs::write(out.join("candidate.hex"), hex::encode(candidate) + "\n")?;
    for (name, source) in region.sources(original, candidate) {
        fs::write(out.join(name), source)?;
    }
    let lean_version = proof::verify_region(out, proof::RegionKind::Mask)?;
    let report = MaskRegionCertificate {
        claim: "conditional internal mask-region residual interpreter calls",
        original_keccak256: keccak256(original).to_string(),
        candidate_keccak256: keccak256(candidate).to_string(),
        entry_pc,
        exit_pc: entry_pc + MASK_BEFORE.len(),
        source_instruction_count: 12,
        candidate_instruction_count: 9,
        execution_count_offset_increase: 3,
        source_gas_minimum: 36,
        candidate_gas_cost: 27,
        gas_surplus_increase: 9,
        input_stack: "a :: tail (top first; arbitrary 256-bit words)",
        maximum_tail_length: 1020,
        output_stack: "high :: (low AND a) :: tail; low = 2^224-1; high = bitwise NOT low",
        interpreter_fuel: "for every natural fuel, source X(fuel+13) and candidate X(fuel+10) reduce to their own X(fuel+1) at the exit",
        state_relation: "arbitrary incoming gas surplus and execution-count offset; related current/original account maps differing only in designated deployed code; both execution-code links; all other frame fields preserved; source execution count gains three more than candidate",
        unproved: [
            "entry reachability",
            "exit instruction execution",
            "suffix outcomes",
            "whole-contract equivalence",
            "revm correspondence",
        ],
        lean_version,
    };
    fs::write(
        out.join("result.json"),
        serde_json::to_string_pretty(&report)? + "\n",
    )?;
    Ok(SelectedRegionCertificate::Mask(report))
}

#[cfg(test)]
mod tests {
    use super::*;
    use revm::primitives::HashMap;

    const ORIGINAL: [u8; 12] = [
        0x60, 32, 0x02, 0x01, 0x90, 0x5f, 0x80, 0x80, 0x61, 0x12, 0x34, 0x56,
    ];
    const CANDIDATE: [u8; 12] = [
        0x60, 5, 0x1b, 0x01, 0x90, 0x5f, 0x80, 0x80, 0x61, 0x12, 0x34, 0x56,
    ];

    fn rendered_image_bytes(source: &str) -> HashMap<String, Vec<u8>> {
        let mut values = HashMap::<String, Vec<u8>>::default();
        for line in source.lines() {
            let Some(definition) = line.strip_prefix("def ") else {
                continue;
            };
            let Some((name, expression)) = definition
                .split_once(" : List Nat := ")
                .or_else(|| definition.split_once(" : ByteArray := "))
            else {
                continue;
            };
            if !name.starts_with("original") && !name.starts_with("candidate") {
                continue;
            }
            let value = if expression.starts_with('[') {
                serde_json::from_str::<Vec<u8>>(expression).unwrap()
            } else if let Some(bytes) = expression.strip_prefix("GolfArtifactBytes.encode ") {
                values[bytes].clone()
            } else {
                expression
                    .trim_matches(['⟨', '⟩'])
                    .split(" ++ ")
                    .flat_map(|child| {
                        values[child.strip_suffix(".data").unwrap_or(child)]
                            .iter()
                            .copied()
                    })
                    .collect()
            };
            assert!(
                values.insert(name.to_owned(), value).is_none(),
                "duplicate image definition"
            );
        }
        values
    }

    #[test]
    fn mask_selection_requires_the_exact_pair_at_the_selected_pc() {
        MaskRegion::select(&MASK_BEFORE, &MASK_AFTER, 0).unwrap();
        for position in 0..MASK_BEFORE.len() {
            let mut wrong = MASK_BEFORE;
            wrong[position] ^= 1;
            assert!(MaskRegion::select(&wrong, &MASK_AFTER, 0).is_err());
            let mut wrong = MASK_AFTER;
            wrong[position] ^= 1;
            assert!(MaskRegion::select(&MASK_BEFORE, &wrong, 0).is_err());
        }
        assert!(MaskRegion::select(&MASK_BEFORE[..17], &MASK_AFTER[..17], 0).is_err());
        assert!(MaskRegion::select(&MASK_BEFORE, &MASK_AFTER[..17], 0).is_err());
        assert!(MaskRegion::select(&MASK_BEFORE, &MASK_AFTER, 1).is_err());
        assert!(MaskRegion::select(&MASK_BEFORE, &MASK_AFTER, usize::MAX).is_err());
        let oversized = vec![0; MAX_RUNTIME_BYTES + 1];
        assert!(MaskRegion::select(&oversized, &oversized, 0).is_err());

        // The selected internal PC is explicit: surrounding instructions and
        // bytes need not match and their execution is outside this certificate.
        for entry in [
            0,
            1,
            19,
            255,
            256,
            257,
            MAX_RUNTIME_BYTES - MASK_BEFORE.len(),
        ] {
            // Distinct chunks make duplicated or reordered child references observable.
            let mut original = (0..entry)
                .map(|index| (index as u8) ^ ((index / IMAGE_CHUNK_BYTES) as u8))
                .collect::<Vec<_>>();
            let mut candidate = original.iter().map(|byte| !byte).collect::<Vec<_>>();
            original.extend(MASK_BEFORE);
            candidate.extend(MASK_AFTER);
            if entry + MASK_BEFORE.len() < MAX_RUNTIME_BYTES {
                original.push(0x5b);
                candidate.push(0);
            }
            let region = MaskRegion::select(&original, &candidate, entry).unwrap();
            let sources = region.sources(&original, &candidate);
            assert_eq!(sources[1].1.matches("theorem originalDecoded").count(), 12);
            assert_eq!(sources[1].1.matches("theorem candidateDecoded").count(), 9);
            assert!(sources[1].1.contains("UInt256.ofNat 4294967295, 5"));
            assert!(sources.iter().all(|(_, source)| !source.contains('$')));
            // Interpret references as emitted, not just leaf declaration order:
            // a duplicated/reordered internal child must alter the reconstructed image.
            let represented = rendered_image_bytes(&sources[0].1);
            for (side, expected) in [("original", &original), ("candidate", &candidate)] {
                assert_eq!(&represented[side], expected, "full {side} natural bytes");
                assert_eq!(
                    &represented[&format!("{side}Code")],
                    expected,
                    "full {side} array bytes"
                );
            }
        }
    }

    #[test]
    fn selected_region_preserves_existing_outputs_before_invoking_lean() {
        let temp = tempfile::tempdir().unwrap();
        let out = temp.path().join("certificate");
        assert!(certify_selected(&MASK_BEFORE, &MASK_BEFORE, 0, &out).is_err());
        assert!(!out.exists());
        fs::create_dir(&out).unwrap();
        fs::write(out.join("result.json"), "existing evidence").unwrap();
        assert!(certify_selected(&MASK_BEFORE, &MASK_AFTER, 0, &out).is_err());
        assert_eq!(
            fs::read_to_string(out.join("result.json")).unwrap(),
            "existing evidence"
        );
    }

    #[test]
    fn selected_power_json_is_exactly_the_legacy_shape() {
        let report = RegionCertificate {
            claim: "legacy",
            original_keccak256: "original".into(),
            candidate_keccak256: "candidate".into(),
            entry_pc: 0,
            exit_pc: 11,
            pushed_destination: 0x1234,
            source_gas_minimum: 25,
            gas_surplus_increase: 2,
            input_stack: "a :: b :: c :: tail",
            maximum_tail_length: 1018,
            output_stack: "legacy".into(),
            interpreter_fuel: "legacy",
            state_relation: "legacy",
            unproved: [
                "entry reachability",
                "exit JUMP execution",
                "suffix outcomes",
                "whole-contract equivalence",
                "revm correspondence",
            ],
            lean_version: "4.22.0".into(),
        };
        let legacy = serde_json::to_value(&report).unwrap();
        let selected = serde_json::to_value(SelectedRegionCertificate::Power(report)).unwrap();
        assert_eq!(legacy, selected);
        assert_eq!(selected["pushed_destination"], 0x1234);
        assert!(selected.get("source_instruction_count").is_none());
        assert!(selected.get("Power").is_none());
    }

    #[test]
    fn selection_rejects_wrong_rewrites_and_partial_regions() {
        let region = Region::select(&ORIGINAL, &CANDIDATE, 0).unwrap();
        assert_eq!(region.destination, 0x1234);
        for (position, value) in [(1, 6), (2, 2), (10, 0x35), (11, 0)] {
            let mut wrong = CANDIDATE;
            wrong[position] = value;
            assert!(Region::select(&ORIGINAL, &wrong, 0).is_err());
        }
        assert!(Region::select(&ORIGINAL, &CANDIDATE[..11], 0).is_err());
        assert!(Region::select(&ORIGINAL[..11], &CANDIDATE[..11], 0).is_err());
        assert!(Region::select(&ORIGINAL, &CANDIDATE, usize::MAX).is_err());
        assert!(Region::select(&CANDIDATE, &CANDIDATE, 0).is_err());
    }

    #[test]
    fn malformed_input_and_existing_outputs_preserve_evidence() {
        let temp = tempfile::tempdir().unwrap();
        let out = temp.path().join("certificate");
        assert!(certify(&ORIGINAL, &ORIGINAL, 0, &out).is_err());
        assert!(!out.exists());
        fs::create_dir(&out).unwrap();
        fs::write(out.join("result.json"), "existing evidence").unwrap();
        assert!(certify(&ORIGINAL, &CANDIDATE, 0, &out).is_err());
        assert_eq!(
            fs::read_to_string(out.join("result.json")).unwrap(),
            "existing evidence"
        );
    }
}
