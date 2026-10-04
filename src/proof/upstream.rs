//! Separate pinned upstream semantics checker; never uses the expression toolchain.
use anyhow::{Context, Result, ensure};
use serde::Deserialize;
use serde_json::json;
use std::{
    collections::BTreeSet,
    env, fs,
    io::Write as _,
    path::{Path, PathBuf},
    process::Command,
    time::{Duration, Instant},
};

use super::{AxiomPolicy, audit_axioms, run_command};

const REVISION: &str = "047f63070309f436b66c61e276ab3b6d1169265a";
// The curated corpus was checked under this cap; do not silently escalate failures.
const MODULE_TIMEOUT: Duration = Duration::from_secs(45);
const MODULES: &[(&str, &str, &[&str])] = &[
    (
        "Driver",
        include_str!("../../lean/upstream/Driver.lean"),
        &[
            "GolfUpstream.X_next",
            "GolfUpstream.X_next_extended",
            "GolfUpstream.step_add",
            "GolfUpstream.step_swap1",
            "GolfUpstream.step_dup1",
            "GolfUpstream.step_push0",
        ],
    ),
    (
        "Power",
        include_str!("../../lean/upstream/Power.lean"),
        &["GolfUpstream.fullX_power_refinement"],
    ),
    (
        "StateRelation",
        include_str!("../../lean/upstream/StateRelation.lean"),
        &[
            "GolfUpstream.frame_push_deployed",
            "GolfUpstream.frame_binary_deployed",
            "GolfUpstream.frame_stop_deployed",
        ],
    ),
    (
        "Transport",
        include_str!("../../lean/upstream/Transport.lean"),
        &[
            "GolfUpstream.deployed_step_transport",
            "GolfUpstream.extended_step_transport",
        ],
    ),
    (
        "Regions",
        include_str!("../../lean/upstream/Regions.lean"),
        &[
            "GolfUpstream.deployed_power_boundary",
            "GolfUpstream.open_region_simulation",
        ],
    ),
    (
        "Bytes",
        include_str!("../../lean/upstream/Bytes.lean"),
        &[
            "GolfArtifactBytes.bytes_encode",
            "GolfArtifactBytes.encode_injective",
        ],
    ),
];

#[derive(Clone, Copy)]
pub(crate) enum RegionKind<'a> {
    Power,
    PowerJump(&'a JumpPlan),
    Mask,
    ChunkedSpan(&'a SpanPlan),
}

/// Ordered modules emitted by the trusted full-image membership generator.
#[derive(Debug)]
pub(crate) struct JumpPlan {
    pub(crate) modules: Vec<(String, Vec<String>)>,
}

impl JumpPlan {
    fn validate(&self) -> Result<()> {
        let mut counters = [0usize; 3];
        let mut seen = BTreeSet::new();
        let mut phase = 0;
        for (position, (name, roots)) in self.modules.iter().enumerate() {
            ensure!(seen.insert(name), "duplicate jump proof module");
            let suffixes: Vec<&str> = match name.as_str() {
                "JumpOriginal" => {
                    ensure!(phase == 0, "misordered source membership module");
                    phase = 1;
                    vec!["original_byte", "original_membership"]
                }
                "JumpCandidate" => {
                    ensure!(phase == 1, "misordered candidate membership module");
                    phase = 2;
                    vec!["candidate_byte", "candidate_membership"]
                }
                "JumpMembership" => {
                    ensure!(phase == 2, "misordered membership certificate");
                    phase = 3;
                    vec!["original_membership", "candidate_membership"]
                }
                "JumpRegionProof" => {
                    ensure!(
                        phase == 3 && position + 1 == self.modules.len(),
                        "jump boundary must be the final generated module"
                    );
                    phase = 4;
                    ensure!(
                        roots
                            == &[
                                "GolfCertificates.Jump.source_count".to_owned(),
                                "GolfCertificates.Jump.source_gas".to_owned(),
                                "GolfCertificates.Jump.compiler_jump_boundary".to_owned()
                            ],
                        "unexpected jump boundary roots"
                    );
                    continue;
                }
                _ => {
                    ensure!(phase < 2, "membership nodes after final side certificate");
                    let family = ["JumpCover", "JumpChunk", "JumpNode"]
                        .iter()
                        .position(|prefix| name.starts_with(*prefix))
                        .context("unknown generated jump module")?;
                    let prefix = ["JumpCover", "JumpChunk", "JumpNode"][family];
                    ensure!(
                        name == &format!("{prefix}{}", counters[family]),
                        "jump module numbers must be contiguous and ordered"
                    );
                    counters[family] += 1;
                    let endings = match family {
                        0 => vec!["size", "route"],
                        1 if roots.len() == 3 => vec!["size", "complete", "route"],
                        1 => vec!["size", "complete", "local", "route"],
                        _ => vec!["size", "complete", "route"],
                    };
                    let expected: Vec<_> = endings
                        .iter()
                        .map(|ending| format!("GolfCertificates.JumpMembership.{name}_{ending}"))
                        .collect();
                    ensure!(roots == &expected, "unexpected jump node roots");
                    continue;
                }
            };
            let expected: Vec<_> = suffixes
                .iter()
                .map(|suffix| format!("GolfCertificates.JumpMembership.{suffix}"))
                .collect();
            ensure!(roots == &expected, "unexpected jump membership roots");
        }
        ensure!(phase == 4 && counters[1] >= 2, "incomplete jump proof plan");
        Ok(())
    }

    fn generated_modules(&self) -> Vec<(String, Vec<String>)> {
        let mut modules = power_generated_modules();
        modules.extend(self.modules.clone());
        modules
    }
}

fn power_generated_modules() -> Vec<(String, Vec<String>)> {
    vec![
        (
            "Images".to_owned(),
            [
                "originalRoundtrip",
                "candidateRoundtrip",
                "originalWindowFetch",
                "candidateWindowFetch",
            ]
            .map(|name| format!("GolfCertificates.{name}"))
            .to_vec(),
        ),
        ("Decode".to_owned(), vec![]),
        (
            "RegionProof".to_owned(),
            vec![
                "GolfCertificates.Region.compilerTrace".to_owned(),
                "GolfCertificates.Region.compiler_region_boundary".to_owned(),
            ],
        ),
    ]
}

/// The generator and verifier share one ordered, complete composition tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SpanNode {
    Leaf(usize),
    Compose(usize),
}

#[derive(Debug)]
pub(crate) struct SpanPlan {
    pub(crate) leaf_count: usize,
    pub(crate) compositions: Vec<(SpanNode, SpanNode)>,
}

impl SpanPlan {
    fn validate(&self) -> Result<()> {
        ensure!(self.leaf_count > 0, "empty span proof plan");
        ensure!(
            self.compositions.len() == self.leaf_count - 1,
            "incomplete span composition tree"
        );
        let mut leaves = vec![0usize; self.leaf_count];
        let mut parents = vec![0usize; self.compositions.len()];
        let mut ranges: Vec<(usize, usize)> = Vec::new();
        for (index, (left, right)) in self.compositions.iter().enumerate() {
            for child in [left, right] {
                match *child {
                    SpanNode::Leaf(leaf) => {
                        let count = leaves.get_mut(leaf).context("unknown span leaf")?;
                        *count += 1;
                    }
                    SpanNode::Compose(parent) => {
                        ensure!(
                            parent < index,
                            "span composition is not in dependency order"
                        );
                        parents[parent] += 1;
                    }
                }
            }
            let range = |node: &SpanNode| match *node {
                SpanNode::Leaf(leaf) => (leaf, leaf + 1),
                SpanNode::Compose(parent) => ranges[parent],
            };
            let (left, right) = (range(left), range(right));
            ensure!(
                left.1 == right.0,
                "span composition children are not contiguous and ordered"
            );
            ranges.push((left.0, right.1));
        }
        if self.leaf_count == 1 {
            leaves[0] = 1;
        } else {
            ensure!(
                ranges.last() == Some(&(0, self.leaf_count)),
                "span composition does not cover every leaf in order"
            );
            *parents.last_mut().unwrap() = 1;
        }
        ensure!(
            leaves.iter().chain(&parents).all(|count| *count == 1),
            "span proof tree must use every child exactly once"
        );
        Ok(())
    }

    fn modules(&self) -> Vec<(String, Vec<String>)> {
        let mut modules = vec![(
            "Images".to_owned(),
            [
                "originalRoundtrip",
                "candidateRoundtrip",
                "originalWindowFetch",
                "candidateWindowFetch",
            ]
            .map(|name| format!("GolfCertificates.{name}"))
            .to_vec(),
        )];
        for leaf in 0..self.leaf_count {
            modules.push((
                format!("TraceLeaf{leaf}"),
                vec![format!("GolfSpanTrace{leaf}.summary")],
            ));
            modules.push((
                format!("DecodeLeaf{leaf}"),
                vec![
                    format!("GolfSpanDecode{leaf}.originalDecoded"),
                    format!("GolfSpanDecode{leaf}.candidateDecoded"),
                ],
            ));
            modules.push((
                format!("BindLeaf{leaf}"),
                vec![format!("GolfSpanBind{leaf}.summary")],
            ));
        }
        for node in 0..self.compositions.len() {
            modules.push((
                format!("Compose{node}"),
                vec![format!("GolfSpanCompose{node}.summary")],
            ));
        }
        modules.push((
            "RegionProof".to_owned(),
            [
                "source_gas",
                "bound_trace",
                "source_stack",
                "source_count",
                "source_pc",
                "span_boundary",
            ]
            .map(|name| format!("GolfCertificates.Span.{name}"))
            .to_vec(),
        ));
        modules
    }
}

const POWER_MODULES: &[(&str, &str, &[&str])] = &[(
    "PowerRegion",
    include_str!("../../lean/upstream/PowerRegion.lean"),
    &[
        "GolfPowerRegion.pc_add",
        "GolfPowerRegion.compilerExitPC",
        "GolfPowerRegion.compilerExitStack",
        "GolfPowerRegion.compilerExitGas",
        "GolfPowerRegion.compilerTrace",
        "GolfPowerRegion.compiler_region_boundary",
    ],
)];

const JUMP_MODULES: &[(&str, &str, &[&str])] = &[
    (
        "ByteRouting",
        include_str!("../../lean/upstream/ByteRouting.lean"),
        &[
            "GolfByteRouting.left",
            "GolfByteRouting.right",
            "GolfByteRouting.trans",
            "GolfByteRouting.adjacent",
        ],
    ),
    (
        "LayoutScanner",
        concat!(
            include_str!("../../lean/LayoutScanner.lean"),
            "\n#print axioms GolfLayout.scan\n#print axioms GolfWindowArtifact.jumpTargets\n"
        ),
        &["GolfLayout.scan", "GolfWindowArtifact.jumpTargets"],
    ),
    (
        "CheckedScannerSpec",
        include_str!("../../lean/upstream/CheckedScannerSpec.lean"),
        &[
            "GolfScannerSpec.next_progress",
            "GolfScannerSpec.scan_sound",
            "GolfScannerSpec.member_boundary",
            "GolfScannerSpec.boundary_decoded",
            "GolfScannerSpec.boundary_not_before",
        ],
    ),
    (
        "CheckedScannerComplete",
        include_str!("../../lean/upstream/CheckedScannerComplete.lean"),
        &[
            "GolfScannerSpec.parsed_present_in_bounds",
            "GolfScannerSpec.scan_complete",
            "GolfScannerSpec.scan_complete_trace",
            "GolfScannerSpec.full_image_complete",
        ],
    ),
    (
        "CheckedParserBase",
        include_str!("../../lean/upstream/CheckedParserBase.lean"),
        &[],
    ),
    (
        "CheckedParserTable0",
        include_str!("../../lean/upstream/CheckedParserTable0.lean"),
        &["GolfParserFacts.parser_table0"],
    ),
    (
        "CheckedParserTable1",
        include_str!("../../lean/upstream/CheckedParserTable1.lean"),
        &["GolfParserFacts.parser_table1"],
    ),
    (
        "CheckedParserTable2",
        include_str!("../../lean/upstream/CheckedParserTable2.lean"),
        &["GolfParserFacts.parser_table2"],
    ),
    (
        "CheckedParserTable3",
        include_str!("../../lean/upstream/CheckedParserTable3.lean"),
        &["GolfParserFacts.parser_table3"],
    ),
    (
        "CheckedParserFacts",
        include_str!("../../lean/upstream/CheckedParserFacts.lean"),
        &[
            "GolfParserFacts.parser_table",
            "GolfParserFacts.parser_agrees",
            "GolfParserFacts.parser_present",
            "GolfParserFacts.parser_width",
            "GolfParserFacts.parser_jumpdest",
        ],
    ),
    (
        "CheckedScannerBridge",
        include_str!("../../lean/upstream/CheckedScannerBridge.lean"),
        &[
            "GolfScannerBridge.bytes_drop_head",
            "GolfScannerBridge.targets_of_success",
            "GolfScannerBridge.full_image_targets",
        ],
    ),
    (
        "CheckedRevisedScannerProof",
        include_str!("../../lean/upstream/CheckedRevisedScannerProof.lean"),
        &[
            "RevisedScannerProof.checked_of_scan",
            "RevisedScannerProof.checked_complete",
            "RevisedScannerProof.bounded_wrapper",
            "RevisedScannerProof.bounded_table_exists",
            "RevisedScannerProof.outside_fallback",
        ],
    ),
    (
        "CheckedTableEquality",
        include_str!("../../lean/upstream/CheckedTableEquality.lean"),
        &[
            "RevisedTableEquality.table_of_layout",
            "RevisedTableEquality.tables_equal",
        ],
    ),
    (
        "CheckedCompleteSegments",
        include_str!("../../lean/upstream/CheckedCompleteSegments.lean"),
        &[
            "GolfLayout.scanAux_suffix",
            "GolfLayout.scanAux_sufficient",
            "GolfLayout.complete_steps_le_length",
            "GolfLayout.scan_chunks",
            "GolfLayout.chunkSteps_le_length",
            "GolfLayout.scan_complete_chunks",
        ],
    ),
    (
        "CheckedAlignedSplice",
        include_str!("../../lean/upstream/CheckedAlignedSplice.lean"),
        &[
            "GolfAlignedSplice.targets_append",
            "GolfAlignedSplice.scan_two",
            "GolfAlignedSplice.targets_splice",
            "GolfAlignedSplice.targets_splice_empty",
        ],
    ),
    (
        "CheckedBoundaryMembership",
        include_str!("../../lean/upstream/CheckedBoundaryMembership.lean"),
        &[
            "GolfBoundaryMembership.layout_member",
            "GolfBoundaryMembership.contains_of_binding",
            "GolfBoundaryMembership.contains_at_boundary",
        ],
    ),
    (
        "CheckedRouteMembership",
        include_str!("../../lean/upstream/CheckedRouteMembership.lean"),
        &[
            "GolfRouteMembership.byte_get",
            "GolfRouteMembership.route_take",
            "GolfRouteMembership.route_binding",
            "GolfRouteMembership.contains_of_route",
        ],
    ),
    (
        "CheckedRouteSupport",
        include_str!("../../lean/upstream/CheckedRouteSupport.lean"),
        &[
            "SpliceSupport.complete_append",
            "SpliceSupport.complete_bytes_append",
            "SpliceSupport.append_size",
            "GolfJumpRoute.empty_route",
        ],
    ),
    (
        "Jump",
        include_str!("../../lean/upstream/Jump.lean"),
        &[
            "GolfJump.cost_jump",
            "GolfJump.mem_jump",
            "GolfJump.step_jump",
            "GolfJump.X_jump",
            "GolfJump.jump_preserves",
            "GolfJump.paired_jump",
            "GolfJump.compiler_jump_count",
        ],
    ),
];

const MASK_MODULES: &[(&str, &str, &[&str])] = &[
    (
        "CountOffset",
        include_str!("../../lean/upstream/CountOffset.lean"),
        &[
            "GolfCountOffset.of_exact",
            "GolfCountOffset.zero_to_exact",
            "GolfCountOffset.step_sub",
            "GolfCountOffset.step_and",
            "GolfCountOffset.step_not",
        ],
    ),
    (
        "MaskSupport",
        include_str!("../../lean/upstream/MaskSupport.lean"),
        &[
            "CanonicalMaskWindow.word_add_nat",
            "CanonicalMaskWindow.snapshot_push",
            "CanonicalMaskWindow.snapshot_binary",
            "CanonicalMaskWindow.spend_nat",
            "CanonicalMaskWindow.X_next_extra",
        ],
    ),
    (
        "CanonicalMask",
        include_str!("../../lean/upstream/CanonicalMask.lean"),
        &[
            "CanonicalMaskWindow.before_execution",
            "CanonicalMaskWindow.after_execution",
            "CanonicalMaskWindow.canonical_mask_replacement",
            "CanonicalMaskWindow.mask_identity",
            "CanonicalMaskWindow.final_relation",
        ],
    ),
];

const SPAN_MODULES: &[(&str, &str, &[&str])] = &[
    (
        "OffsetPower",
        include_str!("../../lean/upstream/OffsetPower.lean"),
        &[
            "GolfComposition.offset_pc",
            "GolfComposition.offset_stack",
            "GolfComposition.offset_power_boundary",
        ],
    ),
    (
        "OffsetTransport",
        include_str!("../../lean/upstream/OffsetTransport.lean"),
        &[
            "GolfComposition.offset_step_transport",
            "GolfComposition.offset_extended_transport",
            "GolfComposition.offset_extra_transport",
        ],
    ),
    (
        "MixedTrace",
        include_str!("../../lean/upstream/MixedTrace.lean"),
        &[
            "GolfComposition.fuel_gap",
            "GolfComposition.mixed_simulation",
        ],
    ),
];

const CHUNK_MODULES: &[(&str, &str, &[&str])] = &[
    (
        "OpcodeDecode",
        include_str!("../../lean/upstream/OpcodeDecode.lean"),
        &[
            "GolfOpcodeDecode.decode_mul",
            "GolfOpcodeDecode.decode_shl",
            "GolfOpcodeDecode.decode_add",
            "GolfOpcodeDecode.decode_swap1",
            "GolfOpcodeDecode.decode_push0",
            "GolfOpcodeDecode.decode_dup1",
            "GolfOpcodeDecode.decode_sub",
            "GolfOpcodeDecode.decode_and",
            "GolfOpcodeDecode.decode_not",
            "GolfOpcodeDecode.decode_push1",
            "GolfOpcodeDecode.decode_push2",
            "GolfOpcodeDecode.decode_push3",
            "GolfOpcodeDecode.decode_push4",
            "GolfOpcodeDecode.decode_push5",
            "GolfOpcodeDecode.decode_push6",
            "GolfOpcodeDecode.decode_push7",
            "GolfOpcodeDecode.decode_push8",
            "GolfOpcodeDecode.decode_push9",
            "GolfOpcodeDecode.decode_push10",
            "GolfOpcodeDecode.decode_push11",
            "GolfOpcodeDecode.decode_push12",
            "GolfOpcodeDecode.decode_push13",
            "GolfOpcodeDecode.decode_push14",
            "GolfOpcodeDecode.decode_push15",
            "GolfOpcodeDecode.decode_push16",
            "GolfOpcodeDecode.decode_push17",
            "GolfOpcodeDecode.decode_push18",
            "GolfOpcodeDecode.decode_push19",
            "GolfOpcodeDecode.decode_push20",
            "GolfOpcodeDecode.decode_push21",
            "GolfOpcodeDecode.decode_push22",
            "GolfOpcodeDecode.decode_push23",
            "GolfOpcodeDecode.decode_push24",
            "GolfOpcodeDecode.decode_push25",
            "GolfOpcodeDecode.decode_push26",
            "GolfOpcodeDecode.decode_push27",
            "GolfOpcodeDecode.decode_push28",
            "GolfOpcodeDecode.decode_push29",
            "GolfOpcodeDecode.decode_push30",
            "GolfOpcodeDecode.decode_push31",
            "GolfOpcodeDecode.decode_push32",
        ],
    ),
    (
        "PureBounds",
        include_str!("../../lean/upstream/PureBounds.lean"),
        &[
            "GolfPureBounds.bounds_push",
            "GolfPureBounds.bounds_push0",
            "GolfPureBounds.bounds_mul",
            "GolfPureBounds.bounds_shl",
            "GolfPureBounds.bounds_add",
            "GolfPureBounds.bounds_swap1",
            "GolfPureBounds.bounds_dup1",
            "GolfPureBounds.canonical_step_push",
            "GolfPureBounds.canonical_step_push0",
            "GolfPureBounds.canonical_step_mul",
            "GolfPureBounds.canonical_step_shl",
            "GolfPureBounds.canonical_step_add",
            "GolfPureBounds.canonical_step_swap1",
            "GolfPureBounds.canonical_step_dup1",
            "GolfPureBounds.remaining_enough",
            "GolfPureBounds.remaining_sub",
            "GolfPureBounds.bounds_sub",
            "GolfPureBounds.bounds_and",
            "GolfPureBounds.bounds_not",
            "GolfPureBounds.canonical_step_sub",
            "GolfPureBounds.canonical_step_and",
            "GolfPureBounds.canonical_step_not",
        ],
    ),
    (
        "TraceChunk",
        include_str!("../../lean/upstream/TraceChunk.lean"),
        &[
            "GolfChunk.identity",
            "GolfChunk.append",
            "GolfChunk.recover",
            "GolfChunk.fuel_gap",
            "GolfChunk.mask",
            "GolfChunk.power",
            "GolfChunk.same",
            "GolfChunk.extended",
            "GolfChunk.extra",
        ],
    ),
    (
        "ChunkSummary",
        include_str!("../../lean/upstream/ChunkSummary.lean"),
        &[
            "GolfChunkSummary.successor_bounds",
            "GolfChunkSummary.compose",
            "GolfChunkSummary.composed_count",
            "GolfChunkSummary.composed_pc",
            "GolfChunkSummary.composed_stack",
            "GolfChunkSummary.composed_gas",
            "GolfChunkSummary.composed_trace",
        ],
    ),
    (
        "ByteRouting",
        include_str!("../../lean/upstream/ByteRouting.lean"),
        &[
            "GolfByteRouting.left",
            "GolfByteRouting.right",
            "GolfByteRouting.trans",
            "GolfByteRouting.adjacent",
        ],
    ),
];

#[derive(Deserialize)]
struct Manifest {
    #[serde(rename = "packagesDir")]
    packages_dir: String,
    packages: Vec<Package>,
}

#[derive(Deserialize)]
struct Package {
    name: String,
    rev: String,
    #[serde(rename = "type")]
    kind: String,
    #[serde(rename = "subDir")]
    sub_dir: Option<String>,
}

fn upstream_root() -> Result<PathBuf> {
    env::var_os("EVM_GOLF_UPSTREAM")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join(".tools/upstream"))
        .canonicalize()
        .context("upstream toolchain unavailable; run scripts/setup-upstream.sh")
}

/// Reject installation-local output before any certificate files are written.
pub(crate) fn check_jump_output(out: &Path) -> Result<()> {
    check_output_separation(out, &upstream_root()?.join("checked-scanner"))
}

fn check_output_separation(out: &Path, installation: &Path) -> Result<()> {
    let installation = installation
        .canonicalize()
        .context("checked scanner unavailable; run scripts/setup-upstream.sh --checked-scanner")?;
    // Resolve the nearest existing parent before creating anything. Missing
    // components must be ordinary names: unresolved '..' could create an
    // installation-local directory before traversing back outside it.
    let mut parent = out
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."))
        .to_path_buf();
    let mut missing = Vec::new();
    while !parent
        .try_exists()
        .context("checking certificate output parent")?
    {
        ensure!(
            !parent.is_symlink(),
            "certificate output parent is a dangling symlink"
        );
        missing.push(
            parent
                .file_name()
                .context("missing output parents must not contain unresolved '..'")?
                .to_owned(),
        );
        parent.pop();
        if parent.as_os_str().is_empty() {
            parent.push(".");
        }
    }
    let mut resolved = parent
        .canonicalize()
        .context("resolving certificate output parent")?;
    for component in missing.iter().rev() {
        resolved.push(component);
    }
    resolved.push(
        out.file_name()
            .context("certificate output must name a new directory")?,
    );
    ensure!(
        !resolved.starts_with(&installation),
        "certificate output must be outside the checked-scanner installation"
    );
    Ok(())
}

/// Called only after the trusted generator writes its fixed certificate files.
pub(crate) fn verify_region(out: &Path, kind: RegionKind<'_>) -> Result<String> {
    let out = out.canonicalize()?;
    let planned = match kind {
        RegionKind::ChunkedSpan(plan) => {
            plan.validate()?;
            Some(plan.modules())
        }
        RegionKind::PowerJump(plan) => {
            plan.validate()?;
            Some(plan.generated_modules())
        }
        _ => None,
    };
    if let Some(modules) = &planned {
        let expected: BTreeSet<_> = modules
            .iter()
            .map(|(name, _)| format!("{name}.lean"))
            .collect();
        let mut found = BTreeSet::new();
        for entry in fs::read_dir(&out)? {
            let path = entry?.path();
            if path.extension().is_some_and(|ext| ext == "lean") {
                ensure!(
                    path.is_file(),
                    "planned proof module is not a file: {}",
                    path.display()
                );
                found.insert(
                    path.file_name()
                        .and_then(|name| name.to_str())
                        .context("invalid span module filename")?
                        .to_owned(),
                );
            }
        }
        ensure!(
            found == expected,
            "generated module set differs from the complete proof plan"
        );
    }

    for entry in fs::read_dir(&out)? {
        let path = entry?.path();
        ensure!(
            path.extension()
                .is_none_or(|ext| ext != "olean" && ext != "ilean"),
            "proof output contains cached Lean artifacts: {}",
            path.display()
        );
    }
    let root = upstream_root()?;
    let lean = root
        .join("lean/bin/lean")
        .canonicalize()
        .context("missing pinned upstream Lean executable; run scripts/setup-upstream.sh")?;
    let semantics = root
        .join("semantics")
        .canonicalize()
        .context("missing pinned upstream semantics checkout; run scripts/setup-upstream.sh")?;
    let mut version_command = Command::new(&lean);
    version_command.arg("--version");
    sanitize(&mut version_command);
    let version = capture(&mut version_command, &out.join("environment-version.log"))?;
    ensure!(
        version.trim().starts_with("Lean (version 4.22.0,"),
        "expected pinned upstream Lean 4.22.0, got {}",
        version.trim()
    );
    check_checkout(&semantics, REVISION, &out, "semantics")?;
    ensure!(
        fs::read_to_string(semantics.join("lean-toolchain"))?.trim() == "leanprover/lean4:v4.22.0",
        "wrong upstream lean-toolchain"
    );
    let manifest: Manifest =
        serde_json::from_slice(&fs::read(semantics.join("lake-manifest.json"))?)?;
    validate_manifest(&manifest)?;
    let mut paths = vec![out.clone()];
    let mut packages = Vec::new();
    for package in &manifest.packages {
        let checkout = semantics
            .join(&manifest.packages_dir)
            .join(&package.name)
            .canonicalize()?;
        check_checkout(&checkout, &package.rev, &out, &package.name)?;
        // Lake includes build paths for locked packages even when their modules
        // are unused and have not been built. Lean rejects missing required imports.
        paths.push(checkout.join(".lake/build/lib/lean"));
        packages.push(json!({"name": package.name, "revision": package.rev, "checkout": checkout}));
    }
    let checked_profile = if matches!(kind, RegionKind::PowerJump(_)) {
        let profile = check_scanner_profile(&root, &lean, &semantics, &out)?;
        paths = vec![out.clone()];
        paths.extend(env::split_paths(
            profile["inputs"]["lean_path"]
                .as_str()
                .context("checked scanner lookup path missing")?,
        ));
        Some(profile)
    } else {
        paths.push(
            semantics
                .join(".lake/build/lib/lean")
                .canonicalize()
                .context("missing upstream semantics build; run scripts/setup-upstream.sh")?,
        );
        None
    };
    if checked_profile.is_none() {
        paths.push(
            root.join("lean/lib/lean")
                .canonicalize()
                .context("missing pinned Lean standard library")?,
        );
    }
    let search_path = env::join_paths(&paths)?;
    let mut environment = json!({
        "lean_version": version.trim(), "lean": lean, "upstream_revision": REVISION,
        "semantics": semantics, "packages": packages, "lean_path": paths,
        "module_timeout_seconds": MODULE_TIMEOUT.as_secs(),
        "claim_scope": "internal region boundary and residual canonical X calls; no whole-contract equivalence",
        "trust": "installed Lean and pinned upstream/dependency build artifacts are trusted; local certificate support modules are rebuilt from embedded sources"
    });
    if let Some(profile) = &checked_profile {
        environment["semantics_profile"] = json!({
            "identity": "evm-golf-checked-scanner",
            "base_revision": REVISION,
            "overlay_sha256": profile["inputs"]["overlay_sha256"],
            "revised_source_sha256": profile["inputs"]["revised_source_sha256"],
            "semantics_object_sha256": profile["build"]["object_sha256"],
            "manifest": root.join("checked-scanner/manifest.json"),
            "original_opaque_scanner_equality_proved": false
        });
    }
    fs::write(
        out.join("environment.json"),
        serde_json::to_vec_pretty(&environment)?,
    )?;
    let additional = match kind {
        RegionKind::Power | RegionKind::PowerJump(_) => POWER_MODULES,
        RegionKind::Mask | RegionKind::ChunkedSpan(_) => MASK_MODULES,
    };
    let composition = match kind {
        RegionKind::ChunkedSpan(_) => SPAN_MODULES,
        RegionKind::Power | RegionKind::PowerJump(_) | RegionKind::Mask => &[],
    };
    let chunks = match kind {
        RegionKind::ChunkedSpan(_) => CHUNK_MODULES,
        _ => &[],
    };
    let jump_modules = if matches!(kind, RegionKind::PowerJump(_)) {
        JUMP_MODULES
    } else {
        &[]
    };
    for (name, source, _) in MODULES
        .iter()
        .chain(additional)
        .chain(composition)
        .chain(chunks)
        .chain(jump_modules)
    {
        let path = out.join(format!("{name}.lean"));
        ensure!(
            !path.exists(),
            "refusing to overwrite support source {}",
            path.display()
        );
        fs::write(path, source)?;
    }
    let region_roots: &[&str] = match kind {
        RegionKind::Power | RegionKind::PowerJump(_) => &[
            "GolfCertificates.Region.compilerTrace",
            "GolfCertificates.Region.compiler_region_boundary",
        ],
        RegionKind::Mask => &[
            "GolfCertificates.Mask.beforeDecoded",
            "GolfCertificates.Mask.afterDecoded",
            "GolfCertificates.Mask.compiler_mask_boundary",
        ],
        RegionKind::ChunkedSpan(_) => &[
            "GolfCertificates.Span.source_gas",
            "GolfCertificates.Span.bound_trace",
            "GolfCertificates.Span.source_stack",
            "GolfCertificates.Span.source_count",
            "GolfCertificates.Span.source_pc",
            "GolfCertificates.Span.span_boundary",
        ],
    };
    let image_roots: &[&str] = &[
        "GolfCertificates.originalRoundtrip",
        "GolfCertificates.candidateRoundtrip",
        "GolfCertificates.originalWindowFetch",
        "GolfCertificates.candidateWindowFetch",
    ];
    let generated: &[(&str, &[&str])] = match kind {
        RegionKind::ChunkedSpan(_) | RegionKind::PowerJump(_) => &[],
        RegionKind::Power | RegionKind::Mask => &[
            ("Images", image_roots),
            ("Decode", &[]),
            ("RegionProof", region_roots),
        ],
    };
    let generated = match kind {
        RegionKind::ChunkedSpan(plan) => plan.modules(),
        RegionKind::PowerJump(plan) => plan.generated_modules(),
        _ => generated
            .iter()
            .map(|(name, roots)| {
                (
                    (*name).to_owned(),
                    roots.iter().map(|root| (*root).to_owned()).collect(),
                )
            })
            .collect(),
    };
    // Diagnostic measurements never substitute for compilation and the axiom audit.
    let mut measurements = if matches!(kind, RegionKind::ChunkedSpan(_) | RegionKind::PowerJump(_))
    {
        Some(
            fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(out.join("module-checks.jsonl"))?,
        )
    } else {
        None
    };
    for (name, expected) in MODULES
        .iter()
        .chain(additional)
        .chain(composition)
        .chain(chunks)
        .chain(jump_modules)
        .map(|(name, _, roots)| {
            (
                (*name).to_owned(),
                roots
                    .iter()
                    .map(|root| (*root).to_owned())
                    .collect::<Vec<_>>(),
            )
        })
        .chain(generated)
    {
        let log = out.join(format!("{name}.log"));
        let mut command = Command::new(&lean);
        sanitize(&mut command);
        command
            .current_dir(&out)
            .env("LEAN_PATH", &search_path)
            .args(["-o", &format!("{name}.olean"), &format!("{name}.lean")]);
        let started = Instant::now();
        let compiled = run_command(&mut command, &log, started + MODULE_TIMEOUT)
            .with_context(|| format!("upstream module {name} failed; see {}", log.display()));
        let compile_ms = started.elapsed().as_millis();
        let compilation_succeeded = compiled.is_ok();
        let checked = compiled.and_then(|()| {
            audit_axioms(
                &fs::read_to_string(&log)?,
                &expected,
                AxiomPolicy::Foundational,
            )
            .with_context(|| format!("upstream axiom audit failed; see {}", log.display()))
        });
        if let Some(measurements) = &mut measurements {
            let record = json!({
                "module": name,
                "compile_ms": compile_ms,
                "source_bytes": fs::metadata(out.join(format!("{name}.lean")))?.len(),
                "object_bytes": fs::metadata(out.join(format!("{name}.olean"))).ok().map(|meta| meta.len()),
                "expected_roots": expected,
                "compilation_succeeded": compilation_succeeded,
                "accepted": checked.is_ok()
            });
            writeln!(measurements, "{record}")?;
        }
        checked?;
    }
    Ok(version.trim().to_owned())
}

fn check_scanner_profile(
    root: &Path,
    lean: &Path,
    semantics: &Path,
    out: &Path,
) -> Result<serde_json::Value> {
    let trusted = out.join(".checked-scanner-validation");
    fs::create_dir(&trusted)?;
    fs::create_dir(trusted.join("scripts"))?;
    fs::create_dir_all(trusted.join("lean/checked-scanner"))?;
    let script = trusted.join("scripts/setup-checked-scanner.py");
    fs::write(
        &script,
        include_str!("../../scripts/setup-checked-scanner.py"),
    )?;
    fs::write(
        trusted.join("lean/checked-scanner/overlay.json"),
        include_str!("../../lean/checked-scanner/overlay.json"),
    )?;
    let installation = root.join("checked-scanner");
    let mut command = Command::new("python3");
    sanitize(&mut command);
    command
        .arg(script)
        .arg("--semantics")
        .arg(semantics)
        .arg("--lean")
        .arg(lean)
        .arg("--out")
        .arg(&installation)
        .arg("--check");
    capture(&mut command, &out.join("environment-checked-scanner.log")).context(
        "checked scanner unavailable or changed; run scripts/setup-upstream.sh --checked-scanner",
    )?;
    let profile: serde_json::Value =
        serde_json::from_slice(&fs::read(installation.join("manifest.json"))?)?;
    ensure!(
        profile["inputs"]["base_revision"] == REVISION
            && profile["inputs"]["overlay_sha256"]
                == "b3c6fd1b1aea261f00fc7a6306581bc0bbcb922c87f09ced26e2eb219a6dd9d8"
            && profile["inputs"]["revised_source_sha256"]
                == "3d94b61e0b1354a6b7d2992f17e8599a311ae5e5a9feb1d62596dfeadbd0a336",
        "unexpected checked-scanner semantics identity"
    );
    Ok(profile)
}

fn validate_manifest(manifest: &Manifest) -> Result<()> {
    ensure!(
        manifest.packages_dir == ".lake/packages",
        "unexpected upstream package directory"
    );
    let mut names = BTreeSet::new();
    for package in &manifest.packages {
        ensure!(
            package.kind == "git"
                && package.sub_dir.is_none()
                && !package.name.is_empty()
                && package
                    .name
                    .bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-')
                && package.rev.len() == 40
                && package
                    .rev
                    .bytes()
                    .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
                && names.insert(&package.name),
            "unsupported or duplicate locked upstream package"
        );
    }
    ensure!(!names.is_empty(), "empty upstream package manifest");
    Ok(())
}

fn sanitize(command: &mut Command) {
    for (name, _) in env::vars_os() {
        let name_text = name.to_string_lossy();
        if name_text.starts_with("LEAN_")
            || name_text.starts_with("LAKE_")
            || name_text.starts_with("GIT_")
            || name == "LEAN"
        {
            command.env_remove(name);
        }
    }
}

fn capture(command: &mut Command, log: &Path) -> Result<String> {
    run_command(command, log, Instant::now() + MODULE_TIMEOUT)?;
    fs::read_to_string(log).context("reading environment validation log")
}

fn check_checkout(path: &Path, revision: &str, out: &Path, name: &str) -> Result<()> {
    for (suffix, args, expected) in [
        ("head", vec!["rev-parse", "HEAD"], revision),
        (
            "status",
            vec!["status", "--porcelain", "--untracked-files=no"],
            "",
        ),
    ] {
        let mut command = Command::new("git");
        sanitize(&mut command);
        command.arg("-C").arg(path).args(args);
        let actual = capture(
            &mut command,
            &out.join(format!("environment-{name}-{suffix}.log")),
        )?;
        ensure!(
            actual.trim() == expected,
            "upstream checkout {name} has wrong revision or tracked changes ({suffix})"
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{
        JumpPlan, Manifest, RegionKind, SpanNode, SpanPlan, check_output_separation,
        validate_manifest, verify_region,
    };
    use std::fs;

    #[test]
    fn jump_output_cannot_write_into_the_checked_installation() {
        let temp = tempfile::tempdir().unwrap();
        let installation = temp.path().join("checked-scanner");
        fs::create_dir(&installation).unwrap();
        fs::write(installation.join("manifest.json"), "unchanged").unwrap();
        assert!(check_output_separation(&installation.join("run"), &installation).is_err());
        assert!(
            check_output_separation(&installation.join("missing/nested/run"), &installation)
                .is_err()
        );
        assert!(
            check_output_separation(
                &installation.join("missing/../../outside/run"),
                &installation
            )
            .is_err()
        );
        assert!(!installation.join("missing").exists());
        check_output_separation(&temp.path().join("new/nested/run"), &installation).unwrap();
        assert!(!temp.path().join("new").exists());
        assert!(check_output_separation(&installation, &installation).is_err());
        check_output_separation(&temp.path().join("checked-scanner-output"), &installation)
            .unwrap();
        #[cfg(unix)]
        {
            let alias = temp.path().join("alias");
            std::os::unix::fs::symlink(&installation, &alias).unwrap();
            assert!(check_output_separation(&alias.join("run"), &installation).is_err());
            assert!(
                check_output_separation(&alias.join("missing/nested/run"), &installation).is_err()
            );
        }
        assert_eq!(
            fs::read_to_string(installation.join("manifest.json")).unwrap(),
            "unchanged"
        );
        assert_eq!(fs::read_dir(&installation).unwrap().count(), 1);
    }

    fn jump_plan() -> JumpPlan {
        let mut modules = Vec::new();
        for (index, side) in ["Original", "Candidate"].iter().enumerate() {
            let name = format!("JumpChunk{index}");
            modules.push((
                name.clone(),
                ["size", "complete", "route"]
                    .map(|suffix| format!("GolfCertificates.JumpMembership.{name}_{suffix}"))
                    .to_vec(),
            ));
            let lower = side.to_lowercase();
            modules.push((
                format!("Jump{side}"),
                ["byte", "membership"]
                    .map(|suffix| format!("GolfCertificates.JumpMembership.{lower}_{suffix}"))
                    .to_vec(),
            ));
        }
        modules.push((
            "JumpMembership".to_owned(),
            ["original", "candidate"]
                .map(|side| format!("GolfCertificates.JumpMembership.{side}_membership"))
                .to_vec(),
        ));
        modules.push((
            "JumpRegionProof".to_owned(),
            ["source_count", "source_gas", "compiler_jump_boundary"]
                .map(|name| format!("GolfCertificates.Jump.{name}"))
                .to_vec(),
        ));
        JumpPlan { modules }
    }

    #[test]
    fn jump_plan_rejects_missing_duplicate_reordered_and_unexpected_roots() {
        jump_plan().validate().unwrap();
        for mutation in ["missing", "duplicate", "reordered", "root", "gap"] {
            let mut plan = jump_plan();
            match mutation {
                "missing" => {
                    plan.modules.pop();
                }
                "duplicate" => plan.modules.insert(1, plan.modules[0].clone()),
                "reordered" => plan.modules.swap(1, 3),
                "root" => plan.modules[0].1[0] = "Untrusted.root".to_owned(),
                "gap" => plan.modules[0].0 = "JumpChunk99".to_owned(),
                _ => unreachable!(),
            }
            assert!(plan.validate().is_err(), "accepted {mutation}: {plan:?}");
        }
    }

    #[test]
    fn jump_module_closure_rejects_partial_extra_and_cached_artifacts_before_setup() {
        let plan = jump_plan();
        for mutation in ["missing", "extra", "cached"] {
            let out = tempfile::tempdir().unwrap();
            for (name, _) in plan.generated_modules() {
                fs::write(out.path().join(format!("{name}.lean")), "").unwrap();
            }
            match mutation {
                "missing" => fs::remove_file(out.path().join("JumpMembership.lean")).unwrap(),
                "extra" => fs::write(out.path().join("Unplanned.lean"), "").unwrap(),
                "cached" => fs::write(out.path().join("Images.olean"), "").unwrap(),
                _ => unreachable!(),
            }
            let error = verify_region(out.path(), RegionKind::PowerJump(&plan))
                .unwrap_err()
                .to_string();
            assert!(
                error.contains(if mutation == "cached" {
                    "cached Lean artifacts"
                } else {
                    "module set differs"
                }),
                "{error}"
            );
            assert!(!out.path().join("environment.json").exists());
        }
    }

    #[test]
    fn span_plan_rejects_missing_reused_reordered_and_forward_children() {
        use SpanNode::{Compose, Leaf};
        SpanPlan {
            leaf_count: 1,
            compositions: vec![],
        }
        .validate()
        .unwrap();
        SpanPlan {
            leaf_count: 3,
            compositions: vec![(Leaf(0), Leaf(1)), (Compose(0), Leaf(2))],
        }
        .validate()
        .unwrap();
        for plan in [
            SpanPlan {
                leaf_count: 0,
                compositions: vec![],
            },
            SpanPlan {
                leaf_count: 2,
                compositions: vec![],
            },
            SpanPlan {
                leaf_count: 2,
                compositions: vec![(Leaf(0), Leaf(0))],
            },
            SpanPlan {
                leaf_count: 2,
                compositions: vec![(Leaf(1), Leaf(0))],
            },
            SpanPlan {
                leaf_count: 3,
                compositions: vec![(Leaf(0), Leaf(2)), (Compose(0), Leaf(1))],
            },
            SpanPlan {
                leaf_count: 2,
                compositions: vec![(Compose(0), Leaf(0))],
            },
            SpanPlan {
                leaf_count: 2,
                compositions: vec![(Leaf(0), Leaf(2))],
            },
        ] {
            assert!(plan.validate().is_err(), "accepted invalid tree: {plan:?}");
        }
    }

    #[test]
    fn span_module_closure_rejects_partial_extra_and_cached_artifacts_before_setup() {
        let plan = SpanPlan {
            leaf_count: 1,
            compositions: vec![],
        };
        for mutation in ["missing", "extra", "cached"] {
            let out = tempfile::tempdir().unwrap();
            for (name, _) in plan.modules() {
                fs::write(out.path().join(format!("{name}.lean")), "").unwrap();
            }
            match mutation {
                "missing" => fs::remove_file(out.path().join("BindLeaf0.lean")).unwrap(),
                "extra" => fs::write(out.path().join("Unplanned.lean"), "").unwrap(),
                "cached" => fs::write(out.path().join("Images.olean"), "").unwrap(),
                _ => unreachable!(),
            }
            let error = verify_region(out.path(), RegionKind::ChunkedSpan(&plan))
                .unwrap_err()
                .to_string();
            assert!(
                error.contains(if mutation == "cached" {
                    "cached Lean artifacts"
                } else {
                    "module set differs"
                }),
                "{error}"
            );
            assert!(!out.path().join("environment.json").exists());
        }
    }

    #[test]
    fn manifest_rejects_path_escape_unlocked_and_duplicate_packages() {
        let valid = serde_json::json!({"packagesDir": ".lake/packages", "packages": [{"name": "mathlib", "type": "git", "rev": "79e94a093aff4a60fb1b1f92d9681e407124c2ca", "subDir": null}]});
        let parse = |value| serde_json::from_value::<Manifest>(value).unwrap();
        validate_manifest(&parse(valid.clone())).unwrap();
        for (field, value) in [
            ("name", "../escape"),
            ("rev", "main"),
            ("type", "path"),
            ("subDir", "nested"),
        ] {
            let mut bad = valid.clone();
            bad["packages"][0][field] = value.into();
            assert!(validate_manifest(&parse(bad)).is_err());
        }
        let mut duplicate = valid.clone();
        duplicate["packages"]
            .as_array_mut()
            .unwrap()
            .push(valid["packages"][0].clone());
        assert!(validate_manifest(&parse(duplicate)).is_err());
    }
}
