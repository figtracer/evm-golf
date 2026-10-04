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
    Mask,
    ChunkedSpan(&'a SpanPlan),
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

/// Called only after the trusted generator writes its fixed certificate files.
pub(crate) fn verify_region(out: &Path, kind: RegionKind<'_>) -> Result<String> {
    let out = out.canonicalize()?;
    if let RegionKind::ChunkedSpan(plan) = kind {
        plan.validate()?;
        let expected: BTreeSet<_> = plan
            .modules()
            .into_iter()
            .map(|(name, _)| format!("{name}.lean"))
            .collect();
        let mut found = BTreeSet::new();
        for entry in fs::read_dir(&out)? {
            let path = entry?.path();
            if path.extension().is_some_and(|ext| ext == "lean") {
                ensure!(
                    path.is_file(),
                    "span module is not a file: {}",
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
            "span generated module set differs from the complete proof plan"
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
    let root = env::var_os("EVM_GOLF_UPSTREAM")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join(".tools/upstream"))
        .canonicalize()
        .context("upstream toolchain unavailable; run scripts/setup-upstream.sh")?;
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
    paths.push(
        semantics
            .join(".lake/build/lib/lean")
            .canonicalize()
            .context("missing upstream semantics build; run scripts/setup-upstream.sh")?,
    );
    paths.push(
        root.join("lean/lib/lean")
            .canonicalize()
            .context("missing pinned Lean standard library")?,
    );
    let search_path = env::join_paths(&paths)?;
    fs::write(
        out.join("environment.json"),
        serde_json::to_vec_pretty(&json!({
            "lean_version": version.trim(), "lean": lean, "upstream_revision": REVISION,
            "semantics": semantics, "packages": packages, "lean_path": paths,
            "module_timeout_seconds": MODULE_TIMEOUT.as_secs(),
            "claim_scope": "internal region boundary and residual canonical X calls; no whole-contract equivalence",
            "trust": "installed Lean and pinned upstream/dependency build artifacts are trusted; local certificate support modules are rebuilt from embedded sources"
        }))?,
    )?;
    let additional = match kind {
        RegionKind::Power => POWER_MODULES,
        RegionKind::Mask | RegionKind::ChunkedSpan(_) => MASK_MODULES,
    };
    let composition = match kind {
        RegionKind::ChunkedSpan(_) => SPAN_MODULES,
        RegionKind::Power | RegionKind::Mask => &[],
    };
    let chunks = match kind {
        RegionKind::ChunkedSpan(_) => CHUNK_MODULES,
        _ => &[],
    };
    for (name, source, _) in MODULES
        .iter()
        .chain(additional)
        .chain(composition)
        .chain(chunks)
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
        RegionKind::Power => &[
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
        RegionKind::ChunkedSpan(_) => &[],
        RegionKind::Power | RegionKind::Mask => &[
            ("Images", image_roots),
            ("Decode", &[]),
            ("RegionProof", region_roots),
        ],
    };
    let generated = match kind {
        RegionKind::ChunkedSpan(plan) => plan.modules(),
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
    let mut measurements = if matches!(kind, RegionKind::ChunkedSpan(_)) {
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
    use super::{Manifest, RegionKind, SpanNode, SpanPlan, validate_manifest, verify_region};
    use std::fs;

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
