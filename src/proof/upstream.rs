//! Separate pinned upstream semantics checker; never uses the expression toolchain.
use anyhow::{Context, Result, ensure};
use serde::Deserialize;
use serde_json::json;
use std::{
    collections::BTreeSet,
    env, fs,
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
pub(crate) enum RegionKind {
    Power,
    Mask,
}

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

/// Called only after the trusted generator writes the three fixed certificate files.
pub(crate) fn verify_region(out: &Path, kind: RegionKind) -> Result<String> {
    let out = out.canonicalize()?;
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
        RegionKind::Power => &[][..],
        RegionKind::Mask => MASK_MODULES,
    };
    for (name, source, _) in MODULES.iter().chain(additional) {
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
    };
    let image_roots: &[&str] = match kind {
        RegionKind::Power => &[],
        RegionKind::Mask => &[
            "GolfCertificates.originalRoundtrip",
            "GolfCertificates.candidateRoundtrip",
            "GolfCertificates.originalWindowFetch",
            "GolfCertificates.candidateWindowFetch",
        ],
    };
    let generated: &[(&str, &[&str])] = &[
        ("Images", image_roots),
        ("Decode", &[]),
        ("RegionProof", region_roots),
    ];
    for (name, expected) in MODULES
        .iter()
        .chain(additional)
        .map(|(name, _, roots)| (*name, *roots))
        .chain(generated.iter().copied())
    {
        let log = out.join(format!("{name}.log"));
        let mut command = Command::new(&lean);
        sanitize(&mut command);
        command
            .current_dir(&out)
            .env("LEAN_PATH", &search_path)
            .args(["-o", &format!("{name}.olean"), &format!("{name}.lean")]);
        run_command(&mut command, &log, Instant::now() + MODULE_TIMEOUT)
            .with_context(|| format!("upstream module {name} failed; see {}", log.display()))?;
        let expected = expected
            .iter()
            .map(|name| (*name).to_owned())
            .collect::<Vec<_>>();
        audit_axioms(
            &fs::read_to_string(&log)?,
            &expected,
            AxiomPolicy::Foundational,
        )
        .with_context(|| format!("upstream axiom audit failed; see {}", log.display()))?;
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
    use super::{Manifest, validate_manifest};

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
