//! Bind local layout certificates to the complete emitted byte arrays.

use anyhow::{Result, ensure};
use std::fmt::Write as _;

use super::{
    MAX_RUNTIME_BYTES, Rewrite, certificates, from_hex, layout, window_proposal::WindowProof,
};

const FRAGMENT_MODEL: &str = include_str!("../../lean/Fragment.lean");
const LITERAL_MODEL: &str = include_str!("../../lean/Literals.lean");
const ZERO_CHAIN_MODEL: &str = include_str!("../../lean/ZeroChains.lean");
const LOCAL_CERTIFICATES: &str = include_str!("../../lean/Certificates.lean");
const MASK_MODEL: &str = include_str!("../../lean/MaskWindow.lean");
const MASK_REUSE_MODEL: &str = include_str!("../../lean/MaskReuse.lean");
const IDEMPOTENT_MASK_MODEL: &str = include_str!("../../lean/IdempotentMask.lean");
const WINDOW_MODEL: &str = include_str!("../../lean/WindowArtifact.lean");
const WINDOW_CHECKER: &str = include_str!("../../lean/WindowChecker.lean");
const WINDOW_STRUCTURE: &str = include_str!("../../lean/WindowStructure.lean");
const WINDOW_PROOF: &str = include_str!("../../lean/WindowArtifactProof.lean.in");
const STACK_MODEL: &str = include_str!("../../lean/Stack.lean");
const COMPOSITION_MODEL: &str = include_str!("../../lean/Composition.lean");
const LAYOUT_MODEL: &str = include_str!("../../lean/Layout.lean");
// A full EIP-170 image exceeded 65K recursive elaboration depth and the default
// heartbeat budget. Kernel reduction at these limits checked 24,576 bytes; the
// existing 60-second wall-clock proof budget still bounds the entire attempt.
const ARTIFACT_RECURSION_LIMIT: usize = 131_072;
const ARTIFACT_HEARTBEATS: usize = 2_000_000;

pub(super) fn certificate(
    original: &[u8],
    candidate: &[u8],
    rewrites: &[Rewrite],
    copies: &[layout::CodeCopy],
) -> Result<(String, Vec<String>)> {
    ensure!(
        original.len() <= MAX_RUNTIME_BYTES && candidate.len() <= MAX_RUNTIME_BYTES,
        "layout artifact exceeds EIP-170 size limit"
    );
    ensure!(
        rewrites
            .iter()
            .all(|rewrite| rewrite.required_stack <= 1 || layout::is_mask(rewrite)),
        "layout artifacts require certified fragment prefixes"
    );
    // Local soundness is proved once; the kernel checks every actual site below.
    // Compact-mode certificates still emit their individual fragment theorems.
    let (mut source, _) = certificates(&[])?;
    writeln!(
        source,
        "\n{FRAGMENT_MODEL}\n{STACK_MODEL}\n{COMPOSITION_MODEL}\n{LAYOUT_MODEL}\n{LITERAL_MODEL}\n{ZERO_CHAIN_MODEL}"
    )
    .unwrap();
    writeln!(
        source,
        "\nset_option maxRecDepth {ARTIFACT_RECURSION_LIMIT}\nset_option maxHeartbeats {ARTIFACT_HEARTBEATS}\n{LOCAL_CERTIFICATES}"
    ).unwrap();
    let windows = rewrites.iter().any(layout::is_mask);
    if windows {
        writeln!(
            source,
            "{MASK_MODEL}\n{IDEMPOTENT_MASK_MODEL}\n{MASK_REUSE_MODEL}\n{WINDOW_MODEL}\n{WINDOW_CHECKER}\n{WINDOW_STRUCTURE}"
        )
        .unwrap();
    }
    source.push_str("\nnamespace GolfArtifact\n");
    // Embed both actual images independently; never define candidate by applying
    // the proposed patches, which would conceal errors in the Rust emitter.
    writeln!(source, "def original : List Nat := {original:?}").unwrap();
    writeln!(source, "def candidate : List Nat := {candidate:?}").unwrap();
    source.push_str("def sites : List GolfLayout.Site := [\n");
    for (i, rewrite) in rewrites.iter().enumerate() {
        let before = from_hex(&rewrite.before)?;
        let after = from_hex(&rewrite.after)?;
        writeln!(
            source,
            "  ⟨{}, {before:?}, {after:?}, {}⟩{}",
            rewrite.original_pc,
            rewrite.required_stack,
            if i + 1 == rewrites.len() { "" } else { "," }
        )
        .unwrap();
    }
    // These are kernel reductions, not native evaluation. The aggregate theorem
    // depends transitively on each site's certified operational and context proofs.
    source.push_str("]\nend GolfArtifact\n");
    if windows {
        source.push_str("namespace GolfArtifact\nopen GolfLayout GolfWindowArtifact\ndef copies : List GolfLayout.CodeCopy := [\n");
        for (i, copy) in copies.iter().enumerate() {
            writeln!(
                source,
                "  ⟨{}, {}, {}, {}, {}⟩{}",
                copy.pc,
                copy.prefix_start,
                copy.source,
                copy.len,
                copy.destination,
                if i + 1 == copies.len() { "" } else { "," }
            )
            .unwrap();
        }
        source.push_str("]\n");
        let mut masks = Vec::new();
        for site in rewrites.iter().filter(|site| layout::is_mask(site)) {
            let before = from_hex(&site.before)?;
            let after = from_hex(&site.after)?;
            masks.push(format!(
                "⟨{}, {before:?}, {after:?}, {}⟩",
                site.original_pc, site.required_stack
            ));
        }
        source.push_str(&WINDOW_PROOF.replace("$MASK_SITES", &format!("[{}]", masks.join(","))));
        source.push_str("\nend GolfArtifact\n#print axioms GolfArtifact.window_artifact\n");
        return Ok((source, vec!["GolfArtifact.window_artifact".into()]));
    }
    source.push_str(
        "\ntheorem layout_artifact :\n  GolfLayout.LayoutArtifact GolfArtifact.original GolfArtifact.candidate GolfArtifact.sites := by\n  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩\n  exact GolfReflected.checkSites_sound GolfArtifact.sites (by decide +kernel)\n#print axioms layout_artifact\n",
    );
    let mut names = vec!["layout_artifact".into()];
    if !copies.is_empty() {
        source.push_str("\nnamespace GolfArtifact\ndef copies : List GolfLayout.CodeCopy := [\n");
        for (i, copy) in copies.iter().enumerate() {
            writeln!(
                source,
                "  ⟨{}, {}, {}, {}, {}⟩{}",
                copy.pc,
                copy.prefix_start,
                copy.source,
                copy.len,
                copy.destination,
                if i + 1 == copies.len() { "" } else { "," }
            )
            .unwrap();
        }
        source.push_str(
            "]\nend GolfArtifact\n\ntheorem codecopy_artifact :\n  GolfLayout.CodeCopyArtifact GolfArtifact.original GolfArtifact.candidate GolfArtifact.copies := by\n  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩\n#print axioms codecopy_artifact\n",
        );
        names.push("codecopy_artifact".into());
    }
    Ok((source, names))
}

/// A separate typed gate for one generated byte-pair proof. Existing family
/// checkers are intentionally not extended to recognize arbitrary byte pairs.
pub(super) fn proposal_certificate(
    original: &[u8],
    candidate: &[u8],
    rewrite: &Rewrite,
    copies: &[layout::CodeCopy],
    local: WindowProof,
) -> Result<(String, Vec<String>)> {
    ensure!(
        original.len() <= MAX_RUNTIME_BYTES && candidate.len() <= MAX_RUNTIME_BYTES,
        "proposal artifact exceeds EIP-170 size limit"
    );
    ensure!(
        rewrite.required_stack == local.required,
        "proposal stack metadata mismatch"
    );
    let before = from_hex(&rewrite.before)?;
    let after = from_hex(&rewrite.after)?;
    let mut source = local.source;
    let mut names = local.names;
    writeln!(source, "\nset_option maxRecDepth {ARTIFACT_RECURSION_LIMIT}\nset_option maxHeartbeats {ARTIFACT_HEARTBEATS}\n{}\n{}",
        include_str!("../../lean/GenericWindowArtifact.lean"),
        include_str!("../../lean/GenericWindowChecker.lean")).unwrap();
    writeln!(source, "namespace GolfProposedArtifact\nopen GolfLayout GolfGenericWindow\ndef site : Site := ⟨{}, {before:?}, {after:?}, {}⟩",
        rewrite.original_pc, rewrite.required_stack).unwrap();
    writeln!(
        source,
        "def localCertificate : GenericLocal site {} ({}) {} {} {} where
 requiredExact := rfl
 feasible := by decide
 nonemptyBefore := by decide
 nonemptyAfter := by decide
 sameLength := by decide
 beforeBytes := GolfGenerated.before_bytes
 afterBytes := GolfGenerated.after_bytes
 beforeSupported := by decide +kernel
 afterSupported := by decide +kernel
 beforeComplete := GolfGenerated.before_complete
 afterComplete := GolfGenerated.after_complete
 beforeProfile := GolfGenerated.before_profile
 afterProfile := GolfGenerated.after_profile
 output := GolfGenerated.output
 success := GolfGenerated.success
 underflow := GolfGenerated.underflow
 overflow := GolfGenerated.overflow
 allHeight := GolfGenerated.all_height
 context := GolfGenerated.context
 faultClasses := GolfGenerated.fault_classes",
        local.required, local.delta, local.peak, local.before_ops, local.after_ops
    )
    .unwrap();
    // Embed independently supplied images; the kernel must check reconstruction.
    writeln!(source, "def original : List Nat := {original:?}\ndef candidate : List Nat := {candidate:?}\ndef copies : List GolfLayout.CodeCopy := [").unwrap();
    for (i, copy) in copies.iter().enumerate() {
        writeln!(
            source,
            "  ⟨{}, {}, {}, {}, {}⟩{}",
            copy.pc,
            copy.prefix_start,
            copy.source,
            copy.len,
            copy.destination,
            if i + 1 == copies.len() { "" } else { "," }
        )
        .unwrap();
    }
    writeln!(source, "]\ndef artifact : GenericWindowArtifact original candidate site copies {} ({}) {} {} {} :=\n certify localCertificate (by decide +kernel)\nend GolfProposedArtifact\n#print axioms GolfProposedArtifact.artifact",
        local.required, local.delta, local.peak, local.before_ops, local.after_ops).unwrap();
    names.push("GolfProposedArtifact.artifact".into());
    Ok((source, names))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{proof, runtime::decode};
    use revm::primitives::{U256, hex};
    use std::fs;
    use tempfile::tempdir;

    #[test]
    #[ignore = "requires Lean 4.34.0"]
    fn generated_proposals_bind_full_stacks_and_exact_artifacts() {
        let dir = tempdir().unwrap();
        for (i, (before, after)) in [
            ("600150600250", "630000000050"),
            ("600116600116", "630000000116"),
            ("6001506002501616", "6300000000501616"),
            ("600160025050600350", "6400000000005f5050"),
        ]
        .into_iter()
        .enumerate()
        {
            let before = from_hex(before).unwrap();
            let after = from_hex(after).unwrap();
            let local = super::super::window_proposal::certificate(&before, &after).unwrap();
            let site = Rewrite {
                original_pc: 1,
                before: hex::encode(&before),
                after: hex::encode(&after),
                required_stack: local.required,
            };
            let original = [vec![0x5b], before.clone(), vec![0x00]].concat();
            let candidate = [vec![0x5b], after.clone(), vec![0x00]].concat();
            let (source, names) =
                proposal_certificate(&original, &candidate, &site, &[], local).unwrap();
            let path = dir.path().join(format!("Proposal{i}.lean"));
            fs::write(&path, source).unwrap();
            let checked = proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational);
            assert!(
                checked.is_ok(),
                "{checked:?}\n{}",
                fs::read_to_string(path.with_extension("log")).unwrap_or_default()
            );
            if i == 1 {
                // The candidate argument is independent of the local proof and
                // patch construction. An unrelated exterior change must fail.
                let mut corrupted = candidate;
                *corrupted.last_mut().unwrap() = 0x5b;
                let local = super::super::window_proposal::certificate(&before, &after).unwrap();
                let (source, names) =
                    proposal_certificate(&original, &corrupted, &site, &[], local).unwrap();
                let path = dir.path().join("ChangedExterior.lean");
                fs::write(&path, source).unwrap();
                assert!(
                    proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational).is_err()
                );
                // A proof of one exact byte pair cannot certify another pair,
                // even when length and stack metadata are unchanged.
                let mut different = after;
                different[4] = 2;
                let local = super::super::window_proposal::certificate(
                    &before,
                    &from_hex(&site.after).unwrap(),
                )
                .unwrap();
                let different_site = Rewrite {
                    after: hex::encode(&different),
                    ..site
                };
                let candidate = [vec![0x5b], different, vec![0x00]].concat();
                let (source, names) =
                    proposal_certificate(&original, &candidate, &different_site, &[], local)
                        .unwrap();
                let path = dir.path().join("ChangedPair.lean");
                fs::write(&path, source).unwrap();
                assert!(
                    proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational).is_err()
                );
            }
        }
    }

    #[test]
    #[ignore = "requires Lean 4.34.0"]
    fn binds_mixed_mask_artifacts_and_rejects_unlisted_changes() {
        let dir = tempdir().unwrap();
        let before = "6001600160e01b03166001600160e01b0319";
        let after = "6001600160e01b03166400ffffffff60e01b";
        let original = from_hex(&format!("6007{before}60020200")).unwrap();
        let candidate = from_hex(&format!("6007{after}60011b00")).unwrap();
        let sites = [
            Rewrite {
                original_pc: 2,
                before: before.into(),
                after: after.into(),
                required_stack: 1,
            },
            Rewrite {
                original_pc: 20,
                before: "600202".into(),
                after: "60011b".into(),
                required_stack: 1,
            },
        ];
        let verify = |name: &str, candidate: &[u8]| {
            let (source, names) = certificate(&original, candidate, &sites, &[]).unwrap();
            assert_eq!(names, ["GolfArtifact.window_artifact"]);
            let path = dir.path().join(format!("{name}.lean"));
            fs::write(&path, source).unwrap();
            proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational)
        };
        verify("Mixed", &candidate).unwrap();
        let mut outside = candidate.clone();
        outside[1] = 8;
        assert!(verify("UnlistedByte", &outside).is_err());
        let mut wrong_mask = candidate;
        wrong_mask[16] = 0xfe;
        assert!(verify("WrongMask", &wrong_mask).is_err());
    }

    #[test]
    #[ignore = "requires Lean 4.34.0"]
    fn binds_both_mask_families_and_rejects_wrong_idempotent_outputs() {
        let dir = tempdir().unwrap();
        let original = from_hex(
            "60076001600160e01b03166001600160e01b03196001600160a01b03166001600160a01b031600",
        )
        .unwrap();
        let (candidate, sites) =
            layout::transform(&layout::analyze(&original, false).unwrap()).unwrap();
        assert_eq!(sites.len(), 2);
        let verify = |name: &str, candidate: &[u8], sites: &[Rewrite]| {
            let (source, names) = certificate(&original, candidate, sites, &[]).unwrap();
            assert_eq!(names, ["GolfArtifact.window_artifact"]);
            let path = dir.path().join(format!("{name}.lean"));
            fs::write(&path, source).unwrap();
            proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational)
        };
        verify("BothFamilies", &candidate, &sites).unwrap();
        // Alter the retained mask width and declare the altered bytes too: exact
        // family admission must reject it, even when reconstruction matches.
        let mut wrong = candidate.clone();
        wrong[34] = 0x80;
        let mut altered_sites = sites;
        altered_sites[1].after = hex::encode(&wrong[20..38]);
        assert!(verify("WrongIdempotent", &wrong, &altered_sites).is_err());
    }

    #[test]
    #[ignore = "requires Lean 4.34.0"]
    fn binds_all_mask_families_and_rejects_inconsistent_stack_metadata() {
        let dir = tempdir().unwrap();
        let original = from_hex(concat!(
            "6001600260036004600560066007",
            "6001600160e01b03166001600160e01b0319",
            "6001600160a01b03166001600160a01b0316",
            "6001600160a01b0316866001600160a01b0316",
            "6001600160801b0316816001600160801b0316",
            "00"
        ))
        .unwrap();
        let (candidate, sites) =
            layout::transform(&layout::analyze(&original, false).unwrap()).unwrap();
        assert_eq!(
            sites
                .iter()
                .map(|site| site.required_stack)
                .collect::<Vec<_>>(),
            [1, 1, 7, 2]
        );
        let verify = |name: &str, sites: &[Rewrite]| {
            let (source, names) = certificate(&original, &candidate, sites, &[]).unwrap();
            let path = dir.path().join(format!("{name}.lean"));
            fs::write(&path, source).unwrap();
            proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational)
        };
        verify("AllFamilies", &sites).unwrap();
        let mut wrong = sites;
        wrong[2].required_stack = 1;
        assert!(verify("WrongMetadata", &wrong).is_err());
        wrong[2].required_stack = 6;
        assert!(certificate(&original, &candidate, &wrong, &[]).is_err());
        wrong[2].required_stack = 7;
        wrong[2].after = wrong[2].after.replacen("91", "90", 1);
        assert!(certificate(&original, &candidate, &wrong, &[]).is_err());
    }

    #[test]
    #[ignore = "requires Lean 4.34.0"]
    fn binds_complete_artifacts_to_aligned_successful_rewrites() {
        let dir = tempdir().unwrap();
        let original = from_hex("600760020260010200").unwrap();
        let candidate = from_hex("600760011b60000100").unwrap();
        let rewrites = [
            Rewrite {
                original_pc: 2,
                before: "600202".into(),
                after: "60011b".into(),
                required_stack: 1,
            },
            Rewrite {
                original_pc: 5,
                before: "600102".into(),
                after: "600001".into(),
                required_stack: 1,
            },
        ];
        let check = |name: &str, original: &[u8], candidate: &[u8], rewrites: &[Rewrite]| {
            let (source, names) = certificate(original, candidate, rewrites, &[])?;
            let path = dir.path().join(format!("{name}.lean"));
            fs::write(&path, source).unwrap();
            proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational)
        };
        check("Valid", &original, &candidate, &rewrites).unwrap();
        check("Identity", &original, &original, &[]).unwrap();
        check("Empty", &[], &[], &[]).unwrap();
        let mut family_original = vec![0x5f];
        let mut family_candidate = vec![0x5f];
        let mut family_sites = Vec::new();
        for width in 0u8..=32 {
            let mut values = vec![U256::ZERO];
            if width > 0 {
                values.extend([U256::from(1), U256::from(2)]);
                // Every power at its minimum PUSH width, plus padded tiny values.
                values.extend(
                    ((usize::from(width) - 1) * 8..usize::from(width) * 8)
                        .map(|shift| U256::from(1) << shift),
                );
                values.sort_unstable();
                values.dedup();
            }
            for value in values {
                let mut before = vec![0x5f + width];
                let mut after = before.clone();
                if width > 0 {
                    before.extend_from_slice(&value.to_be_bytes::<32>()[32 - usize::from(width)..]);
                    after.extend(std::iter::repeat_n(0, usize::from(width)));
                    if value > U256::from(1) {
                        *after.last_mut().unwrap() = value.trailing_zeros() as u8;
                    }
                }
                before.push(0x02);
                after.push(if value.is_zero() {
                    0x16
                } else if value == U256::from(1) {
                    0x01
                } else {
                    0x1b
                });
                family_sites.push(Rewrite {
                    original_pc: family_original.len(),
                    before: hex::encode(&before),
                    after: hex::encode(&after),
                    required_stack: 1,
                });
                family_original.extend(before);
                family_candidate.extend(after);
            }
        }
        // Preserve unreachable truncated PUSH data without treating it as a site.
        family_original.extend([0, 0x61, 1]);
        family_candidate.extend([0, 0x61, 1]);
        check(
            "Families",
            &family_original,
            &family_candidate,
            &family_sites,
        )
        .unwrap();
        // A changed byte outside the certified sites must not be hidden.
        let mut changed = candidate.clone();
        changed[1] = 8;
        assert!(check("Untouched", &original, &changed, &rewrites).is_err());
        assert!(check("Missing", &original, &candidate, &rewrites[..1]).is_err());
        let duplicate = Rewrite {
            original_pc: 2,
            before: "600202".into(),
            after: "60011b".into(),
            required_stack: 1,
        };
        assert!(
            check(
                "Overlap",
                &original,
                &candidate,
                &[
                    duplicate,
                    Rewrite {
                        original_pc: 2,
                        before: "600202".into(),
                        after: "60011b".into(),
                        required_stack: 1
                    }
                ]
            )
            .is_err()
        );
        // The global layout is identical here, but the patch is inside PUSH data.
        let embedded = Rewrite {
            original_pc: 1,
            before: "600202".into(),
            after: "60011b".into(),
            required_stack: 1,
        };
        assert!(
            check(
                "Immediate",
                &from_hex("6560020200000000").unwrap(),
                &from_hex("6560011b00000000").unwrap(),
                &[embedded],
            )
            .is_err()
        );
        let wrong_slice = Rewrite {
            original_pc: 0,
            before: "600102".into(),
            after: "600001".into(),
            required_stack: 1,
        };
        assert!(
            check(
                "WrongSlice",
                &from_hex("60020200").unwrap(),
                &from_hex("60000100").unwrap(),
                &[wrong_slice],
            )
            .is_err()
        );
        let reordered = [
            Rewrite {
                original_pc: 5,
                before: "600102".into(),
                after: "600001".into(),
                required_stack: 1,
            },
            Rewrite {
                original_pc: 2,
                before: "600202".into(),
                after: "60011b".into(),
                required_stack: 1,
            },
        ];
        assert!(check("Reordered", &original, &candidate, &reordered).is_err());
        // Prove every other acceptance condition before rejecting a layout or
        // profile mismatch. These fixtures need direct bounded proofs because
        // they intentionally lie outside the production PUSH+binary templates.
        let direct_behavior = "by\n      constructor\n      · intro stack x y\n        cases stack with\n        | nil => simp [GolfBounded.run, Golf.run, Golf.immediate]\n        | cons a tail => simp [GolfBounded.run, Golf.run, Golf.immediate] <;> (repeat' split) <;> simp_all <;> omega\n      · intro x y\n        simp [Golf.run, Golf.immediate]";
        for (name, before, after, mismatch) in [
            (
                "Boundaries",
                "630000000102",
                "600001600001",
                "GolfLayout.scan GolfArtifact.original ≠ GolfLayout.scan GolfArtifact.candidate ∧ GolfArtifact.sites.all (fun site => GolfLayout.profile site.before == some (1, 0, 1) && GolfLayout.profile site.after == some (1, 0, 1)) = true",
            ),
            (
                "Profile",
                "5f17",
                "5f17",
                "GolfLayout.scan GolfArtifact.original = GolfLayout.scan GolfArtifact.candidate ∧ GolfArtifact.sites.all (fun site => GolfLayout.profile site.before == some (1, 0, 1) && GolfLayout.profile site.after == some (1, 0, 1)) ≠ true",
            ),
        ] {
            let rewrite = Rewrite {
                original_pc: 0,
                before: before.into(),
                after: after.into(),
                required_stack: 1,
            };
            let mut original = from_hex(before).unwrap();
            let mut candidate = from_hex(after).unwrap();
            original.push(0);
            candidate.push(0);
            // These deliberately unusual fragments need independent local
            // proofs so the test isolates the global boundary/profile gate.
            let (unbounded, _) = certificates(std::slice::from_ref(&rewrite)).unwrap();
            let (source, _) = certificate(&original, &candidate, &[rewrite], &[]).unwrap();
            let leaf = &unbounded[unbounded.find("theorem runtime_rewrite_0").unwrap()..];
            let before_bytes = from_hex(before).unwrap();
            let after_bytes = from_hex(after).unwrap();
            let mut local = format!(
                "{leaf}\ntheorem runtime_bounded_0 : GolfBounded.FragmentEquivalent {before_bytes:?} {after_bytes:?} := by\n  exact GolfBounded.of_unbounded ({direct_behavior}) ({direct_behavior}) runtime_rewrite_0\n#print axioms runtime_bounded_0\n"
            );
            local.push_str(&format!("theorem runtime_context_0 : GolfComposition.ContextEquivalent {before_bytes:?} {after_bytes:?} := by\n  apply GolfComposition.context_of_fragment (beforeCount := {}) (afterCount := {}) ?_ ?_ runtime_bounded_0\n", decode(&before_bytes).len(), decode(&after_bytes).len()));
            for bytes in [&before_bytes, &after_bytes] {
                let instructions = decode(bytes);
                local.push_str("  · exact ");
                for instruction in &instructions {
                    write!(local, "(GolfComposition.Complete.step (op := {}) (immediate := {:?}) (by decide +kernel) ", instruction.bytes[0], &instruction.bytes[1..]).unwrap();
                }
                local.push_str("GolfComposition.Complete.nil");
                for _ in instructions {
                    local.push(')');
                }
                local.push('\n');
            }
            local.push_str("#print axioms runtime_context_0\n");
            let checked_source = source
                .replace("theorem layout_artifact :", &format!("{local}\ntheorem layout_artifact :"))
                .replace("GolfReflected.checkSites_sound GolfArtifact.sites (by decide +kernel)", "GolfLayout.CertifiedSites.cons (by decide +kernel) runtime_rewrite_0 runtime_bounded_0 runtime_context_0 GolfLayout.CertifiedSites.nil");
            let names = [
                "runtime_rewrite_0",
                "runtime_bounded_0",
                "runtime_context_0",
                "layout_artifact",
            ]
            .map(str::to_owned)
            .to_vec();
            let (declarations, _) = checked_source
                .split_once("theorem layout_artifact :")
                .unwrap();
            let positive = format!("{declarations}
 theorem isolated_failure :
  GolfArtifact.original.all (fun byte => byte < 256) = true ∧
  GolfArtifact.candidate.all (fun byte => byte < 256) = true ∧
  GolfLayout.applySites GolfArtifact.original GolfArtifact.sites = some GolfArtifact.candidate ∧
  GolfArtifact.original.length = GolfArtifact.candidate.length ∧
  GolfLayout.aligned GolfArtifact.sites ((GolfLayout.scan GolfArtifact.original).map (fun item => item.1) ++ [GolfArtifact.original.length]) = true ∧
  ({mismatch}) ∧ GolfLayout.CertifiedSites GolfArtifact.sites := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  exact GolfLayout.CertifiedSites.cons (by decide +kernel) runtime_rewrite_0 runtime_bounded_0 runtime_context_0 GolfLayout.CertifiedSites.nil
#print axioms isolated_failure
");
            let path = dir.path().join(format!("{name}Prerequisites.lean"));
            fs::write(&path, positive).unwrap();
            let mut positive_names = names.clone();
            *positive_names.last_mut().unwrap() = "isolated_failure".into();
            proof::verify_named(&path, &positive_names, proof::AxiomPolicy::Foundational)
                .unwrap_or_else(|error| {
                    panic!(
                        "{error:#}\n{}",
                        fs::read_to_string(path.with_extension("log")).unwrap_or_default()
                    )
                });
            let path = dir.path().join(format!("{name}.lean"));
            fs::write(&path, checked_source).unwrap();
            assert!(proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational).is_err());
        }
        // The new guarantee must depend on enforcing the actual 1,024-word bound.
        let (source, names) = certificate(&original, &candidate, &rewrites, &[]).unwrap();
        let path = dir.path().join("WrongStackLimit.lean");
        fs::write(
            &path,
            source.replace(
                "if stack.length > 1024 then none",
                "if stack.length > 1025 then none",
            ),
        )
        .unwrap();
        assert!(proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational).is_err());
        // Local theorems must be attached to their own concrete sites.
        let (source, names) = certificate(&original, &candidate, &rewrites, &[]).unwrap();
        let path = dir.path().join("WrongTheorem.lean");
        fs::write(
            &path,
            source.replace(
                "GolfReflected.checkSites_sound GolfArtifact.sites",
                "GolfReflected.checkSites_sound [⟨2, [96,2,2], [96,1,27], 1⟩, ⟨2, [96,2,2], [96,1,27], 1⟩]",
            ),
        )
        .unwrap();
        assert!(proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational).is_err());
        // A correct aggregate type must not hide an untrusted local proof.
        let path = dir.path().join("UntrustedLocal.lean");
        fs::write(&path, source
            .replace("theorem layout_artifact :", "axiom unsupported_local (sites : List GolfLayout.Site) : GolfReflected.checkSites sites = true → GolfLayout.CertifiedSites sites\ntheorem layout_artifact :")
            .replace("GolfReflected.checkSites_sound GolfArtifact.sites", "unsupported_local GolfArtifact.sites"))
            .unwrap();
        let error =
            proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational).unwrap_err();
        assert!(format!("{error:#}").contains("unexpected axiom dependency: unsupported_local"));
        let path = dir.path().join("MissingAggregateReport.lean");
        fs::write(&path, source.replace("#print axioms layout_artifact", "")).unwrap();
        assert!(proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational).is_err());
        // Wrong shift immediates retain layout, but must fail semantic checking.
        for exponent in [8usize, 128, 255] {
            let mut before = vec![0x7f];
            before.extend_from_slice(&(U256::from(1) << exponent).to_be_bytes::<32>());
            before.push(0x02);
            let mut after = vec![0; 34];
            after[0] = 0x7f;
            after[32] = (exponent - 1) as u8;
            after[33] = 0x1b;
            let wrong = Rewrite {
                original_pc: 0,
                before: hex::encode(&before),
                after: hex::encode(&after),
                required_stack: 1,
            };
            assert!(check(&format!("WrongPower{exponent}"), &before, &after, &[wrong]).is_err());
        }
    }
    #[test]
    #[ignore = "requires Lean 4.34.0"]
    fn binds_literal_folds_and_stack_requirements() {
        let dir = tempdir().unwrap();
        let mut original = Vec::new();
        let mut candidate = Vec::new();
        let mut rewrites = Vec::new();
        // Empty input stack, PUSH0, unequal widths, and oversized shifts.
        for (before, after) in [
            ("5f5f16", "5f5f50"),
            ("60f0600f16", "6000600050"),
            ("61012360ff16", "610023600050"),
            ("60016101001b", "600061000050"),
        ] {
            rewrites.push(Rewrite {
                original_pc: original.len(),
                before: before.into(),
                after: after.into(),
                required_stack: 0,
            });
            original.extend(from_hex(before).unwrap());
            candidate.extend(from_hex(after).unwrap());
        }
        let mut before = vec![0x7f];
        before.extend_from_slice(&U256::from(1).to_be_bytes::<32>());
        before.extend([0x60, 255, 0x1b]);
        let mut after = vec![0x7f];
        after.extend_from_slice(&(U256::from(1) << 255usize).to_be_bytes::<32>());
        after.extend([0x60, 0, 0x50]);
        rewrites.push(Rewrite {
            original_pc: original.len(),
            before: hex::encode(&before),
            after: hex::encode(&after),
            required_stack: 0,
        });
        original.extend(before);
        candidate.extend(after);
        original.push(0);
        candidate.push(0);
        let check = |name: &str, source: &str, names: &[String]| {
            let path = dir.path().join(format!("{name}.lean"));
            fs::write(&path, source).unwrap();
            proof::verify_named(&path, names, proof::AxiomPolicy::Foundational)
        };
        let (mut source, mut names) = certificate(&original, &candidate, &rewrites, &[]).unwrap();
        // Concrete false-checker witnesses preserve the reason for rejection:
        // wrong result, missing POP, truncated PUSH, unsupported operator, and
        // a one-word rewrite falsely claiming to need no initial stack.
        source.push_str(
            r#"
theorem literal_rejection_controls :
  GolfReflected.checkSite ⟨0, [96,240,96,15,22], [96,1,96,0,80], 0⟩ = false ∧
  GolfReflected.checkSite ⟨0, [96,240,96,15,22], [96,0,96,0,22], 0⟩ = false ∧
  GolfReflected.checkSite ⟨0, [97,1,95,22], [97,0,95,80], 0⟩ = false ∧
  GolfReflected.checkSite ⟨0, [95,95,23], [95,95,80], 0⟩ = false ∧
  GolfReflected.checkSite ⟨0, [96,2,2], [96,1,27], 0⟩ = false := by decide +kernel
#print axioms literal_rejection_controls
"#,
        );
        names.push("literal_rejection_controls".into());
        check("LiteralFamilies", &source, &names).unwrap();
        rewrites[0].required_stack = 1;
        let (source, names) = certificate(&original, &candidate, &rewrites, &[]).unwrap();
        assert!(check("FalseRequirement", &source, &names).is_err());
        rewrites[0].required_stack = 0;
        rewrites[1].after = "6001600050".into();
        candidate[4] = 1;
        let (source, names) = certificate(&original, &candidate, &rewrites, &[]).unwrap();
        assert!(check("WrongLiteralValue", &source, &names).is_err());
    }

    #[test]
    #[ignore = "requires Lean 4.34.0"]
    fn binds_zero_dup_to_actual_artifact_and_stack_profile() {
        let dir = tempdir().unwrap();
        let mut original = Vec::new();
        let mut candidate = Vec::new();
        let mut rewrites = Vec::new();
        for width in 0u8..=32 {
            let mut before = vec![0x5f + width];
            before.extend(std::iter::repeat_n(0, usize::from(width)));
            before.push(0x80);
            let mut after = before.clone();
            *after.last_mut().unwrap() = 0x5f;
            rewrites.push(Rewrite {
                original_pc: original.len(),
                before: hex::encode(&before),
                after: hex::encode(&after),
                required_stack: 0,
            });
            original.extend(before);
            candidate.extend(after);
        }
        for before in [
            vec![95, 128, 128],
            std::iter::once(95)
                .chain(std::iter::repeat_n(128, 1023))
                .collect(),
            vec![96, 0, 128, 95, 128],
        ] {
            let after: Vec<_> = before
                .iter()
                .map(|op| if *op == 128 { 95 } else { *op })
                .collect();
            rewrites.push(Rewrite {
                original_pc: original.len(),
                before: hex::encode(&before),
                after: hex::encode(&after),
                required_stack: 0,
            });
            original.extend(before);
            candidate.extend(after);
        }
        original.push(0);
        candidate.push(0);
        let (mut source, mut names) = certificate(&original, &candidate, &rewrites, &[]).unwrap();
        source.push_str(
            r#"
theorem zero_dup_controls :
  GolfLayout.profile [128] = some (1,1,1) ∧
  GolfLayout.profile [96,0,128] = some (0,2,2) ∧
  GolfLayout.profile [96,0,95] = some (0,2,2) ∧
  ((GolfLayout.profile [96,0,96,0,80] == some (0,1,2) &&
      GolfLayout.profile [96,0,128] == some (0,1,2)) ||
    (GolfLayout.profile [96,0,96,0,80] == some (0,2,2) &&
      GolfLayout.profile [96,0,128] == some (0,2,2))) = false ∧
  GolfReflected.checkSite ⟨0,[96,1,128],[96,1,95],0⟩ = false ∧
  GolfReflected.checkSite ⟨0,[96,0,129],[96,0,95],0⟩ = false ∧
  GolfReflected.checkSite ⟨0,[96,0,128],[96,0,80],0⟩ = false ∧
  GolfReflected.checkSite ⟨0,[],[],0⟩ = false ∧
  GolfReflected.checkSite ⟨0,[97,0,128],[97,0,95],0⟩ = false ∧
  GolfReflected.checkSite ⟨0,[128,128],[128,95],0⟩ = false ∧
  GolfReflected.checkSite ⟨0,[95,0,128],[95,0,95],0⟩ = false ∧
  GolfReflected.checkSite ⟨0,[96,0,128],[96,1,95],0⟩ = false ∧
  GolfReflected.checkSite ⟨0,[97,0,0,128],[96,0,95],0⟩ = false ∧
  GolfReflected.checkSite ⟨0,[96,0,128],[96,0,95],1⟩ = false ∧
  GolfReflected.checkSite ⟨0,[96,0,128,128],[96,0,95,128],0⟩ = false ∧
  GolfReflected.checkSite ⟨0,95 :: List.replicate 1024 128,
    List.replicate 1025 95,0⟩ = false ∧
  GolfLayout.zeroChainProfile ⟨0,[96,0,128,128],[96,0,95,95],0⟩ = true := by decide +kernel
#print axioms zero_dup_controls
"#,
        );
        names.push("zero_dup_controls".into());
        let path = dir.path().join("ZeroDup.lean");
        fs::write(&path, &source).unwrap();
        proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational).unwrap();
        // A changed zero immediate must fail the aggregate proof, not only a leaf check.
        let mut bad_original = original.clone();
        let mut bad_candidate = candidate.clone();
        let mut bad_rewrites = rewrites;
        let byte = bad_rewrites[1].original_pc + 1;
        bad_original[byte] = 1;
        bad_candidate[byte] = 1;
        bad_rewrites[1].before = "600180".into();
        bad_rewrites[1].after = "60015f".into();
        let (source, names) =
            certificate(&bad_original, &bad_candidate, &bad_rewrites, &[]).unwrap();
        let path = dir.path().join("NonzeroDup.lean");
        fs::write(&path, source).unwrap();
        assert!(proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational).is_err());
    }

    #[test]
    #[ignore = "requires Lean 4.34.0"]
    fn binds_constant_codecopy_prefixes_and_actual_copied_bytes() {
        let dir = tempdir().unwrap();
        let original = from_hex("600760020250600260005f3900").unwrap();
        let candidate = from_hex("600760011b50600260005f3900").unwrap();
        let rewrite = Rewrite {
            original_pc: 2,
            before: "600202".into(),
            after: "60011b".into(),
            required_stack: 1,
        };
        let (source, names) = certificate(
            &original,
            &candidate,
            &[rewrite],
            &layout::code_copies(&original),
        )
        .unwrap();
        assert_eq!(names, ["layout_artifact", "codecopy_artifact"]);
        let check = |name: &str, source: &str, names: &[String]| {
            let path = dir.path().join(format!("{name}.lean"));
            fs::write(&path, source).unwrap();
            proof::verify_named(&path, names, proof::AxiomPolicy::Foundational)
        };
        check("DisjointCopy", &source, &names).unwrap();
        // Isolate the new root: reconstruction must not mask a broken copy gate.
        let start = source.find("theorem layout_artifact :").unwrap();
        let end = source.find("#print axioms layout_artifact\n").unwrap()
            + "#print axioms layout_artifact\n".len();
        let mut isolated = source.clone();
        isolated.replace_range(start..end, "");
        let names = vec!["codecopy_artifact".into()];
        check("CopyOnly", &isolated, &names).unwrap();
        for (name, image, bytes) in [
            ("OriginalCopy", "original", &original),
            ("CandidateCopy", "candidate", &candidate),
        ] {
            let mut changed = bytes.clone();
            changed[1] = 8;
            let tampered = isolated.replace(
                &format!("def {image} : List Nat := {bytes:?}"),
                &format!("def {image} : List Nat := {changed:?}"),
            );
            assert!(check(name, &tampered, &names).is_err());
        }
        // A changed destination leaves copied bytes and source bounds intact.
        let mut changed = candidate.clone();
        changed[10] = 0x30; // ADDRESS is not the certified PUSH0 destination.
        let tampered = isolated.replace(
            &format!("def candidate : List Nat := {candidate:?}"),
            &format!("def candidate : List Nat := {changed:?}"),
        );
        assert!(check("ChangedPrefix", &tampered, &names).is_err());
        // Matching literal bytes inside another PUSH are not instruction edges.
        let mut embedded = isolated.clone();
        for (image, bytes) in [("original", &original), ("candidate", &candidate)] {
            let mut changed = bytes.clone();
            changed[0] = 0x6b;
            embedded = embedded.replace(
                &format!("def {image} : List Nat := {bytes:?}"),
                &format!("def {image} : List Nat := {changed:?}"),
            );
        }
        assert!(check("EmbeddedPrefix", &embedded, &names).is_err());
        // Equal truncated slices do not prove an in-bounds copy. Use a matching
        // literal prefix on both sides, leaving only sourceBounds false.
        let mut bounds = isolated.clone();
        for (image, bytes) in [("original", &original), ("candidate", &candidate)] {
            let mut changed = bytes.clone();
            changed[7] = 32;
            changed[9] = 32;
            bounds = bounds.replace(
                &format!("def {image} : List Nat := {bytes:?}"),
                &format!("def {image} : List Nat := {changed:?}"),
            );
        }
        bounds = bounds.replace("⟨11, 6, 0, 2, 0⟩", "⟨11, 6, 32, 32, 0⟩");
        let root = bounds.find("theorem codecopy_artifact :").unwrap();
        let control = format!(
            "{}\ntheorem copy_bounds_control :\n  GolfArtifact.copies.all (fun site => GolfLayout.copyPrefix GolfArtifact.original site && GolfLayout.copyPrefix GolfArtifact.candidate site) = true ∧\n  GolfArtifact.copies.all (fun site => (GolfArtifact.original.drop site.source).take site.length == (GolfArtifact.candidate.drop site.source).take site.length) = true ∧\n  GolfArtifact.copies.all (fun site => site.source + site.length ≤ GolfArtifact.original.length && site.source + site.length ≤ GolfArtifact.candidate.length) = false := by decide +kernel\n#print axioms copy_bounds_control\n",
            &bounds[..root]
        );
        check(
            "BoundsCounterexample",
            &control,
            &["copy_bounds_control".into()],
        )
        .unwrap();
        assert!(check("OutOfBounds", &bounds, &names).is_err());
        let missing_report = isolated.replace("#print axioms codecopy_artifact", "");
        assert!(check("MissingCopyRoot", &missing_report, &names).is_err());
    }

    #[test]
    #[ignore = "requires Lean 4.34.0"]
    fn contextual_replacement_preserves_success_and_checks_its_boundaries() {
        let dir = tempdir().unwrap();
        let before = from_hex("600202").unwrap();
        let after = from_hex("60011b").unwrap();
        let rewrite = Rewrite {
            original_pc: 0,
            before: hex::encode(&before),
            after: hex::encode(&after),
            required_stack: 1,
        };
        let (mut source, mut names) = certificate(&before, &after, &[rewrite], &[]).unwrap();
        source.push_str(r#"theorem context_nonvacuous (x y : Golf.Word) :
  GolfBounded.run 9 [95,53,96,1,27,96,3,1] [] x y = some [3 + 2*x] := by
  exact GolfComposition.context_success (front := [95,53]) (suffix := [96,3,1])
    (GolfReflected.checkLocal_sound ⟨0, [96,2,2], [96,1,27], 1⟩ (by decide +kernel)).contextual ((GolfComposition.Complete.step (op := 95) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 53) (immediate := []) (by decide +kernel) GolfComposition.Complete.nil))) ((GolfComposition.Complete.step (op := 96) (immediate := [3]) (by decide +kernel) (GolfComposition.Complete.step (op := 1) (immediate := []) (by decide +kernel) GolfComposition.Complete.nil))) [] x y [3 + 2*x]
    (by simp [GolfBounded.run, Golf.run, Golf.immediate])
#print axioms context_nonvacuous
-- A changed shift immediate is a semantic error even when all boundaries match.
theorem changed_byte_matters :
    GolfBounded.run 9 [95,53,96,2,2,96,3,1] [] 1 0 ≠
      GolfBounded.run 9 [95,53,96,2,27,96,3,1] [] 1 0 := by decide +kernel

-- The front byte is a truncated PUSH1. Appending the local fragments changes
-- decoding and cannot be treated as executing the fragments at their starts.
theorem incomplete_boundary_matters :
    GolfBounded.run 5 ([96] ++ [96,2,2]) [0,1] 0 0 ≠
      GolfBounded.run 5 ([96] ++ [96,1,27]) [0,1] 0 0 := by decide +kernel

-- Termination itself needs one unit of fuel in the existing executor.
theorem inadequate_fuel_matters :
    GolfBounded.run 2 [95] [] 0 0 ≠ GolfBounded.run 1 [95] [] 0 0 := by decide +kernel

-- Erasing a mathematically neutral multiply would remove a real PUSH overflow.
theorem overflow_matters :
    GolfBounded.run 4 [96,1,2] (List.replicate 1024 0) 0 0 ≠
      GolfBounded.run 1 [] (List.replicate 1024 0) 0 0 := by decide +kernel

#print axioms changed_byte_matters
#print axioms incomplete_boundary_matters
#print axioms inadequate_fuel_matters
#print axioms overflow_matters
"#);
        let controls = [
            "changed_byte_matters",
            "incomplete_boundary_matters",
            "inadequate_fuel_matters",
            "overflow_matters",
        ];
        names.push("context_nonvacuous".into());
        names.extend(controls.map(str::to_owned));
        let path = dir.path().join("Context.lean");
        fs::write(&path, &source).unwrap();
        proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational).unwrap();
        // Each concrete counterexample is checked before asking Lean to reject
        // the corresponding false equality; failures cannot stand in for proofs.
        for name in controls {
            let start = source.find(&format!("theorem {name}")).unwrap();
            let end = start + source[start..].find(":= by decide +kernel").unwrap();
            let mut false_claim = source.clone();
            false_claim.replace_range(start..end, &source[start..end].replace('≠', "="));
            let path = dir.path().join(format!("{name}.lean"));
            fs::write(&path, false_claim).unwrap();
            assert!(proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational).is_err());
        }
        // Equality of two failed executions must never replace a successful
        // context witness. Mutate the actual bounded executor's termination.
        let path = dir.path().join("AlwaysFailing.lean");
        fs::write(
            &path,
            source.replace(
                STACK_MODEL,
                &STACK_MODEL.replace("    | [] => some stack", "    | [] => none"),
            ),
        )
        .unwrap();
        assert!(proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational).is_err());
    }
}
