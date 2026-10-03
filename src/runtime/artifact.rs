//! Bind local layout certificates to the complete emitted byte arrays.

use anyhow::{Result, ensure};
use revm::primitives::HashMap;
use std::fmt::Write as _;

use super::{MAX_RUNTIME_BYTES, Rewrite, certificates, from_hex};

const STACK_MODEL: &str = include_str!("../../lean/Stack.lean");
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
) -> Result<(String, Vec<String>)> {
    ensure!(
        original.len() <= MAX_RUNTIME_BYTES && candidate.len() <= MAX_RUNTIME_BYTES,
        "layout artifact exceeds EIP-170 size limit"
    );
    ensure!(
        rewrites.iter().all(|rewrite| rewrite.required_stack == 1),
        "layout artifacts require one-word fragment prefixes"
    );
    let (mut source, mut names) = certificates(rewrites)?;
    writeln!(source, "\n{STACK_MODEL}\n{LAYOUT_MODEL}").unwrap();
    writeln!(
        source,
        "\nset_option maxRecDepth {ARTIFACT_RECURSION_LIMIT}\nset_option maxHeartbeats {ARTIFACT_HEARTBEATS}\nnamespace GolfArtifact"
    ).unwrap();
    // Embed both actual images independently; never define candidate by applying
    // the proposed patches, which would conceal errors in the Rust emitter.
    writeln!(source, "def original : List Nat := {original:?}").unwrap();
    writeln!(source, "def candidate : List Nat := {candidate:?}").unwrap();
    source.push_str("def sites : List GolfLayout.Site := [\n");
    let mut unique: HashMap<_, _> = HashMap::default();
    let mut proofs = Vec::new();
    let mut bounded = String::new();
    for (i, rewrite) in rewrites.iter().enumerate() {
        let before = from_hex(&rewrite.before)?;
        let after = from_hex(&rewrite.after)?;
        writeln!(
            source,
            "  ⟨{}, {before:?}, {after:?}⟩{}",
            rewrite.original_pc,
            if i + 1 == rewrites.len() { "" } else { "," }
        )
        .unwrap();
        // Match certificates()'s first-seen deduplication order while retaining
        // every concrete site in the final theorem.
        let next = unique.len();
        let index = *unique
            .entry((
                rewrite.before.as_str(),
                rewrite.after.as_str(),
                rewrite.required_stack,
            ))
            .or_insert(next);
        if index == next {
            let name = format!("runtime_bounded_{index}");
            writeln!(
                bounded,
                "theorem {name} : GolfBounded.FragmentEquivalent {before:?} {after:?} := by"
            )
            .unwrap();
            writeln!(
                bounded,
                "  apply GolfBounded.of_unbounded (before := {before:?}) (after := {after:?}) ?_ ?_ runtime_rewrite_{index}"
            )
            .unwrap();
            for bytes in [&before, &after] {
                ensure!(
                    bytes.len() >= 2,
                    "layout fragment must contain PUSH and binary opcode"
                );
                writeln!(bounded, "  · exact GolfBounded.push_binary {:?} {} (by decide +kernel) (by decide +kernel)", &bytes[1..bytes.len()-1], bytes[bytes.len()-1]).unwrap();
            }
            writeln!(bounded, "#print axioms {name}\n").unwrap();
            names.push(name);
        }
        proofs.push(index);
    }
    // Check and cache each closed fact directly in Lean's kernel. Repeated
    // elaborator reduction with `rfl` exhausted the same 60-second budget on
    // dense EIP-170 artifacts. This is not native evaluation or a new axiom.
    source.push_str("]\nend GolfArtifact\n\n");
    source.push_str(&bounded);
    source.push_str(
        "theorem layout_artifact :\n  GolfLayout.LayoutArtifact GolfArtifact.original GolfArtifact.candidate GolfArtifact.sites := by\n  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩\n  exact ",
    );
    for index in &proofs {
        write!(
            source,
            "(GolfLayout.CertifiedSites.cons runtime_rewrite_{index} runtime_bounded_{index} "
        )
        .unwrap();
    }
    source.push_str("GolfLayout.CertifiedSites.nil");
    for _ in proofs {
        source.push(')');
    }
    source.push_str("\n#print axioms layout_artifact\n");
    names.push("layout_artifact".into());
    Ok((source, names))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proof;
    use revm::primitives::hex;
    use std::fs;
    use tempfile::tempdir;

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
            let (source, names) = certificate(original, candidate, rewrites)?;
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
        for width in 0..=32 {
            for value in 0..=2 {
                if width == 0 && value != 0 {
                    continue;
                }
                let mut before = vec![0x5f + width];
                let mut after = before.clone();
                if width > 0 {
                    before.extend(std::iter::repeat_n(0, usize::from(width) - 1));
                    after.extend(std::iter::repeat_n(0, usize::from(width) - 1));
                    before.push(value);
                    after.push(u8::from(value == 2));
                }
                before.push(0x02);
                after.push(match value {
                    0 => 0x16,
                    1 => 0x01,
                    _ => 0x1b,
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
            let (source, names) = certificate(&original, &candidate, &[rewrite]).unwrap();
            let mut checked_source = String::new();
            for line in source.lines() {
                if line.starts_with("  · exact GolfBounded.push_binary") {
                    checked_source.push_str("  · exact ");
                    checked_source.push_str(direct_behavior);
                    checked_source.push('\n');
                } else {
                    checked_source.push_str(line);
                    checked_source.push('\n');
                }
            }
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
  exact GolfLayout.CertifiedSites.cons runtime_rewrite_0 runtime_bounded_0 GolfLayout.CertifiedSites.nil
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
        let (source, names) = certificate(&original, &candidate, &rewrites).unwrap();
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
        let (source, names) = certificate(&original, &candidate, &rewrites).unwrap();
        let path = dir.path().join("WrongTheorem.lean");
        fs::write(
            &path,
            source.replace(
                "CertifiedSites.cons runtime_rewrite_1",
                "CertifiedSites.cons runtime_rewrite_0",
            ),
        )
        .unwrap();
        assert!(proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational).is_err());
    }
}
