//! Bind local layout certificates to the complete emitted byte arrays.

use anyhow::{Result, ensure};
use revm::primitives::HashMap;
use std::fmt::Write as _;

use super::{MAX_RUNTIME_BYTES, Rewrite, certificates, from_hex};

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
    writeln!(
        source,
        "\n{LAYOUT_MODEL}\nset_option maxRecDepth {ARTIFACT_RECURSION_LIMIT}\nset_option maxHeartbeats {ARTIFACT_HEARTBEATS}\nnamespace GolfArtifact"
    ).unwrap();
    // Embed both actual images independently; never define candidate by applying
    // the proposed patches, which would conceal errors in the Rust emitter.
    writeln!(source, "def original : List Nat := {original:?}").unwrap();
    writeln!(source, "def candidate : List Nat := {candidate:?}").unwrap();
    source.push_str("def sites : List GolfLayout.Site := [\n");
    let mut unique: HashMap<_, _> = HashMap::default();
    let mut proofs = Vec::new();
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
        proofs.push(index);
    }
    source.push_str(
        "]\nend GolfArtifact\n\ntheorem layout_artifact :\n  GolfLayout.LayoutArtifact GolfArtifact.original GolfArtifact.candidate GolfArtifact.sites := by\n  refine ⟨by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, ?_⟩\n  exact ",
    );
    for index in &proofs {
        write!(
            source,
            "(GolfLayout.CertifiedSites.cons runtime_rewrite_{index} "
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
            let (source, names) = certificate(original, candidate, rewrites).unwrap();
            let path = dir.path().join(format!("{name}.lean"));
            fs::write(&path, source).unwrap();
            proof::verify_named(&path, &names)
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
        // Both fragments are total identities with profile (1, 0, 1), and the
        // patch reconstructs the candidate, but instruction boundaries differ.
        let different_layout = Rewrite {
            original_pc: 0,
            before: "630000000102".into(),
            after: "600001600001".into(),
            required_stack: 1,
        };
        let (source, names) = certificates(std::slice::from_ref(&different_layout)).unwrap();
        let path = dir.path().join("BoundaryFragments.lean");
        fs::write(&path, source).unwrap();
        proof::verify_named(&path, &names).unwrap();
        assert!(
            check(
                "Boundaries",
                &from_hex("63000000010200").unwrap(),
                &from_hex("60000160000100").unwrap(),
                &[different_layout],
            )
            .is_err()
        );
        // A model-proved identity cannot use two failed stack profiles.
        let unsupported_profile = Rewrite {
            original_pc: 0,
            before: "19".into(),
            after: "19".into(),
            required_stack: 1,
        };
        assert!(check("Profile", &[0x19, 0], &[0x19, 0], &[unsupported_profile]).is_err());
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
        assert!(proof::verify_named(&path, &names).is_err());
    }
}
