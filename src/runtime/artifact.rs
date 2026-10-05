//! Bind local layout certificates to the complete emitted byte arrays.

use anyhow::{Result, ensure};
use std::{collections::BTreeMap, fmt::Write as _};

use super::{
    Instruction, MAX_PROPOSAL_SITES, MAX_RUNTIME_BYTES, Rewrite, decode, from_hex, layout, prelude,
    window_proposal::{self, WindowProof},
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
const LAYOUT_SCANNER: &str = include_str!("../../lean/LayoutScanner.lean");
const LAYOUT_MODEL: &str = include_str!("../../lean/Layout.lean");
const LAYOUT_CHUNKS: &str = include_str!("../../lean/LayoutChunks.lean");
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
    let mut source = prelude();
    writeln!(
        source,
        "\n{FRAGMENT_MODEL}\n{STACK_MODEL}\n{COMPOSITION_MODEL}\n{LAYOUT_SCANNER}\n{LAYOUT_MODEL}\n{LITERAL_MODEL}\n{ZERO_CHAIN_MODEL}"
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
    // Kernel checks never execute compiled code; skipping codegen for the
    // image literals avoids compiling ~24K-element lists for every proof.
    writeln!(
        source,
        "noncomputable def original : List Nat := {original:?}"
    )
    .unwrap();
    writeln!(
        source,
        "noncomputable def candidate : List Nat := {candidate:?}"
    )
    .unwrap();
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
    // Deciding equality of two full scans is slow in the kernel once the images
    // differ (see shared_scan), so artifacts with up to a batch of sites derive it from
    // shared gap rows. Larger site lists keep the direct decision.
    let same_layout = if rewrites.is_empty() || rewrites.len() > MAX_PROPOSAL_SITES {
        "by decide +kernel"
    } else {
        let decoded = rewrites
            .iter()
            .map(|rewrite| {
                Ok((
                    rewrite.original_pc,
                    from_hex(&rewrite.before)?,
                    from_hex(&rewrite.after)?,
                ))
            })
            .collect::<Result<Vec<_>>>()?;
        let sites: Vec<_> = decoded
            .iter()
            .map(|(pc, before, after)| (*pc, before.as_slice(), after.as_slice()))
            .collect();
        // Shapes the emitter cannot share keep the direct decision, so invalid
        // artifacts still fail in the kernel rather than in this generator.
        let mut shared = format!(
            "\n-- Shared scan rows for layout_artifact.\n{LAYOUT_CHUNKS}\nnamespace GolfArtifact\nopen GolfLayout\n"
        );
        let shape = |code| {
            decode(code)
                .iter()
                .map(|op| (op.pc, op.bytes.len(), op.bytes[0] == 0x5b))
                .collect::<Vec<_>>()
        };
        if sites
            .iter()
            .all(|(_, before, after)| shape(before) == shape(after))
            && shared_scan(&mut shared, original, candidate, &sites).is_ok()
        {
            source.push_str(&shared);
            let mut rows = Vec::new();
            for i in 0..sites.len() {
                writeln!(
                    source,
                    "theorem rows_{i} : oldRows_{i} = newRows_{i} := by decide +kernel"
                )
                .unwrap();
                rows.push(format!("rows_{i}"));
            }
            writeln!(source, "theorem sameLayout : scan original = scan candidate := by\n rw [originalShared, candidateShared, {}]\nend GolfArtifact", rows.join(", ")).unwrap();
            "GolfArtifact.sameLayout"
        } else {
            "by decide +kernel"
        }
    };
    writeln!(source,
        "\ntheorem layout_artifact :\n  GolfLayout.LayoutArtifact GolfArtifact.original GolfArtifact.candidate GolfArtifact.sites := by\n  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, {same_layout}, by decide +kernel, by decide +kernel, ?_⟩\n  exact GolfReflected.checkSites_sound GolfArtifact.sites (by decide +kernel)\n#print axioms layout_artifact",
    ).unwrap();
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

/// Emit `originalShared`/`candidateShared`: both independent images split into
/// the same symbolic unchanged gaps and per-site window rows. Requires the
/// LayoutChunks model and `original`/`candidate` definitions in scope. The
/// kernel then never compares two full scans, which took ~48s on one Balancer
/// image versus <1s for a single scan.
/// Returns each gap's start, end and scan fuel.
fn shared_scan(
    source: &mut String,
    original: &[u8],
    candidate: &[u8],
    windows: &[(usize, &[u8], &[u8])],
) -> Result<Vec<(usize, usize, usize)>> {
    // Full independent arrays stay above. Complete unchanged gaps are shared
    // symbolically; every rendered split and local row list is kernel checked.
    ensure!(
        original.len() == candidate.len(),
        "proposal candidate must preserve the original length"
    );
    let mut gaps = Vec::new();
    let mut chunks = [Vec::new(), Vec::new()];
    let mut rows = [Vec::new(), Vec::new()];
    let mut gap_start = 0;
    let count = windows.len();
    for site in 0..=count {
        let end = windows.get(site).map_or(original.len(), |window| window.0);
        ensure!(
            gap_start <= end && end <= original.len(),
            "proposal sites must be sorted, disjoint and inside the original"
        );
        let gap = &original[gap_start..end];
        ensure!(
            gap == &candidate[gap_start..end],
            "proposal candidate changes an unchanged gap"
        );
        let instructions = decode(gap);
        let fuel = if site < count {
            ensure!(
                complete(&instructions),
                "proposal boundary truncates a PUSH instruction"
            );
            instructions.len()
        } else {
            // The final gap may contain a truncated PUSH, like canonical scan.
            gap.len()
        };
        writeln!(source, "noncomputable def gap_{site} : List Nat := {gap:?}\ntheorem gap_{site}_length : gap_{site}.length = {} := by decide +kernel", gap.len()).unwrap();
        if site < count {
            writeln!(source, "theorem gap_{site}_complete : CompleteScanPrefix gap_{site} {fuel} := completeCount_sound (gap_{site}.length+1) gap_{site} {fuel} (by decide +kernel)\nnoncomputable def gapChunk_{site} : CompleteChunk := ⟨gap_{site}, {fuel}, gap_{site}_complete⟩").unwrap();
        }
        writeln!(
            source,
            "noncomputable def gapRows_{site} : List (Nat × Nat × Bool) := scanAux {fuel} {gap_start} gap_{site}"
        )
        .unwrap();
        gaps.push((gap_start, end, fuel));
        if site == count {
            break;
        }
        let (pc, before, after) = windows[site];
        gap_start = pc + before.len();
        ensure!(
            before.len() == after.len()
                && original.get(pc..gap_start) == Some(before)
                && candidate.get(pc..gap_start) == Some(after),
            "site bytes do not match both images"
        );
        ensure!(
            complete(&decode(before)) && complete(&decode(after)),
            "site truncates a PUSH instruction"
        );
        for ((side, code), (chunks, rows)) in [("old", before), ("new", after)]
            .into_iter()
            .zip(chunks.iter_mut().zip(rows.iter_mut()))
        {
            let instructions = decode(code);
            let operations = instructions.len();
            writeln!(source, "def {side}Chunk_{site} : CompleteChunk := ⟨{code:?}, {operations}, completeCount_sound ({}+1) {code:?} {operations} (by decide +kernel)⟩", code.len()).unwrap();
            write!(
                source,
                "def {side}Rows_{site} : List (Nat × Nat × Bool) := ["
            )
            .unwrap();
            for (index, instruction) in instructions.iter().enumerate() {
                write!(
                    source,
                    "{}({}, {}, {})",
                    if index == 0 { "" } else { ", " },
                    pc + instruction.pc,
                    instruction.bytes.len(),
                    instruction.bytes[0] == 0x5b
                )
                .unwrap();
            }
            writeln!(source, "]\ntheorem {side}Rows_{site}_exact : scanAux {operations} {pc} {code:?} = {side}Rows_{site} := by decide +kernel").unwrap();
            chunks.extend([format!("gapChunk_{site}"), format!("{side}Chunk_{site}")]);
            rows.extend([format!("gapRows_{site}"), format!("{side}Rows_{site}")]);
        }
    }
    let prefix_end = gaps.last().unwrap().0;
    for ((side, image), (chunks, rows)) in [("old", "original"), ("new", "candidate")]
        .into_iter()
        .zip(chunks.iter().zip(rows.iter_mut()))
    {
        writeln!(source, "noncomputable def {side}Chunks : List CompleteChunk := [{}]\ntheorem {image}_split : {image} = chunkBytes {side}Chunks ++ gap_{count} := by decide +kernel\ntheorem {side}Chunks_length : (chunkBytes {side}Chunks).length = {prefix_end} := by decide +kernel", chunks.join(", ")).unwrap();
        let mut definitions = vec![format!("{side}Chunks"), "chunkRows".into()];
        definitions.extend((0..count).map(|i| format!("gapChunk_{i}")));
        definitions.extend((0..count).map(|i| format!("{side}Chunk_{i}")));
        definitions.extend((0..count).map(|i| format!("gap_{i}_length")));
        definitions.extend((0..count).map(|i| format!("{side}Rows_{i}_exact")));
        definitions.extend(
            [
                "List.length_cons",
                "List.length_nil",
                "Nat.reduceAdd",
                "List.append_nil",
                "List.append_assoc",
            ]
            .map(str::to_owned),
        );
        // Associativity must be proved symbolically: rfl alone can normalize the
        // entire shared scan to reconcile differently associated append trees.
        writeln!(source, "theorem {side}Chunks_rows : chunkRows 0 {side}Chunks = {} := by\n simp only [{}] <;> rfl", rows.join(" ++ "), definitions.join(", ")).unwrap();
        rows.push(format!("gapRows_{count}"));
        writeln!(source, "theorem {image}Shared : scan {image} = {} := by\n rw [{image}_split, scan_complete_chunks, {side}Chunks_length, {side}Chunks_rows]\n simp only [gap_{count}_length, List.append_assoc] <;> rfl", rows.join(" ++ ")).unwrap();
    }
    Ok(gaps)
}

fn complete(instructions: &[Instruction]) -> bool {
    instructions.iter().all(|instruction| {
        let op = instruction.bytes[0];
        instruction.bytes.len()
            == if (0x60..=0x7f).contains(&op) {
                usize::from(op - 0x5f) + 1
            } else {
                1
            }
    })
}

/// One fresh proof binds every disjoint proposal to the immutable original.
/// Identical byte pairs share local theorems, never site occurrences.
pub(super) fn proposal_batch_certificate(
    original: &[u8],
    candidate: &[u8],
    rewrites: &[Rewrite],
    copies: &[layout::CodeCopy],
) -> Result<(String, Vec<String>)> {
    ensure!(
        original.len() <= MAX_RUNTIME_BYTES && candidate.len() <= MAX_RUNTIME_BYTES,
        "proposal batch artifact exceeds EIP-170 size limit"
    );
    ensure!(
        !rewrites.is_empty() && rewrites.len() <= MAX_PROPOSAL_SITES,
        "proposal batch requires 1..={MAX_PROPOSAL_SITES} sites"
    );
    let mut unique = BTreeMap::new();
    let mut proofs: Vec<(Vec<u8>, Vec<u8>, WindowProof)> = Vec::new();
    let mut indexes = Vec::with_capacity(rewrites.len());
    let mut previous_end = 0;
    for rewrite in rewrites {
        let before = from_hex(&rewrite.before)?;
        let after = from_hex(&rewrite.after)?;
        let end = rewrite
            .original_pc
            .checked_add(before.len())
            .ok_or_else(|| anyhow::anyhow!("proposal site range overflow"))?;
        ensure!(
            rewrite.original_pc >= previous_end && end <= original.len(),
            "proposal sites must be sorted, disjoint and inside the original"
        );
        ensure!(
            original[rewrite.original_pc..end] == before,
            "proposal bytes do not match immutable original"
        );
        let key = (before.clone(), after.clone());
        let index = if let Some(&index) = unique.get(&key) {
            index
        } else {
            let index = proofs.len();
            let local = window_proposal::certificate_for_pair(&before, &after, index)?;
            proofs.push((before, after, local));
            unique.insert(key, index);
            index
        };
        ensure!(
            rewrite.required_stack == proofs[index].2.required,
            "proposal stack metadata mismatch"
        );
        indexes.push(index);
        previous_end = end;
    }
    let mut source = window_proposal::batch_prelude()?;
    let mut names = Vec::new();
    for (_, _, proof) in &proofs {
        source.push_str(&proof.source);
        names.extend(proof.names.iter().cloned());
    }
    writeln!(source,"\nset_option maxRecDepth {ARTIFACT_RECURSION_LIMIT}\nset_option maxHeartbeats {ARTIFACT_HEARTBEATS}\n{}\n{}\n{}\n{}",
        include_str!("../../lean/GenericWindowArtifact.lean"),include_str!("../../lean/GenericWindowBatch.lean"),
        include_str!("../../lean/LayoutChunks.lean"),include_str!("../../lean/GenericWindowScan.lean")).unwrap();
    source.push_str("\nnamespace GolfProposedBatch\nopen GolfLayout GolfGenericWindow\n");
    for (index, (before, after, proof)) in proofs.iter().enumerate() {
        let namespace = format!("GolfGenerated.Pair{index}");
        writeln!(source,"def certificate_{index} (pc : Nat) : GenericLocal ⟨pc,{before:?},{after:?},{}⟩ {} ({}) {} {} {} where
 requiredExact := rfl
 feasible := by decide
 nonemptyBefore := by change ({before:?} : List Nat) ≠ []; decide +kernel
 nonemptyAfter := by change ({after:?} : List Nat) ≠ []; decide +kernel
 sameLength := by change ({before:?} : List Nat).length = ({after:?} : List Nat).length; decide +kernel
 beforeBytes := {namespace}.before_bytes
 afterBytes := {namespace}.after_bytes
 beforeSupported := by change GolfGenericWindow.supported ({before:?} : List Nat) = true; decide +kernel
 afterSupported := by change GolfGenericWindow.supported ({after:?} : List Nat) = true; decide +kernel
 beforeComplete := {namespace}.before_complete
 afterComplete := {namespace}.after_complete
 beforeProfile := {namespace}.before_profile
 afterProfile := {namespace}.after_profile
 output := {namespace}.output
 success := {namespace}.success
 underflow := {namespace}.underflow
 overflow := {namespace}.overflow
 allHeight := {namespace}.all_height
 context := {namespace}.context
 faultClasses := {namespace}.fault_classes",proof.required,proof.required,proof.delta,proof.peak,proof.before_ops,proof.after_ops).unwrap();
    }
    for (site, (rewrite, &index)) in rewrites.iter().zip(&indexes).enumerate() {
        let (before, after, proof) = &proofs[index];
        writeln!(
            source,
            "def site_{site} : Site := ⟨{}, {before:?}, {after:?}, {}⟩",
            rewrite.original_pc, proof.required
        )
        .unwrap();
    }
    let sites = (0..rewrites.len())
        .map(|i| format!("site_{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    writeln!(source,"def sites : List Site := [{sites}]\ndef locals : GolfGenericWindowBatch.CertifiedLocals sites :=").unwrap();
    for (rewrite, index) in rewrites.iter().zip(&indexes) {
        writeln!(
            source,
            " GolfGenericWindowBatch.CertifiedLocals.cons (certificate_{index} {}) (",
            rewrite.original_pc
        )
        .unwrap();
    }
    source.push_str(" GolfGenericWindowBatch.CertifiedLocals.nil");
    for _ in rewrites {
        source.push(')');
    }
    source.push('\n');
    // Both complete arrays are independent inputs, not an application-defined candidate.
    writeln!(source,"noncomputable def original : List Nat := {original:?}\nnoncomputable def candidate : List Nat := {candidate:?}\ndef copies : List GolfLayout.CodeCopy := [").unwrap();
    for (i, copy) in copies.iter().enumerate() {
        writeln!(
            source,
            " ⟨{}, {}, {}, {}, {}⟩{}",
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
    let windows: Vec<_> = rewrites
        .iter()
        .zip(&indexes)
        .map(|(rewrite, &index)| {
            let (before, after, _) = &proofs[index];
            (rewrite.original_pc, before.as_slice(), after.as_slice())
        })
        .collect();
    let gaps = shared_scan(&mut source, original, candidate, &windows)?;
    let count = rewrites.len();
    for (site, &(gap_start, end, fuel)) in gaps.iter().enumerate() {
        writeln!(source, "theorem gapBounds_{site} (row : GolfGenericWindow.Row) (member : row ∈ gapRows_{site}) :
 {gap_start} ≤ row.1 ∧ row.1 < {end} := by
 refine ⟨scanAux_lower {fuel} {gap_start} gap_{site} row member, ?_⟩
 simpa only [gap_{site}_length, Nat.reduceAdd] using scanAux_upper {fuel} {gap_start} gap_{site} row member
theorem gapDisjoint_{site} : ∀ site ∈ sites,
 {end} ≤ site.pc ∨ site.pc+site.before.length ≤ {gap_start} := by
 have checked : sites.all (fun site => decide ({end} ≤ site.pc ∨ site.pc+site.before.length ≤ {gap_start})) = true := by decide +kernel
 intro site member
 exact of_decide_eq_true (List.all_eq_true.mp checked site member)
theorem gapExterior_{site} : GolfGenericWindowBatch.exterior sites gapRows_{site} = gapRows_{site} :=
 GolfSharedSuffix.exterior_gap sites gapRows_{site} {gap_start} {end} gapBounds_{site} gapDisjoint_{site}
theorem gapNoInterior_{site} (site : Site) (member : site ∈ sites) : noInterior site gapRows_{site} = true :=
 GolfSharedSuffix.noInterior_gap site gapRows_{site} {gap_start} {end} gapBounds_{site} (gapDisjoint_{site} site member)").unwrap();
    }
    for site in 0..count {
        for side in ["old", "new"] {
            writeln!(source, "theorem {side}Exterior_{site} : GolfGenericWindowBatch.exterior sites {side}Rows_{site} = [] := by decide +kernel\ntheorem {side}Jumps_{site} : jumps {side}Rows_{site} = [] := by decide +kernel\ntheorem {side}NoInterior_{site} : sites.all (fun site => noInterior site {side}Rows_{site}) = true := by decide +kernel").unwrap();
        }
    }
    let [old_rows, new_rows] = ["old", "new"].map(|side| {
        let mut rows: Vec<_> = (0..count)
            .flat_map(|i| [format!("gapRows_{i}"), format!("{side}Rows_{i}")])
            .collect();
        rows.push(format!("gapRows_{count}"));
        rows
    });
    source.push_str("theorem exterior_append (sites : List Site) (left right : List GolfGenericWindow.Row) :\n GolfGenericWindowBatch.exterior sites (left ++ right) =\n GolfGenericWindowBatch.exterior sites left ++ GolfGenericWindowBatch.exterior sites right := List.filter_append ..\ntheorem jumps_append (left right : List GolfGenericWindow.Row) :\n jumps (left ++ right) = jumps left ++ jumps right := by\n simp only [jumps, List.filter_append, List.map_append]\n");
    for (theorem, function, distribution, property) in [
        (
            "exteriorShared",
            "GolfGenericWindowBatch.exterior sites",
            "exterior_append",
            "Exterior",
        ),
        ("jumpsShared", "jumps", "jumps_append", "Jumps"),
    ] {
        let mut lemmas = vec![
            "originalShared".to_owned(),
            "candidateShared".to_owned(),
            distribution.to_owned(),
        ];
        for side in ["old", "new"] {
            lemmas.extend((0..count).map(|i| format!("{side}{property}_{i}")));
        }
        lemmas.extend(["List.nil_append".to_owned(), "List.append_nil".to_owned()]);
        if property == "Exterior" {
            lemmas.extend((0..=count).map(|i| format!("gapExterior_{i}")));
        }
        writeln!(source, "theorem {theorem} : {function} (scan original) = {function} (scan candidate) := by\n simp only [{}]", lemmas.join(", ")).unwrap();
    }
    for (side, image, rows) in [
        ("old", "original", old_rows),
        ("new", "candidate", new_rows),
    ] {
        writeln!(source, "theorem {side}NoInterior : sites.all (fun site => noInterior site (scan {image})) = true := by\n rw [{image}Shared]\n apply List.all_eq_true.mpr\n intro site member").unwrap();
        for i in 0..count {
            writeln!(source, " have h{i} : noInterior site {side}Rows_{i} = true := List.all_eq_true.mp {side}NoInterior_{i} site member").unwrap();
        }
        let terms = rows
            .iter()
            .map(|row| format!("noInterior site {row}"))
            .collect::<Vec<_>>()
            .join(" && ");
        let lemmas = (0..=count)
            .map(|i| format!("gapNoInterior_{i} site member"))
            .chain((0..count).map(|i| format!("h{i}")))
            .collect::<Vec<_>>()
            .join(", ");
        writeln!(source, " simp only [noInterior, List.all_append]\n change ({terms}) = true\n rw [{lemmas}]\n rfl").unwrap();
    }
    source.push_str("noncomputable def artifact : GolfGenericWindowBatch.Artifact original candidate sites copies := by\n refine ⟨locals, ?_⟩\n exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,\n   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,\n   exteriorShared,jumpsShared,oldNoInterior,newNoInterior,\n   by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩\nend GolfProposedBatch\n#print axioms GolfProposedBatch.artifact\n");
    names.push("GolfProposedBatch.artifact".into());
    Ok((source, names))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proof;
    use revm::primitives::{U256, hex};
    use std::fs;
    use tempfile::tempdir;

    // Unbounded local theorems for single fragments, used to isolate global gates.
    fn certificates(rewrites: &[Rewrite]) -> anyhow::Result<(String, Vec<String>)> {
        let mut source = crate::runtime::prelude();
        let mut names = Vec::new();
        // Repeated sites share the same local theorem; source locations remain in JSON.
        let mut seen = std::collections::BTreeSet::new();
        for rewrite in rewrites {
            if !seen.insert((&rewrite.before, &rewrite.after, rewrite.required_stack)) {
                continue;
            }
            let before = from_hex(&rewrite.before)?;
            let after = from_hex(&rewrite.after)?;
            let name = format!("runtime_rewrite_{}", names.len());
            let stack = if rewrite.required_stack == 0 {
                "tail"
            } else {
                "a :: tail"
            };
            source.push_str(&format!("theorem {name} (a x y : Golf.Word) (tail : List Golf.Word) :\n  ∃ output, Golf.run {} {:?} ({stack}) x y = some output ∧\n    Golf.run {} {:?} ({stack}) x y = some output := by\n  refine ⟨_, rfl, ?_⟩\n  simp [Golf.run, Golf.immediate, GolfProof.shift_one, GolfProof.shift_power, BitVec.mul_two, BitVec.two_mul, BitVec.mul_comm]\n#print axioms {name}\n\n", before.len()+1, before, after.len()+1, after));
            names.push(name);
        }
        Ok((source, names))
    }

    #[test]
    fn proposal_batch_rejects_unbound_gaps_and_incomplete_boundaries() {
        let before = from_hex("600150600250").unwrap();
        let after = from_hex("630000000050").unwrap();
        let rewrite = Rewrite {
            original_pc: 0,
            before: hex::encode(&before),
            after: hex::encode(&after),
            required_stack: 0,
        };
        let original = [before.clone(), vec![0x5b, 0]].concat();
        let changed_suffix = [after.clone(), vec![0x5a, 0]].concat();
        assert!(proposal_batch_certificate(&original, &changed_suffix, &[rewrite], &[]).is_err());

        let original = [vec![0x5b], before.clone()].concat();
        let candidate = [vec![0x5a], after.clone()].concat();
        let rewrite = Rewrite {
            original_pc: 1,
            before: hex::encode(&before),
            after: hex::encode(&after),
            required_stack: 0,
        };
        assert!(proposal_batch_certificate(&original, &candidate, &[rewrite], &[]).is_err());

        // The proposed interval is embedded in an outer PUSH8's immediate.
        // Its endpoint therefore cannot certify a complete decoded prefix.
        let original = [vec![0x67], before, vec![0, 0]].concat();
        let candidate = [vec![0x67], after, vec![0, 0]].concat();
        let rewrite = Rewrite {
            original_pc: 1,
            before: "600150600250".into(),
            after: "630000000050".into(),
            required_stack: 0,
        };
        assert!(proposal_batch_certificate(&original, &candidate, &[rewrite], &[]).is_err());
    }

    #[test]
    #[ignore = "requires Lean 4.34.0"]
    fn proposal_batch_shared_gaps_are_kernel_bound() {
        let before = from_hex("605b50600150").unwrap();
        let after = from_hex("630000000050").unwrap();
        let rewrite = Rewrite {
            original_pc: 1,
            before: hex::encode(&before),
            after: hex::encode(&after),
            required_stack: 0,
        };
        let directory = tempdir().unwrap();
        for (index, suffix) in [vec![0, 0x61, 0xff], vec![]].into_iter().enumerate() {
            // JUMPDEST inside the PUSH immediate is data; a truncated final PUSH
            // in the unchanged suffix is still represented by canonical scan.
            let original = [vec![0x5b], before.clone(), suffix.clone()].concat();
            let candidate = [vec![0x5b], after.clone(), suffix].concat();
            let (source, names) = proposal_batch_certificate(
                &original,
                &candidate,
                std::slice::from_ref(&rewrite),
                &[],
            )
            .unwrap();
            let path = directory.path().join(format!("Shared{index}.lean"));
            fs::write(&path, &source).unwrap();
            let checked = proof::verify_named(&path, &names);
            assert!(
                checked.is_ok(),
                "{checked:?}\n{}",
                fs::read_to_string(path.with_extension("log")).unwrap_or_default()
            );
            if index == 0 {
                for (label, correct, wrong) in [
                    (
                        "Suffix",
                        "def gap_1 : List Nat := [0, 97, 255]",
                        "def gap_1 : List Nat := [0, 97, 254]",
                    ),
                    ("Pc", "scanAux 3 7 gap_1", "scanAux 3 8 gap_1"),
                    (
                        "Count",
                        "gap_0 1 (by decide +kernel)",
                        "gap_0 0 (by decide +kernel)",
                    ),
                ] {
                    let changed = source.replacen(correct, wrong, 1);
                    assert_ne!(source, changed, "missing mutation {label}");
                    let path = directory.path().join(format!("Wrong{label}.lean"));
                    fs::write(&path, changed).unwrap();
                    assert!(
                        proof::verify_named(&path, &names).is_err(),
                        "accepted {label} corruption"
                    );
                }
            }
        }
    }

    #[test]
    #[ignore = "requires Lean 4.34.0"]
    fn proposal_batch_adjacent_sites_have_empty_shared_gaps() {
        let before = from_hex("600150600250").unwrap();
        let after = from_hex("630000000050").unwrap();
        let original = [before.clone(), before.clone()].concat();
        let candidate = [after.clone(), after.clone()].concat();
        let rewrites = [0, before.len()].map(|original_pc| Rewrite {
            original_pc,
            before: hex::encode(&before),
            after: hex::encode(&after),
            required_stack: 0,
        });
        let (source, names) =
            proposal_batch_certificate(&original, &candidate, &rewrites, &[]).unwrap();
        let directory = tempdir().unwrap();
        let path = directory.path().join("Adjacent.lean");
        fs::write(&path, source).unwrap();
        let checked = proof::verify_named(&path, &names);
        assert!(
            checked.is_ok(),
            "{checked:?}\n{}",
            fs::read_to_string(path.with_extension("log")).unwrap_or_default()
        );
    }

    #[test]
    fn proposal_batches_share_proofs_without_dropping_sites() {
        let before = from_hex("600116600116").unwrap();
        let after = from_hex("630000000116").unwrap();
        let original = [before.clone(), before.clone(), vec![0]].concat();
        let candidate = [after.clone(), after.clone(), vec![0]].concat();
        let rows: Vec<_> = [0, 6]
            .into_iter()
            .map(|pc| Rewrite {
                original_pc: pc,
                before: hex::encode(&before),
                after: hex::encode(&after),
                required_stack: 1,
            })
            .collect();
        let (source, names) =
            proposal_batch_certificate(&original, &candidate, &rows, &[]).unwrap();
        assert_eq!(names.len(), 11);
        assert_eq!(source.matches("namespace Golf\n").count(), 1);
        assert_eq!(source.matches("namespace GolfGeneratedFault\n").count(), 1);
        assert!(!source.contains("namespace GolfGenerated.Pair1"));
        assert!(source.contains("certificate_0 0"));
        assert!(source.contains("certificate_0 6"));
        assert!(source.contains("def sites : List Site := [site_0, site_1]"));
        assert_eq!(names.last().unwrap(), "GolfProposedBatch.artifact");
    }

    #[test]
    fn proposal_batches_reject_invalid_shape_before_proof_emission() {
        let before = from_hex("600116600116").unwrap();
        let after = from_hex("630000000116").unwrap();
        let row = |pc, required| Rewrite {
            original_pc: pc,
            before: hex::encode(&before),
            after: hex::encode(&after),
            required_stack: required,
        };
        assert!(proposal_batch_certificate(&before, &after, &[], &[]).is_err());
        assert!(proposal_batch_certificate(&before, &after, &[row(0, 0)], &[]).is_err());
        assert!(proposal_batch_certificate(&before, &after, &[row(usize::MAX, 1)], &[]).is_err());
        assert!(proposal_batch_certificate(&before, &after, &[row(0, 1), row(0, 1)], &[]).is_err());
        let rows: Vec<_> = (0..33).map(|_| row(0, 1)).collect();
        assert!(proposal_batch_certificate(&before, &after, &rows, &[]).is_err());
    }

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
                proposal_batch_certificate(&original, &candidate, std::slice::from_ref(&site), &[])
                    .unwrap();
            let path = dir.path().join(format!("Proposal{i}.lean"));
            fs::write(&path, source).unwrap();
            let checked = proof::verify_named(&path, &names);
            assert!(
                checked.is_ok(),
                "{checked:?}\n{}",
                fs::read_to_string(path.with_extension("log")).unwrap_or_default()
            );
            if i == 1 {
                // An unrelated exterior change must fail in the generator or
                // in the kernel; it is never certified.
                let mut corrupted = candidate;
                *corrupted.last_mut().unwrap() = 0x5b;
                if let Ok((source, names)) = proposal_batch_certificate(
                    &original,
                    &corrupted,
                    std::slice::from_ref(&site),
                    &[],
                ) {
                    let path = dir.path().join("ChangedExterior.lean");
                    fs::write(&path, source).unwrap();
                    assert!(proof::verify_named(&path, &names).is_err());
                }
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
            proof::verify_named(&path, &names)
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
            proof::verify_named(&path, &names)
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
            proof::verify_named(&path, &names)
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
            proof::verify_named(&path, &names)
        };
        check("Valid", &original, &candidate, &rewrites).unwrap();
        // The shared-row layout proof must bind every rendered row and offset.
        let (source, names) = certificate(&original, &candidate, &rewrites, &[]).unwrap();
        assert!(source.contains("theorem sameLayout"));
        for (label, correct, wrong) in [
            ("GapPc", "scanAux 1 8 gap_2", "scanAux 1 9 gap_2"),
            (
                "WindowRow",
                "[(5, 2, false), (7, 1, false)]",
                "[(5, 2, false), (7, 1, true)]",
            ),
        ] {
            let changed = source.replacen(correct, wrong, 1);
            assert_ne!(source, changed, "missing mutation {label}");
            let path = dir.path().join(format!("Shared{label}.lean"));
            fs::write(&path, changed).unwrap();
            assert!(
                proof::verify_named(&path, &names).is_err(),
                "accepted {label} corruption"
            );
        }
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
            proof::verify_named(&path, &positive_names).unwrap_or_else(|error| {
                panic!(
                    "{error:#}\n{}",
                    fs::read_to_string(path.with_extension("log")).unwrap_or_default()
                )
            });
            let path = dir.path().join(format!("{name}.lean"));
            fs::write(&path, checked_source).unwrap();
            assert!(proof::verify_named(&path, &names).is_err());
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
        assert!(proof::verify_named(&path, &names).is_err());
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
        assert!(proof::verify_named(&path, &names).is_err());
        // A correct aggregate type must not hide an untrusted local proof.
        let path = dir.path().join("UntrustedLocal.lean");
        fs::write(&path, source
            .replace("theorem layout_artifact :", "axiom unsupported_local (sites : List GolfLayout.Site) : GolfReflected.checkSites sites = true → GolfLayout.CertifiedSites sites\ntheorem layout_artifact :")
            .replace("GolfReflected.checkSites_sound GolfArtifact.sites", "unsupported_local GolfArtifact.sites"))
            .unwrap();
        let error = proof::verify_named(&path, &names).unwrap_err();
        assert!(format!("{error:#}").contains("unexpected axiom dependency: unsupported_local"));
        let path = dir.path().join("MissingAggregateReport.lean");
        fs::write(&path, source.replace("#print axioms layout_artifact", "")).unwrap();
        assert!(proof::verify_named(&path, &names).is_err());
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
            proof::verify_named(&path, names)
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
        proof::verify_named(&path, &names).unwrap();
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
        assert!(proof::verify_named(&path, &names).is_err());
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
            proof::verify_named(&path, names)
        };
        check("DisjointCopy", &source, &names).unwrap();
        // Isolate the new root: reconstruction must not mask a broken copy gate.
        let start = source
            .find("-- Shared scan rows for layout_artifact.")
            .unwrap();
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
        proof::verify_named(&path, &names).unwrap();
        // Each concrete counterexample is checked before asking Lean to reject
        // the corresponding false equality; failures cannot stand in for proofs.
        for name in controls {
            let start = source.find(&format!("theorem {name}")).unwrap();
            let end = start + source[start..].find(":= by decide +kernel").unwrap();
            let mut false_claim = source.clone();
            false_claim.replace_range(start..end, &source[start..end].replace('≠', "="));
            let path = dir.path().join(format!("{name}.lean"));
            fs::write(&path, false_claim).unwrap();
            assert!(proof::verify_named(&path, &names).is_err());
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
        assert!(proof::verify_named(&path, &names).is_err());
    }
}
