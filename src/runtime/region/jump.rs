//! Exact full-image jump membership from bounded, instruction-aligned prefixes.

use anyhow::{Context as _, Result, ensure};
use std::fmt::Write as _;

use super::{ImageLeaf, MAX_RUNTIME_BYTES, RenderedImages};

const CHUNK_BYTES: usize = 128;
const CHUNK_INSTRUCTIONS: usize = 32;
const NAMESPACE: &str = "GolfCertificates.JumpMembership";
type Module = (String, String, Vec<String>);

#[derive(Clone)]
struct Part {
    code: String,
    size: String,
    route: String,
    complete: String,
    module: String,
    base: usize,
    len: usize,
    steps: usize,
}

#[derive(Default)]
struct Generator {
    modules: Vec<Module>,
    covers: usize,
    chunks: usize,
    nodes: usize,
}

impl Generator {
    fn emit(&mut self, name: &str, imports: &[String], body: &str, roots: &[String]) {
        let mut source = String::new();
        for (index, import) in imports.iter().enumerate() {
            if !imports[..index].contains(import) {
                writeln!(source, "import {import}").unwrap();
            }
        }
        writeln!(source, "set_option Elab.async false\nset_option maxRecDepth 4096\nset_option maxHeartbeats 2000000\nopen EvmYul EvmYul.EVM GolfLayout GolfByteRouting GolfCertificates\nnamespace {NAMESPACE}\n{body}\nend {NAMESPACE}").unwrap();
        let names: Vec<_> = roots
            .iter()
            .map(|root| format!("{NAMESPACE}.{root}"))
            .collect();
        for root in &names {
            writeln!(source, "#print axioms {root}").unwrap();
        }
        self.modules.push((name.to_owned(), source, names));
    }

    fn chunk(
        &mut self,
        side: &str,
        bytes: &[u8],
        base: usize,
        steps: usize,
        leaves: &[&ImageLeaf],
    ) -> Result<Part> {
        let name = format!("JumpChunk{}", self.chunks);
        self.chunks += 1;
        let len = bytes.len();
        let literal = bytes
            .iter()
            .map(u8::to_string)
            .collect::<Vec<_>>()
            .join(",");
        let mut body = format!(
            "def {name} : ByteArray := ⟨#[{literal}]⟩\ntheorem {name}_size : {name}.size = {len} := rfl\ntheorem {name}_complete : CompleteScanPrefix ({name}.data.toList.map UInt8.toNat) {steps} := by\n change CompleteScanPrefix [{literal}] {steps}\n"
        );
        let mut pc = 0;
        let mut remaining = steps;
        while pc < len {
            let op = bytes[pc];
            let width = push_width(op);
            let immediate = &bytes[pc + 1..pc + 1 + width];
            remaining -= 1;
            writeln!(
                body,
                " refine CompleteScanPrefix.cons {op} {immediate:?} _ {remaining} rfl ?_"
            )
            .unwrap();
            pc += 1 + width;
        }
        body.push_str(" exact CompleteScanPrefix.nil\n");
        let mut imports = vec!["Images".to_owned(), "CheckedRouteSupport".to_owned()];
        let mut roots = vec![format!("{name}_size"), format!("{name}_complete")];
        if bytes.is_empty() {
            writeln!(body, "theorem {name}_route : Route {side}Code 0 {name} := GolfJumpRoute.empty_route {side}Code").unwrap();
        } else {
            let covering: Vec<_> = leaves
                .iter()
                .copied()
                .filter(|leaf| leaf.base < base + len && base < leaf.base + leaf.len)
                .collect();
            let first = covering
                .first()
                .context("missing image route for scanner prefix")?;
            let mut cover = Part {
                code: first.code.clone(),
                size: first.size.clone(),
                route: first.route.clone(),
                complete: String::new(),
                module: "Images".into(),
                base: first.base,
                len: first.len,
                steps: 0,
            };
            for leaf in covering.iter().skip(1) {
                ensure!(
                    cover.base + cover.len == leaf.base,
                    "noncontiguous image routes"
                );
                let next = format!("JumpCover{}", self.covers);
                self.covers += 1;
                let full_len = cover.len + leaf.len;
                let proof = format!(
                    "def {next} : ByteArray := ⟨{}.data ++ {}.data⟩\ntheorem {next}_size : {next}.size = {full_len} := SpliceSupport.append_size {} {} {} {} {} {}\ntheorem {next}_route : Route {side}Code {} {next} := by\n have coverSize : {}.size = {} := {}\n apply GolfByteRouting.adjacent {side}Code {} {} {} {}\n simpa only [coverSize] using {}\n",
                    cover.code,
                    leaf.code,
                    cover.code,
                    leaf.code,
                    cover.len,
                    leaf.len,
                    cover.size,
                    leaf.size,
                    cover.base,
                    cover.code,
                    cover.len,
                    cover.size,
                    cover.code,
                    leaf.code,
                    cover.base,
                    cover.route,
                    leaf.route
                );
                self.emit(
                    &next,
                    &[
                        cover.module.clone(),
                        "Images".into(),
                        "CheckedRouteSupport".into(),
                    ],
                    &proof,
                    &[format!("{next}_size"), format!("{next}_route")],
                );
                cover = Part {
                    code: next.clone(),
                    size: format!("{next}_size"),
                    route: format!("{next}_route"),
                    complete: String::new(),
                    module: next,
                    base: cover.base,
                    len: full_len,
                    steps: 0,
                };
            }
            ensure!(
                cover.base <= base && base + len <= cover.base + cover.len,
                "incomplete scanner byte cover"
            );
            let local = base - cover.base;
            writeln!(body, "theorem {name}_local : ∀ i : Fin {len}, {}.data[{local}+i.val]? = {name}.data[i.val]? := by decide +kernel\ntheorem {name}_route : Route {side}Code {base} {name} := by\n have coverSize : {}.size = {} := {}\n constructor\n · rw [{name}_size, {side}Size]; decide\n · intro i hi\n   have inside : i < {len} := by simpa only [{name}_size] using hi\n   have h := {}.fetch ({local}+i) (by rw [coverSize]; omega)\n   calc\n    {side}Code.data[{base}+i]? = {}.data[{local}+i]? := by simpa only [←Nat.add_assoc] using h\n    _ = {name}.data[i]? := {name}_local ⟨i,inside⟩", cover.code, cover.code, cover.len, cover.size, cover.route, cover.code).unwrap();
            imports.push(cover.module);
            roots.push(format!("{name}_local"));
        }
        roots.push(format!("{name}_route"));
        self.emit(&name, &imports, &body, &roots);
        Ok(Part {
            code: name.clone(),
            size: format!("{name}_size"),
            route: format!("{name}_route"),
            complete: format!("{name}_complete"),
            module: name,
            base,
            len,
            steps,
        })
    }

    fn tree(&mut self, side: &str, mut parts: Vec<Part>) -> Part {
        if parts.len() == 1 {
            return parts.pop().unwrap();
        }
        let right = parts.split_off(parts.len() / 2);
        let a = self.tree(side, parts);
        let b = self.tree(side, right);
        let name = format!("JumpNode{}", self.nodes);
        self.nodes += 1;
        let len = a.len + b.len;
        let steps = a.steps + b.steps;
        let body = format!(
            "def {name} : ByteArray := ⟨{}.data ++ {}.data⟩\ntheorem {name}_size : {name}.size = {len} := SpliceSupport.append_size {} {} {} {} {} {}\ntheorem {name}_complete : CompleteScanPrefix ({name}.data.toList.map UInt8.toNat) {steps} := SpliceSupport.complete_bytes_append {} {} {} {} {} {}\ntheorem {name}_route : Route {side}Code {} {name} := by\n apply GolfByteRouting.adjacent {side}Code {} {} {} {}\n simpa only [{}] using {}\n",
            a.code,
            b.code,
            a.code,
            b.code,
            a.len,
            b.len,
            a.size,
            b.size,
            a.code,
            b.code,
            a.steps,
            b.steps,
            a.complete,
            b.complete,
            a.base,
            a.code,
            b.code,
            a.base,
            a.route,
            a.size,
            b.route
        );
        self.emit(
            &name,
            &[a.module, b.module],
            &body,
            &[
                format!("{name}_size"),
                format!("{name}_complete"),
                format!("{name}_route"),
            ],
        );
        Part {
            code: name.clone(),
            size: format!("{name}_size"),
            route: format!("{name}_route"),
            complete: format!("{name}_complete"),
            module: name,
            base: a.base,
            len,
            steps,
        }
    }

    fn side(
        &mut self,
        side: &str,
        bytes: &[u8],
        destination: usize,
        images: &RenderedImages,
    ) -> Result<()> {
        let leaves: Vec<_> = images
            .leaves
            .iter()
            .filter(|leaf| leaf.side == side && leaf.len != 0)
            .collect();
        let mut covered = 0;
        for leaf in &leaves {
            ensure!(
                leaf.base == covered,
                "full-image routes must be ordered and contiguous"
            );
            covered = covered
                .checked_add(leaf.len)
                .context("image route size overflow")?;
        }
        ensure!(
            covered == bytes.len(),
            "full-image routes do not cover input bytes"
        );
        let mut parts = Vec::new();
        for (start, end, steps) in prefix_chunks(bytes, destination)? {
            parts.push(self.chunk(side, &bytes[start..end], start, steps, &leaves)?);
        }
        let prefix = self.tree(side, parts);
        self.finish_side(side, destination, &prefix, &leaves, false)
    }

    fn finish_side(
        &mut self,
        side: &str,
        destination: usize,
        prefix: &Part,
        leaves: &[&ImageLeaf],
        transferred: bool,
    ) -> Result<()> {
        let leaf = leaves
            .iter()
            .find(|leaf| leaf.base <= destination && destination < leaf.base + leaf.len)
            .context("missing destination byte route")?;
        let offset = destination - leaf.base;
        let name = if side == "original" {
            "JumpOriginal"
        } else {
            "JumpCandidate"
        };
        let mut body = format!(
            "theorem {side}_byte : {side}Code.get? {}.size = some (UInt8.ofNat 91) := by\n have leafSize : {}.size = {} := {}\n rw [{}, GolfRouteMembership.byte_get]\n calc\n  {side}Code.data[{destination}]? = {}.data[{offset}]? := {}.fetch {offset} (by rw [leafSize]; decide)\n  _ = some (UInt8.ofNat 91) := by decide +kernel\n",
            prefix.code, leaf.code, leaf.len, leaf.size, prefix.size, leaf.code, leaf.route,
        );
        let mut imports = vec![
            prefix.module.clone(),
            "Images".into(),
            "CheckedRouteMembership".into(),
        ];
        if transferred {
            writeln!(body,"theorem candidate_membership : (D_J candidateCode (UInt256.ofNat 0)).contains (UInt256.ofNat {destination}) = true := by\n rw [←tables_equal]\n exact original_membership").unwrap();
            imports.push("JumpSplice".into());
            imports.push("JumpOriginal".into());
        } else {
            writeln!(body,"theorem {side}_membership : (D_J {side}Code (UInt256.ofNat 0)).contains (UInt256.ofNat {destination}) = true := by\n have h := GolfRouteMembership.contains_of_route {side}Code {} {} {} {} {side}_byte (by rw [{side}Size]; decide)\n simpa only [{}] using h",prefix.code,prefix.steps,prefix.route,prefix.complete,prefix.size).unwrap();
        }
        self.emit(
            name,
            &imports,
            &body,
            &[format!("{side}_byte"), format!("{side}_membership")],
        );
        Ok(())
    }
    fn exterior(&mut self, images: &RenderedImages) -> Result<()> {
        fn equal_nodes(
            body: &mut String,
            old: &super::ImageNode,
            new: &super::ImageNode,
        ) -> Result<String> {
            let proof = format!("{}_equal", old.code);
            ensure!(old.len == new.len, "unequal exterior node sizes");
            match (&old.children, &new.children) {
                (Some(a), Some(b)) => {
                    let left = equal_nodes(body, &a.0, &b.0)?;
                    let right = equal_nodes(body, &a.1, &b.1)?;
                    writeln!(body, "private theorem {proof} : {} = {} := append_equal {} {} {} {} {left} {right}", old.code, new.code, a.0.code, a.1.code, b.0.code, b.1.code).unwrap();
                }
                (None, None) => {
                    writeln!(body, "private theorem {proof}_bytes : {} = {} := rfl\nprivate theorem {proof} : {} = {} := congrArg GolfArtifactBytes.encode {proof}_bytes",old.bytes,new.bytes,old.code,new.code).unwrap();
                }
                _ => anyhow::bail!("incompatible exterior image trees"),
            }
            Ok(proof)
        }
        let mut body = String::from(
            "private theorem append_equal (a b c d : ByteArray) (left : a = c) (right : b = d) :\n (ByteArray.mk (a.data ++ b.data)) = ByteArray.mk (c.data ++ d.data) := by\n cases left\n cases right\n rfl\n",
        );
        for (part, root) in [("Prefix", "exterior_prefix"), ("Suffix", "exterior_suffix")] {
            let node = |side| {
                images
                    .parts
                    .iter()
                    .find(|(s, p, _)| *s == side && *p == part)
                    .map(|(_, _, n)| n)
                    .context("missing image exterior tree")
            };
            let proof = equal_nodes(&mut body, node("original")?, node("candidate")?)?;
            writeln!(
                body,
                "theorem {root} : original{part} = candidate{part} := {proof}"
            )
            .unwrap();
        }
        self.emit(
            "JumpExterior",
            &["Images".into(), "CheckedCompleteSegments".into()],
            &body,
            &["exterior_prefix".into(), "exterior_suffix".into()],
        );
        Ok(())
    }

    fn shared(
        &mut self,
        original: &[u8],
        candidate: &[u8],
        destination: usize,
        images: &RenderedImages,
        before_steps: usize,
        after_steps: usize,
    ) -> Result<()> {
        let entry = images.window_start;
        let exit = images.window_end;
        let leaves: Vec<_> = images
            .leaves
            .iter()
            .filter(|l| l.side == "original" && l.len != 0)
            .collect();
        let mut lead_parts = Vec::new();
        for (start, end, steps) in chunks_between(original, 0, entry)? {
            lead_parts.push(self.chunk(
                "original",
                &original[start..end],
                start,
                steps,
                &leaves,
            )?);
        }
        let lead = self.tree("original", lead_parts);
        let segment = self.chunk(
            "original",
            &original[entry..exit],
            entry,
            before_steps,
            &leaves,
        )?;
        let mut prefix_parts = vec![lead.clone(), segment];
        if exit < destination {
            let mut rest = Vec::new();
            for (start, end, steps) in chunks_between(original, exit, destination)? {
                rest.push(self.chunk("original", &original[start..end], start, steps, &leaves)?);
            }
            prefix_parts.push(self.tree("original", rest));
        }
        let prefix = self.tree("original", prefix_parts);
        self.finish_side("original", destination, &prefix, &leaves, false)?;
        self.exterior(images)?;

        let mut body = String::from(
            "private theorem parts_tables (old new lead before after suffix : ByteArray)\n (leadSteps beforeSteps afterSteps : Nat)\n (oldBytes : old.data.toList.map UInt8.toNat = lead.data.toList.map UInt8.toNat ++ before.data.toList.map UInt8.toNat ++ suffix.data.toList.map UInt8.toNat)\n (newBytes : new.data.toList.map UInt8.toNat = lead.data.toList.map UInt8.toNat ++ after.data.toList.map UInt8.toNat ++ suffix.data.toList.map UInt8.toNat)\n (leadComplete : CompleteScanPrefix (lead.data.toList.map UInt8.toNat) leadSteps)\n (beforeComplete : CompleteScanPrefix (before.data.toList.map UInt8.toNat) beforeSteps)\n (afterComplete : CompleteScanPrefix (after.data.toList.map UInt8.toNat) afterSteps)\n (sameLength : before.size = after.size)\n (beforeTargets : GolfWindowArtifact.jumpTargets (scanAux beforeSteps lead.size (before.data.toList.map UInt8.toNat)) = [])\n (afterTargets : GolfWindowArtifact.jumpTargets (scanAux afterSteps lead.size (after.data.toList.map UInt8.toNat)) = [])\n (oldBound : old.size + 32 < UInt256.size) (newBound : new.size + 32 < UInt256.size) :\n D_J old (UInt256.ofNat 0) = D_J new (UInt256.ofNat 0) := by\n apply RevisedTableEquality.tables_equal old new oldBound newBound\n rw [oldBytes,newBytes]\n apply GolfAlignedSplice.targets_splice_empty _ _ _ _ leadSteps beforeSteps afterSteps leadComplete beforeComplete afterComplete\n · simpa only [List.length_map,Array.length_toList,ByteArray.size] using sameLength\n · simpa only [List.length_map,Array.length_toList,ByteArray.size] using beforeTargets\n · simpa only [List.length_map,Array.length_toList,ByteArray.size] using afterTargets\n",
        );
        // Prove route extensionality abstractly, before applying it to the full roots.
        body.push_str("private theorem same_prefix (whole a b : ByteArray) (ra : Route whole 0 a) (rb : Route whole 0 b) (size : a.size = b.size) : a = b := by\n have h := GolfRouteMembership.route_take whole a ra\n have p := GolfRouteMembership.route_take whole b rb\n rw [size] at h\n exact congrArg ByteArray.mk (Array.ext' (h.symm.trans p))\n");
        writeln!(body,"private theorem lead_equal : {} = originalPrefix := same_prefix originalCode {} originalPrefix {} originalPrefixRoute (by rw [{},originalPrefixByteSize])\nprivate theorem lead_complete : CompleteScanPrefix (originalPrefix.data.toList.map UInt8.toNat) {} := by\n rw [←lead_equal]\n exact {}",lead.code,lead.code,lead.route,lead.size,lead.steps,lead.complete).unwrap();
        for (side, bytes, steps) in [
            ("original", &original[entry..exit], before_steps),
            ("candidate", &candidate[entry..exit], after_steps),
        ] {
            let literal = bytes
                .iter()
                .map(u8::to_string)
                .collect::<Vec<_>>()
                .join(",");
            writeln!(body,"private theorem {side}_complete : CompleteScanPrefix ({side}Window.data.toList.map UInt8.toNat) {steps} := by\n change CompleteScanPrefix [{literal}] {steps}").unwrap();
            let mut pc = 0;
            let mut remaining = steps;
            while pc < bytes.len() {
                let op = bytes[pc];
                let width = push_width(op);
                remaining -= 1;
                writeln!(
                    body,
                    " refine CompleteScanPrefix.cons {op} {:?} _ {remaining} rfl ?_",
                    &bytes[pc + 1..pc + 1 + width]
                )
                .unwrap();
                pc += 1 + width;
            }
            body.push_str(" exact CompleteScanPrefix.nil\n");
            writeln!(body,"private theorem {side}_targets : GolfWindowArtifact.jumpTargets (scanAux {steps} originalPrefix.size ({side}Window.data.toList.map UInt8.toNat)) = [] := by\n rw [originalPrefixByteSize]\n change GolfWindowArtifact.jumpTargets (scanAux {steps} {entry} [{literal}]) = []\n decide +kernel").unwrap();
        }
        writeln!(body,"theorem tables_equal : D_J originalCode (UInt256.ofNat 0) = D_J candidateCode (UInt256.ofNat 0) := by\n apply parts_tables originalCode candidateCode originalPrefix originalWindow candidateWindow originalSuffix {} {before_steps} {after_steps}\n · simp only [originalCode,Array.toList_append,List.map_append]\n · simp only [candidateCode,Array.toList_append,List.map_append,←exterior_prefix,←exterior_suffix]\n · exact lead_complete\n · exact original_complete\n · exact candidate_complete\n · rw [originalWindowByteSize,candidateWindowByteSize]\n · exact original_targets\n · exact candidate_targets\n · rw [originalSize]; decide\n · rw [candidateSize]; decide",lead.steps).unwrap();
        self.emit(
            "JumpSplice",
            &[
                "JumpExterior".into(),
                lead.module,
                "CheckedRouteMembership".into(),
                "CheckedRouteSupport".into(),
            ],
            &body,
            &["tables_equal".into()],
        );
        let target_leaves: Vec<_> = images
            .leaves
            .iter()
            .filter(|l| l.side == "candidate" && l.len != 0)
            .collect();
        self.finish_side("candidate", destination, &prefix, &target_leaves, true)
    }
}

fn push_width(op: u8) -> usize {
    if (0x60..=0x7f).contains(&op) {
        usize::from(op - 0x5f)
    } else {
        0
    }
}

fn prefix_chunks(bytes: &[u8], destination: usize) -> Result<Vec<(usize, usize, usize)>> {
    ensure!(
        bytes.len() <= MAX_RUNTIME_BYTES,
        "runtime exceeds EIP-170 size limit"
    );
    ensure!(
        bytes.get(destination) == Some(&0x5b),
        "jump destination must contain JUMPDEST in both images"
    );
    chunks_between(bytes, 0, destination)
}

fn chunks_between(bytes: &[u8], begin: usize, end: usize) -> Result<Vec<(usize, usize, usize)>> {
    ensure!(
        begin <= end && end <= bytes.len(),
        "invalid scanner prefix range"
    );
    let mut result = Vec::new();
    let (mut pc, mut start, mut steps) = (begin, begin, 0);
    while pc < end {
        let next = pc + 1 + push_width(bytes[pc]);
        ensure!(next <= end, "jump destination is inside PUSH data");
        if steps != 0 && (steps == CHUNK_INSTRUCTIONS || next - start > CHUNK_BYTES) {
            result.push((start, pc, steps));
            start = pc;
            steps = 0;
        }
        pc = next;
        steps += 1;
    }
    if steps != 0 || result.is_empty() {
        result.push((start, pc, steps));
    }
    Ok(result)
}

/// Return trusted generated sources; the caller still must compile and audit every root.
pub(super) fn membership_sources(
    original: &[u8],
    candidate: &[u8],
    destination: usize,
    images: &RenderedImages,
) -> Result<Vec<Module>> {
    // Reject malformed input before creating any generated module plan.
    prefix_chunks(original, destination)?;
    prefix_chunks(candidate, destination)?;
    let mut generator = Generator::default();
    // Sharing is a bounded splice representation, never a timeout fallback.
    let entry = images.window_start;
    let exit = images.window_end;
    let local = |bytes: &[u8]| -> Option<usize> {
        if entry >= exit || exit > bytes.len() || exit - entry > CHUNK_BYTES {
            return None;
        }
        let chunks = chunks_between(bytes, entry, exit).ok()?;
        if chunks.len() != 1 {
            return None;
        }
        let mut pc = entry;
        while pc < exit {
            if bytes[pc] == 0x5b {
                return None;
            }
            pc += 1 + push_width(bytes[pc]);
        }
        Some(chunks[0].2)
    };
    let sharing = if original.len() == candidate.len()
        && entry <= exit
        && exit <= original.len()
        && exit <= destination
        && original[..entry] == candidate[..entry]
        && original[exit..] == candidate[exit..]
        && chunks_between(original, 0, entry).is_ok()
    {
        local(original).zip(local(candidate))
    } else {
        None
    };
    if let Some((before, after)) = sharing {
        generator.shared(original, candidate, destination, images, before, after)?;
    } else {
        generator.side("original", original, destination, images)?;
        generator.side("candidate", candidate, destination, images)?;
    }
    generator.emit(
        "JumpMembership",
        &["JumpOriginal".into(), "JumpCandidate".into()],
        "",
        &["original_membership".into(), "candidate_membership".into()],
    );
    Ok(generator.modules)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runtime::region::{ImageRoutes, render_images};

    #[test]
    fn shared_splice_reuses_source_prefix_and_keeps_actual_candidate_binding() {
        for prefix_len in [0, 300] {
            let mut original = vec![0x5f; prefix_len];
            original.extend([0x60, 0x02, 0x02, 0x56, 0x5b, 0x00]);
            let mut candidate = original.clone();
            candidate[prefix_len + 1] = 1;
            candidate[prefix_len + 2] = 0x1b;
            let destination = prefix_len + 4;
            let images = render_images(&original, &candidate, prefix_len, 3, ImageRoutes::All);
            let modules = membership_sources(&original, &candidate, destination, &images).unwrap();
            let names = modules
                .iter()
                .map(|(name, _, _)| name.as_str())
                .collect::<Vec<_>>();
            let original_pos = names
                .iter()
                .position(|name| *name == "JumpOriginal")
                .unwrap();
            assert_eq!(
                &names[original_pos..],
                [
                    "JumpOriginal",
                    "JumpExterior",
                    "JumpSplice",
                    "JumpCandidate",
                    "JumpMembership"
                ]
            );
            // No candidate prefix is silently assumed: its membership is derived from
            // full table equality, while its destination fetch remains independent.
            let candidate_proof = &modules
                .iter()
                .find(|(n, _, _)| n == "JumpCandidate")
                .unwrap()
                .1;
            assert!(candidate_proof.contains("D_J candidateCode"));
            assert!(candidate_proof.contains("candidateCode.data["));
            assert!(candidate_proof.contains("rw [←tables_equal]"));
            assert!(
                modules
                    .iter()
                    .filter(|(n, _, _)| n.starts_with("JumpChunk") || n.starts_with("JumpNode"))
                    .all(|(_, source, _)| !source.contains("Route candidateCode"))
            );
            let splice = &modules
                .iter()
                .find(|(n, _, _)| n == "JumpSplice")
                .unwrap()
                .1;
            assert!(splice.contains("originalPrefixRoute"));
            assert!(splice.contains("original_complete"));
            assert!(splice.contains("candidate_complete"));
        }
    }

    #[test]
    fn independent_generation_preserves_earlier_and_unshareable_cases() {
        let backward = vec![0x5b, 0x60, 0x02, 0x02, 0x56, 0x00];
        let mut large = vec![0x5f; 129];
        large.extend([0x56, 0x5b]);
        let mut many = vec![0x5f; 64];
        many.extend([0x56, 0x5b]);
        for (original, candidate, entry, len, destination) in [
            (backward.clone(), backward, 1, 3, 0),
            (large.clone(), large, 0, 129, 130),
            (many.clone(), many, 0, 64, 65),
            (
                vec![0x5f, 0x56, 0x5b, 0x00],
                vec![0x5f, 0x56, 0x5b, 0x5f],
                0,
                1,
                2,
            ),
            (vec![0x5b, 0x56, 0x5b], vec![0x5b, 0x56, 0x5b], 0, 1, 2),
            (
                vec![0x60, 0x02, 0x56, 0x5b],
                vec![0x60, 0x02, 0x56, 0x5b],
                1,
                1,
                3,
            ),
        ] {
            let images = render_images(&original, &candidate, entry, len, ImageRoutes::All);
            let modules = membership_sources(&original, &candidate, destination, &images).unwrap();
            assert!(!modules.iter().any(|(n, _, _)| n == "JumpSplice"));
            assert!(modules.iter().any(|(n, _, _)| n == "JumpOriginal"));
            assert!(modules.iter().any(|(n, _, _)| n == "JumpCandidate"));
        }
    }

    #[test]
    fn scanner_prefix_rejects_payload_and_accepts_complete_trailing_boundary() {
        assert!(prefix_chunks(&[0x60, 0x5b, 0x5b], 1).is_err());
        assert_eq!(
            prefix_chunks(&[0x60, 0x5b, 0x5b], 2).unwrap(),
            vec![(0, 2, 1)]
        );
        assert_eq!(prefix_chunks(&[0x5b, 0x7f], 0).unwrap(), vec![(0, 0, 0)]);
        assert!(prefix_chunks(&[0x7f, 0x5b], 1).is_err());
    }

    #[test]
    fn membership_binds_full_roots_with_cross_leaf_prefix_and_empty_prefix() {
        for destination in [0, 300] {
            let mut original = vec![0x5f; 305];
            original[destination] = 0x5b;
            let mut candidate = original.clone();
            candidate[304] = 0x00;
            let images = render_images(&original, &candidate, 250, 12, ImageRoutes::All);
            let modules = membership_sources(&original, &candidate, destination, &images).unwrap();
            let output = modules
                .iter()
                .map(|(_, s, _)| s.as_str())
                .collect::<String>();
            assert!(output.contains("D_J originalCode"));
            assert!(output.contains("D_J candidateCode"));
            assert!(modules.last().unwrap().0 == "JumpMembership");
            if destination != 0 {
                assert!(modules.iter().any(|(n, _, _)| n.starts_with("JumpCover")));
            }
        }
    }
}
