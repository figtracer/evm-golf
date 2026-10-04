//! Exact full-image jump membership from bounded, instruction-aligned prefixes.

use anyhow::{Context as _, Result, ensure};
use std::fmt::Write as _;

use super::{ImageLeaf, MAX_RUNTIME_BYTES, RenderedImages};

const CHUNK_BYTES: usize = 128;
const CHUNK_INSTRUCTIONS: usize = 32;
const NAMESPACE: &str = "GolfCertificates.JumpMembership";
type Module = (String, String, Vec<String>);

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
        let body = format!(
            "theorem {side}_byte : {side}Code.get? {}.size = some (UInt8.ofNat 91) := by\n have leafSize : {}.size = {} := {}\n rw [{}, GolfRouteMembership.byte_get]\n calc\n  {side}Code.data[{destination}]? = {}.data[{offset}]? := {}.fetch {offset} (by rw [leafSize]; decide)\n  _ = some (UInt8.ofNat 91) := by decide +kernel\ntheorem {side}_membership : (D_J {side}Code (UInt256.ofNat 0)).contains (UInt256.ofNat {destination}) = true := by\n have h := GolfRouteMembership.contains_of_route {side}Code {} {} {} {} {side}_byte (by rw [{side}Size]; decide)\n simpa only [{}] using h\n",
            prefix.code,
            leaf.code,
            leaf.len,
            leaf.size,
            prefix.size,
            leaf.code,
            leaf.route,
            prefix.code,
            prefix.steps,
            prefix.route,
            prefix.complete,
            prefix.size
        );
        self.emit(
            name,
            &[
                prefix.module,
                "Images".into(),
                "CheckedRouteMembership".into(),
            ],
            &body,
            &[format!("{side}_byte"), format!("{side}_membership")],
        );
        Ok(())
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
    let mut result = Vec::new();
    let (mut pc, mut start, mut steps) = (0, 0, 0);
    while pc < destination {
        let next = pc + 1 + push_width(bytes[pc]);
        ensure!(next <= destination, "jump destination is inside PUSH data");
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
    generator.side("original", original, destination, images)?;
    generator.side("candidate", candidate, destination, images)?;
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
