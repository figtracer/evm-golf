//! Equal-length rewrites that preserve all possible legacy jump destinations.

use anyhow::{Context as _, Result, ensure};
use revm::{
    bytecode::opcode::OpCode,
    interpreter::STACK_LIMIT,
    primitives::{U256, hex},
};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

use super::{Instruction, MAX_RUNTIME_BYTES, Rewrite, allowed, decode, push_value, replacement};

/// Conservative instruction reachability without stack-height or label proofs.
#[derive(Debug, Serialize)]
pub struct LayoutAnalysis {
    pub runtime_bytes: usize,
    pub reachable_instructions: usize,
    pub jump_destinations: usize,
    #[serde(skip)]
    instructions: Vec<Instruction>,
    #[serde(skip)]
    reachable: BTreeSet<usize>,
    #[serde(skip)]
    pub(super) copies: Vec<CodeCopy>,
}

/// Literal own-code read. Offsets are bounded before conversion to slices.
#[derive(Debug)]
pub(super) struct CodeCopy {
    pub(super) pc: usize,
    pub(super) prefix_start: usize,
    pub(super) source: usize,
    pub(super) len: usize,
    pub(super) destination: U256,
}

// Include valid unreachable sites conservatively. Reachability analysis below
// rejects every reachable CODECOPY that is absent from this list.
pub(super) fn code_copies(code: &[u8]) -> Vec<CodeCopy> {
    decode(code)
        .windows(4)
        .filter_map(|ops| {
            if ops[3].bytes[0] != 0x39 {
                return None;
            }
            let len = usize::try_from(push_value(&ops[0].bytes)?).ok()?;
            let source = usize::try_from(push_value(&ops[1].bytes)?).ok()?;
            let destination = push_value(&ops[2].bytes)?;
            if source > code.len() || len > code.len() - source {
                return None;
            }
            Some(CodeCopy {
                pc: ops[3].pc,
                prefix_start: ops[0].pc,
                source,
                len,
                destination,
            })
        })
        .collect()
}

pub(super) fn analyze(code: &[u8], guard_calls: bool) -> Result<LayoutAnalysis> {
    ensure!(
        code.len() <= MAX_RUNTIME_BYTES,
        "runtime exceeds EIP-170 size limit"
    );
    ensure!(
        !code.starts_with(&[0xef, 0x00]),
        "EOF bytecode is unsupported"
    );
    let instructions = decode(code);
    let copies = if guard_calls {
        code_copies(code)
    } else {
        Vec::new()
    };
    let index: BTreeMap<_, _> = instructions
        .iter()
        .enumerate()
        .map(|(i, op)| (op.pc, i))
        .collect();
    let destinations: Vec<_> = instructions
        .iter()
        .filter(|op| op.bytes[0] == 0x5b)
        .map(|op| op.pc)
        .collect();
    let mut reachable = BTreeSet::new();
    let mut queue = VecDeque::from([0]);
    let mut opened_jump_targets = false;
    while let Some(pc) = queue.pop_front() {
        if pc == code.len() || !reachable.insert(pc) {
            continue;
        }
        let i = *index.get(&pc).context("control flow enters PUSH data")?;
        let instruction = &instructions[i];
        let op = instruction.bytes[0];
        if OpCode::info_by_op(op).is_none() {
            // Unknown bytes halt unconditionally in revm. Keep their exact
            // value, stop fallthrough, and still visit independently queued
            // JUMPDESTs after them. This never strips or interprets metadata.
            continue;
        }
        // PC and CODESIZE are stable because no instruction or byte is moved.
        // Explicit fixtures additionally guard ordinary calls during replay.
        // Otherwise GAS is limited to the literal-1 ECRECOVER pattern.
        let supported = match op {
            0x5a if guard_calls => instructions
                .get(i + 1)
                .is_some_and(|next| matches!(next.bytes[0], 0xf1 | 0xfa)),
            0x3b | 0xf1 | 0xfa if guard_calls => true,
            0x39 if guard_calls => copies.iter().any(|copy| copy.pc == pc),
            0x5a | 0xfa => is_direct_ecrecover(&instructions, i),
            _ => allowed(op) || matches!(op, 0x38 | 0x58),
        };
        ensure!(
            supported,
            "unsupported or code/gas-sensitive opcode {} (0x{op:02x}) at PC {pc}",
            OpCode::name_by_op(op)
        );
        if (0x60..=0x7f).contains(&op) {
            ensure!(
                instruction.bytes.len() == usize::from(op - 0x5f) + 1,
                "truncated PUSH at PC {pc}"
            );
        }
        if matches!(op, 0x56 | 0x57) && !opened_jump_targets {
            // Arbitrary computed destinations can reach every real JUMPDEST.
            // Invalid destinations halt; no other PC can become an entry point.
            queue.extend(destinations.iter().copied());
            opened_jump_targets = true;
        }
        if !matches!(op, 0x00 | 0x56 | 0xf3 | 0xfd | 0xfe) {
            queue.push_back(pc + instruction.bytes.len());
        }
    }
    Ok(LayoutAnalysis {
        runtime_bytes: code.len(),
        reachable_instructions: reachable.len(),
        jump_destinations: destinations.len(),
        instructions,
        copies: copies
            .into_iter()
            .filter(|copy| reachable.contains(&copy.pc))
            .collect(),
        reachable,
    })
}

// The decoded sequence contains no JUMPDEST, so any execution reaching its
// GAS or STATICCALL must first execute the literal callee PUSH. GAS is consumed
// immediately as the call's gas argument and cannot escape into contract data.
// This establishes the callee and gas-use restriction, not all-gas equivalence:
// an ECRECOVER call can still change outcome across its 3,000-gas threshold.
fn is_direct_ecrecover(instructions: &[Instruction], i: usize) -> bool {
    let start = match instructions[i].bytes[0] {
        0x5a => i.checked_sub(1),
        0xfa => i.checked_sub(2),
        _ => None,
    };
    start
        .and_then(|start| instructions.get(start..start + 3))
        .is_some_and(|ops| {
            push_value(&ops[0].bytes) == Some(U256::from(1))
                && ops[1].bytes[0] == 0x5a
                && ops[2].bytes[0] == 0xfa
        })
}

pub(super) fn transform(analysis: &LayoutAnalysis) -> Result<(Vec<u8>, Vec<Rewrite>)> {
    let mut instructions = analysis.instructions.clone();
    let mut rewrites = Vec::new();
    for i in 0..instructions.len().saturating_sub(1) {
        let a = &instructions[i];
        let b = &instructions[i + 1];
        // Catalog entries must refer to disjoint bytes in the original image.
        // Never feed a generated opcode back into this pass's next rewrite.
        if rewrites
            .last()
            .is_some_and(|rewrite: &Rewrite| a.pc < rewrite.original_pc + rewrite.before.len() / 2)
        {
            continue;
        }
        if push_value(&a.bytes).is_some_and(|value| value.is_zero())
            && b.bytes == [0x80]
            && analysis.reachable.contains(&a.pc)
            && !analysis
                .copies
                .iter()
                .any(|copy| copy.len != 0 && a.pc < copy.source + copy.len && copy.source < b.pc)
        {
            // Every following PUSH0 or DUP1 preserves the known zero at the top.
            // At most 1024 produced words can succeed on an initially empty stack.
            let end = instructions[i + 1..]
                .iter()
                .take(STACK_LIMIT - 1)
                .take_while(|op| {
                    matches!(op.bytes.as_slice(), [0x5f] | [0x80])
                        && analysis.reachable.contains(&op.pc)
                        && !analysis.copies.iter().any(|copy| {
                            copy.len != 0
                                && op.pc < copy.source + copy.len
                                && copy.source < op.pc + op.bytes.len()
                        })
                })
                .enumerate()
                .filter_map(|(offset, op)| (op.bytes == [0x80]).then_some(i + offset + 2))
                .last()
                .unwrap_or(i + 1);
            if end > i + 1 {
                let source_pc = a.pc;
                let before: Vec<_> = instructions[i..end]
                    .iter()
                    .flat_map(|op| op.bytes.iter().copied())
                    .collect();
                let after: Vec<_> = a
                    .bytes
                    .iter()
                    .copied()
                    .chain(std::iter::repeat_n(0x5f, end - i - 1))
                    .collect();
                for op in &mut instructions[i + 1..end] {
                    op.bytes[0] = 0x5f;
                }
                rewrites.push(Rewrite {
                    original_pc: source_pc,
                    before: hex::encode(before),
                    after: hex::encode(after),
                    required_stack: 0,
                });
                continue;
            }
        }
        // Fold two constants without removing either PUSH: the transient peak
        // must remain two words even when the result could use a single PUSH.
        if let Some(c) = instructions.get(i + 2)
            && [a.pc, b.pc, c.pc]
                .iter()
                .all(|pc| analysis.reachable.contains(pc))
            && matches!(c.bytes[0], 0x16 | 0x1b)
            && !analysis.copies.iter().any(|copy| {
                copy.len != 0 && a.pc < copy.source + copy.len && copy.source < c.pc + c.bytes.len()
            })
            && let Some((3, folded, 0)) = replacement(&[a, b, c])
            && folded.len() <= a.bytes.len()
        {
            let before: Vec<_> = [a, b, c]
                .iter()
                .flat_map(|op| op.bytes.iter().copied())
                .collect();
            let mut first = a.bytes.clone();
            first[1..].fill(0);
            let start = first.len() - (folded.len() - 1);
            first[start..].copy_from_slice(&folded[1..]);
            let mut second = b.bytes.clone();
            second[1..].fill(0);
            let after: Vec<_> = first.iter().chain(&second).copied().chain([0x50]).collect();
            ensure!(
                stack_signature(&before)? == (0, 1, 2) && stack_signature(&after)? == (0, 1, 2),
                "literal fold changes stack requirements or peak growth"
            );
            let source_pc = a.pc;
            instructions[i].bytes = first;
            instructions[i + 1].bytes = second;
            instructions[i + 2].bytes[0] = 0x50;
            rewrites.push(Rewrite {
                original_pc: source_pc,
                before: hex::encode(before),
                after: hex::encode(after),
                required_stack: 0,
            });
            continue;
        }
        if !analysis.reachable.contains(&a.pc)
            || !analysis.reachable.contains(&b.pc)
            || b.bytes[0] != 0x02
        {
            continue;
        }
        // Preserve every byte that an admitted own-code read can observe.
        if analysis.copies.iter().any(|copy| {
            copy.len != 0 && a.pc < copy.source + copy.len && copy.source < b.pc + b.bytes.len()
        }) {
            continue;
        }
        let Some(value) = push_value(&a.bytes) else {
            continue;
        };
        let (constant, operation) = if value.is_zero() {
            (0, 0x16) // x * 0 = x & 0.
        } else if value == U256::from(1) {
            (0, 0x01) // x * 1 = x + 0.
        } else if value.count_ones() == 1 {
            // A nonzero U256 power has exponent 0..255, fitting every PUSH width.
            (value.trailing_zeros() as u8, 0x1b) // Includes wrapping overflow.
        } else {
            continue;
        };
        let before: Vec<_> = a.bytes.iter().chain(&b.bytes).copied().collect();
        let mut after = a.bytes.clone();
        // Retain the PUSH width, including PUSH0, to preserve every boundary.
        after[1..].fill(0);
        if let Some(last) = after.get_mut(1..).and_then(|bytes| bytes.last_mut()) {
            *last = constant;
        }
        after.push(operation);
        ensure!(
            stack_signature(&before)? == stack_signature(&after)?,
            "layout rewrite changes stack requirements or peak growth"
        );
        let source_pc = a.pc;
        instructions[i].bytes = after[..after.len() - 1].to_vec();
        instructions[i + 1].bytes[0] = operation;
        rewrites.push(Rewrite {
            original_pc: source_pc,
            before: hex::encode(before),
            after: hex::encode(after),
            required_stack: 1,
        });
    }
    let candidate: Vec<_> = instructions
        .iter()
        .flat_map(|op| op.bytes.iter().copied())
        .collect();
    validate_layout(analysis, &candidate)?;
    Ok((candidate, rewrites))
}

/// Trusted opportunities, named by original PC, for this exact analysis.
/// Reject any cascading or overlapping rewrite rather than treating it as an
/// independently selectable edit to the immutable input.
pub(super) fn opportunities(analysis: &LayoutAnalysis) -> Result<Vec<Rewrite>> {
    let (candidate, rewrites) = transform(analysis)?;
    let original: Vec<_> = analysis
        .instructions
        .iter()
        .flat_map(|op| op.bytes.iter().copied())
        .collect();
    validate_catalog(&original, &candidate, &rewrites)?;
    Ok(rewrites)
}

/// Select trusted replacements only; callers never supply replacement bytes.
/// Empty selection is the unchanged baseline. Selection order is immaterial.
pub(super) fn transform_selected(
    analysis: &LayoutAnalysis,
    selected_pcs: &[usize],
) -> Result<(Vec<u8>, Vec<Rewrite>)> {
    let catalog = opportunities(analysis)?;
    let mut selected = BTreeSet::new();
    for pc in selected_pcs {
        ensure!(selected.insert(*pc), "duplicate rewrite PC {pc}");
    }
    let mut candidate: Vec<_> = analysis
        .instructions
        .iter()
        .flat_map(|op| op.bytes.iter().copied())
        .collect();
    let mut rewrites = Vec::new();
    for rewrite in catalog {
        if selected.remove(&rewrite.original_pc) {
            let after = hex::decode(&rewrite.after)?;
            candidate[rewrite.original_pc..rewrite.original_pc + after.len()]
                .copy_from_slice(&after);
            rewrites.push(rewrite);
        }
    }
    ensure!(selected.is_empty(), "unknown rewrite PCs: {selected:?}");
    validate_layout(analysis, &candidate)?;
    Ok((candidate, rewrites))
}

fn validate_catalog(original: &[u8], candidate: &[u8], rewrites: &[Rewrite]) -> Result<()> {
    let mut reconstructed = original.to_vec();
    let mut previous_end = 0;
    for rewrite in rewrites {
        let before = hex::decode(&rewrite.before)?;
        let after = hex::decode(&rewrite.after)?;
        ensure!(
            !before.is_empty() && before.len() == after.len(),
            "catalog rewrite changes byte length"
        );
        let start = rewrite.original_pc;
        let end = start
            .checked_add(before.len())
            .context("rewrite PC overflow")?;
        ensure!(
            start >= previous_end,
            "overlapping or unordered catalog rewrites"
        );
        ensure!(
            original.get(start..end) == Some(before.as_slice()),
            "catalog rewrite does not match baseline at PC {start}"
        );
        let signature = stack_signature(&before)?;
        ensure!(
            signature == stack_signature(&after)?
                && usize::try_from(signature.0)? == rewrite.required_stack,
            "catalog rewrite changes stack requirements or peak growth"
        );
        reconstructed[start..end].copy_from_slice(&after);
        previous_end = end;
    }
    ensure!(
        reconstructed == candidate,
        "catalog does not reconstruct full candidate"
    );
    Ok(())
}

fn validate_layout(analysis: &LayoutAnalysis, candidate: &[u8]) -> Result<()> {
    let decoded = decode(candidate);
    ensure!(
        candidate.len() == analysis.runtime_bytes && decoded.len() == analysis.instructions.len(),
        "layout rewrite changes bytecode length or instruction count"
    );
    ensure!(
        decoded
            .iter()
            .zip(&analysis.instructions)
            .all(|(new, old)| new.pc == old.pc
                && new.bytes.len() == old.bytes.len()
                && (new.bytes[0] == 0x5b) == (old.bytes[0] == 0x5b)),
        "layout rewrite changes instruction boundaries or jump destinations"
    );
    Ok(())
}

// (required input height, final height delta, maximum height growth). These
// signatures include transient peaks: stack overflow must not be optimized away.
fn stack_signature(code: &[u8]) -> Result<(isize, isize, isize)> {
    let mut required = 0;
    let mut height = 0;
    let mut peak = 0;
    for instruction in decode(code) {
        let info = OpCode::info_by_op(instruction.bytes[0]).context("unknown rewrite opcode")?;
        required = required.max(info.inputs() as isize - height);
        height += info.outputs() as isize - info.inputs() as isize;
        peak = peak.max(height);
    }
    Ok((required, height, peak))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runtime::{Case, compare, execute, from_hex};

    fn bytes(input: &str) -> Vec<u8> {
        from_hex(input).unwrap()
    }
    fn case(input: &str) -> Case {
        Case {
            calldata: input.into(),
            gas_limit: 200_000,
            value: String::new(),
            storage: BTreeMap::new(),
        }
    }

    #[test]
    fn zero_chains_preserve_overflow_and_protected_suffixes() {
        for height in [0, 1021, 1022, 1024] {
            let mut original = vec![0x5f; height];
            original.extend(bytes("6000808000"));
            let (candidate, rewrites) = transform(&analyze(&original, false).unwrap()).unwrap();
            assert_eq!(rewrites.len(), 1);
            assert_eq!(rewrites[0].before, "60008080");
            assert_eq!(rewrites[0].after, "60005f5f");
            let left = execute(&original, &case("")).unwrap().result;
            let right = execute(&candidate, &case("")).unwrap().result;
            assert_eq!(left.is_halt(), height >= 1022);
            assert_eq!(left.is_halt(), right.is_halt());
            if left.is_halt() {
                assert_eq!(left, right);
            }
        }
        for (original, expected) in [
            // A copied later DUP is preserved while the preceding safe pair improves.
            ("6000808050600160035f3900", "60005f8050600160035f3900"),
            // An entry point ends the fragment; the next DUP has an unknown input.
            ("6000805b8000", "60005f5b8000"),
        ] {
            let original = bytes(original);
            let (candidate, rewrites) = transform(&analyze(&original, true).unwrap()).unwrap();
            assert_eq!(candidate, bytes(expected));
            assert_eq!(rewrites.len(), 1);
            validate_catalog(&original, &candidate, &rewrites).unwrap();
        }
        // The admitted fragment itself must have a successful empty-stack input.
        // Leave the following overflowing DUP outside the maximum useful chain.
        let mut original = vec![0x5f];
        original.extend(std::iter::repeat_n(0x80, 1024));
        original.push(0);
        let (candidate, rewrites) = transform(&analyze(&original, false).unwrap()).unwrap();
        assert_eq!(rewrites.len(), 1);
        assert_eq!(bytes(&rewrites[0].before).len(), 1024);
        assert_eq!(candidate[1024], 0x80);
        assert_eq!(
            execute(&original, &case("")).unwrap().result,
            execute(&candidate, &case("")).unwrap().result
        );
    }

    #[test]
    fn zero_dup_preserves_stack_limits_and_immutable_catalogs() {
        let original = bytes("6000805f5260205260405ff3");
        let (candidate, rewrites) = transform(&analyze(&original, false).unwrap()).unwrap();
        assert_eq!(rewrites.len(), 1);
        assert_eq!(rewrites[0].before, "600080");
        assert_eq!(rewrites[0].after, "60005f");
        assert_eq!(rewrites[0].required_stack, 0);
        let result = compare(&original, &candidate, &case("")).unwrap();
        assert_eq!(result.baseline_gas - result.candidate_gas, 1);
        for code in ["600080", "60005f"] {
            assert_eq!(stack_signature(&bytes(code)).unwrap(), (0, 2, 2));
        }
        for width in 0u8..=32 {
            let mut pair = vec![0x5f + width];
            pair.extend(std::iter::repeat_n(0, usize::from(width)));
            pair.push(0x80);
            let mut replacement = pair.clone();
            *replacement.last_mut().unwrap() = 0x5f;
            let mut original = pair.clone();
            original.extend(bytes("5f5260205260405ff3"));
            let (candidate, rewrites) = transform(&analyze(&original, false).unwrap()).unwrap();
            assert_eq!(rewrites.len(), 1);
            assert_eq!(rewrites[0].before, hex::encode(&pair));
            assert_eq!(rewrites[0].after, hex::encode(&replacement));
            assert_eq!(stack_signature(&pair).unwrap(), (0, 2, 2));
            assert_eq!(stack_signature(&replacement).unwrap(), (0, 2, 2));
            let result = compare(&original, &candidate, &case("")).unwrap();
            assert_eq!(result.baseline_gas - result.candidate_gas, 1);
            for height in [0, 1022, 1023, 1024] {
                let mut before = vec![0x5f; height];
                before.extend(&pair);
                before.push(0);
                let mut after = vec![0x5f; height];
                after.extend(&replacement);
                after.push(0);
                let left = execute(&before, &case("")).unwrap().result;
                let right = execute(&after, &case("")).unwrap().result;
                assert_eq!(left.is_halt(), height >= 1023);
                assert_eq!(left.is_halt(), right.is_halt());
                if left.is_halt() {
                    assert_eq!(left, right);
                }
            }
            if width > 0 {
                let mut nonzero = pair;
                nonzero[usize::from(width)] = 1;
                nonzero.push(0);
                let (candidate, rewrites) = transform(&analyze(&nonzero, false).unwrap()).unwrap();
                assert_eq!(candidate, nonzero);
                assert!(rewrites.is_empty());
            }
        }
        assert!(analyze(&bytes("7f000080"), false).is_err());
        // Generated PUSH0 must not start a second overlapping rule in this pass.
        for (before, after) in [
            ("60008060011600", "60005f60011600"),
            ("6000800200", "60005f0200"),
            ("6000808000", "60005f5f00"),
            ("5f808000", "5f5f5f00"),
            ("6000805f8000", "60005f5f5f00"),
            ("5f8060011600", "5f5f60011600"),
            ("5f800200", "5f5f0200"),
        ] {
            let original = bytes(before);
            let analysis = analyze(&original, false).unwrap();
            let catalog = opportunities(&analysis).unwrap();
            assert_eq!(catalog.len(), 1);
            let (candidate, rewrites) = transform_selected(&analysis, &[0]).unwrap();
            assert_eq!(candidate, bytes(after));
            validate_catalog(&original, &candidate, &rewrites).unwrap();
        }
        for protected in [
            "60018000",
            "60008100",
            "6260008000",
            "00600080",
            "60008050600160015f3900",
            "60008050600160025f3900",
        ] {
            let original = bytes(protected);
            let (candidate, rewrites) = transform(&analyze(&original, true).unwrap()).unwrap();
            assert_eq!(candidate, original);
            assert!(rewrites.is_empty());
        }
        let original = bytes("60008050600260020250600760031600");
        let analysis = analyze(&original, false).unwrap();
        let catalog = opportunities(&analysis).unwrap();
        assert_eq!(
            catalog.iter().map(|r| r.original_pc).collect::<Vec<_>>(),
            [0, 6, 10]
        );
        for mask in 0..8 {
            let selected: Vec<_> = catalog
                .iter()
                .enumerate()
                .filter_map(|(i, r)| (mask & (1 << i) != 0).then_some(r.original_pc))
                .collect();
            let (candidate, rewrites) = transform_selected(&analysis, &selected).unwrap();
            validate_catalog(&original, &candidate, &rewrites).unwrap();
            compare(&original, &candidate, &case("")).unwrap();
        }
    }

    #[test]
    fn selected_rewrites_preserve_baseline_and_all_on_behavior() {
        // A power multiply and a literal fold, separated by an unchanged MUL.
        let original = bytes("600760020260030260ff601f16015f5260205ff3");
        let analysis = analyze(&original, false).unwrap();
        let catalog = opportunities(&analysis).unwrap();
        let pcs: Vec<_> = catalog.iter().map(|r| r.original_pc).collect();
        assert_eq!(pcs, [2, 8]);
        let (all, all_rewrites) = transform(&analysis).unwrap();
        for mask in 0..4 {
            let selected: Vec<_> = pcs
                .iter()
                .enumerate()
                .filter_map(|(i, pc)| (mask & (1 << i) != 0).then_some(*pc))
                .collect();
            let (candidate, rewrites) = transform_selected(&analysis, &selected).unwrap();
            assert_eq!(rewrites.len(), selected.len());
            compare(&original, &candidate, &case("")).unwrap();
            validate_catalog(&original, &candidate, &rewrites).unwrap();
            if selected.is_empty() {
                assert_eq!(candidate, original);
            }
            if selected.len() == pcs.len() {
                assert_eq!(candidate, all);
                assert_eq!(
                    serde_json::to_value(rewrites).unwrap(),
                    serde_json::to_value(&all_rewrites).unwrap()
                );
            }
        }
        assert_eq!(transform_selected(&analysis, &[8, 2]).unwrap().0, all);
        assert!(transform_selected(&analysis, &[2, 2]).is_err());
        assert!(transform_selected(&analysis, &[0]).is_err());
        assert!(transform_selected(&analysis, &[3]).is_err()); // PUSH data
    }

    #[test]
    fn selection_catalog_retains_reachability_and_code_copy_guards() {
        for (input, guarded) in [
            ("0060020200", false),                // unreachable multiplication
            ("600760020250600360025f3900", true), // observed rewrite bytes
        ] {
            let original = bytes(input);
            let analysis = analyze(&original, guarded).unwrap();
            assert!(opportunities(&analysis).unwrap().is_empty());
            assert_eq!(transform_selected(&analysis, &[]).unwrap().0, original);
            assert!(transform_selected(&analysis, &[2]).is_err());
        }
        // Fresh analysis must not inherit a previous input's eligible PC.
        let changed = analyze(&bytes("600760030200"), false).unwrap();
        assert!(transform_selected(&changed, &[2]).is_err());
    }

    #[test]
    fn catalog_rejects_overlap_stale_fragments_and_unrecorded_changes() {
        let original = bytes("600760020200");
        let analysis = analyze(&original, false).unwrap();
        let (candidate, _) = transform(&analysis).unwrap();
        let mut catalog = opportunities(&analysis).unwrap();
        catalog.push(Rewrite {
            original_pc: 2,
            before: "600202".into(),
            after: "60011b".into(),
            required_stack: 1,
        });
        assert!(validate_catalog(&original, &candidate, &catalog).is_err());
        catalog.pop();
        let changed = bytes("600760040200");
        assert!(validate_catalog(&changed, &candidate, &catalog).is_err());
        let mut wrong_output = candidate.clone();
        wrong_output[1] = 8;
        assert!(validate_catalog(&original, &wrong_output, &catalog).is_err());
        catalog[0].after = "600150".into();
        assert!(validate_catalog(&original, &candidate, &catalog).is_err());
    }

    #[test]
    fn constant_copies_preserve_observed_bytes_and_reject_dynamic_ranges() {
        // One multiplication is live; copy three bytes from its encoding.
        let observed = bytes("600760020250600360025f3900");
        assert!(analyze(&observed, false).is_err());
        let (candidate, rewrites) = transform(&analyze(&observed, true).unwrap()).unwrap();
        assert_eq!(candidate, observed);
        assert!(rewrites.is_empty());
        // Copying the following STOP leaves the multiplication eligible.
        let disjoint = bytes("6007600202506001600b5f3900");
        let (candidate, rewrites) = transform(&analyze(&disjoint, true).unwrap()).unwrap();
        assert_eq!(rewrites.len(), 1);
        assert_eq!(&candidate[6..], &disjoint[6..]);
        for code in [
            "600160ff5f3900",   // out of bounds
            "600160005b5f3900", // executable entry splits the literal prefix
            "60015f355f3900",   // dynamic source
            "60015f3900",       // insufficient literal arguments
        ] {
            assert!(analyze(&bytes(code), true).is_err(), "{code}");
        }
        // Unreachable own-code reads must not suppress existing optimizations.
        let unreachable = bytes("60076002025000600360025f3900");
        for guarded in [false, true] {
            let analysis = analyze(&unreachable, guarded).unwrap();
            assert!(analysis.copies.is_empty());
            assert_eq!(transform(&analysis).unwrap().1.len(), 1);
        }
        // JUMPDEST bytes inside immediate data do not create entry points.
        let embedded = bytes("5f5f615b003900");
        assert!(analyze(&embedded, true).is_ok());
        assert_eq!(code_copies(&embedded)[0].destination, U256::from(0x5b00));
        let oversized = bytes(&format!("5f7f{}5f3900", "ff".repeat(32)));
        assert!(analyze(&oversized, true).is_err());
    }

    #[test]
    fn literal_folds_preserve_values_peaks_and_copied_ranges() {
        for width in [0usize, 1, 2, 32] {
            let mut first = vec![0x5f + width as u8];
            first.extend(std::iter::repeat_n(0xff, width));
            for second in [
                U256::ZERO,
                U256::from(1),
                U256::from(255),
                U256::from(256),
                U256::MAX,
            ] {
                for op in [0x16, 0x1b] {
                    let mut code = first.clone();
                    code.push(0x7f);
                    code.extend(second.to_be_bytes::<32>());
                    code.push(op);
                    code.extend(bytes("5f5260205ff3"));
                    let (candidate, rewrites) = transform(&analyze(&code, false).unwrap()).unwrap();
                    let result = compare(&code, &candidate, &case("")).unwrap();
                    assert_eq!(candidate.len(), code.len());
                    assert_eq!(
                        result.baseline_gas - result.candidate_gas,
                        rewrites.len() as u64
                    );
                    for rewrite in rewrites {
                        assert_eq!(rewrite.required_stack, 0);
                        assert_eq!(stack_signature(&bytes(&rewrite.before)).unwrap(), (0, 1, 2));
                        assert_eq!(stack_signature(&bytes(&rewrite.after)).unwrap(), (0, 1, 2));
                    }
                }
            }
        }
        // The folded value must fit the first PUSH, without discarding high bits.
        for (code, count) in [
            ("608060011b00", 0),
            ("600160081b00", 0),
            ("600160071b00", 1),
            ("5f5f1600", 1),
        ] {
            assert_eq!(
                transform(&analyze(&bytes(code), false).unwrap())
                    .unwrap()
                    .1
                    .len(),
                count
            );
        }
        for height in [0, 1, 1022, 1023, 1024] {
            let mut code = vec![0x5f; height];
            code.extend(bytes("600760031600"));
            let (candidate, rewrites) = transform(&analyze(&code, false).unwrap()).unwrap();
            assert_eq!(rewrites.len(), 1);
            let left = execute(&code, &case("")).unwrap().result;
            let right = execute(&candidate, &case("")).unwrap().result;
            assert_eq!(left.is_halt(), height >= 1023);
            assert_eq!(left.is_halt(), right.is_halt());
            if left.is_halt() {
                assert_eq!(left, right);
            }
        }
        // Copy the fold's first literal; even partial contact protects the site.
        let protected = bytes("600760031650600160015f3900");
        let (candidate, rewrites) = transform(&analyze(&protected, true).unwrap()).unwrap();
        assert_eq!(candidate, protected);
        assert!(rewrites.is_empty());
        // Multiple folds plus the previous MUL family remain ordered/disjoint.
        let mixed = bytes("60076003166002600202600f60031600");
        let (_, rewrites) = transform(&analyze(&mixed, false).unwrap()).unwrap();
        assert_eq!(
            rewrites
                .iter()
                .map(|r| r.required_stack)
                .collect::<Vec<_>>(),
            [0, 1, 0]
        );
        assert!(
            rewrites
                .windows(2)
                .all(|pair| pair[0].original_pc + pair[0].before.len() / 2 <= pair[1].original_pc)
        );
    }

    #[test]
    fn rewrites_keep_widths_stack_limits_and_word_boundaries() {
        for width in [0, 1, 2, 32] {
            let values = std::iter::once(U256::ZERO)
                .chain((0..usize::from(width) * 8).map(|shift| U256::from(1) << shift));
            for value in values {
                let mut code = bytes("5f35");
                code.push(0x5f + width);
                if width > 0 {
                    code.extend_from_slice(&value.to_be_bytes::<32>()[32 - usize::from(width)..]);
                }
                code.extend(bytes("025f5260205ff3"));
                let (candidate, rewrites) = transform(&analyze(&code, false).unwrap()).unwrap();
                assert_eq!(candidate.len(), code.len());
                assert_eq!(rewrites.len(), 1);
                for calldata in [
                    "".to_string(),
                    "01".to_string(),
                    "ff".repeat(32),
                    format!("80{}", "00".repeat(31)),
                ] {
                    let result = compare(&code, &candidate, &case(&calldata)).unwrap();
                    assert_eq!(result.baseline_gas - result.candidate_gas, 2);
                }
                assert_eq!(
                    stack_signature(&bytes(&rewrites[0].before)).unwrap(),
                    (1, 0, 1)
                );
                assert_eq!(
                    stack_signature(&bytes(&rewrites[0].after)).unwrap(),
                    (1, 0, 1)
                );
            }
        }
        // Values adjacent to powers must not be mistaken for shift rewrites.
        for literal in [
            "601f".into(),
            "6021".into(),
            "60ff".into(),
            format!("7f{}", "ff".repeat(32)),
        ] {
            let code = bytes(&format!("5f35{literal}025f5260205ff3"));
            let (candidate, changes) = transform(&analyze(&code, false).unwrap()).unwrap();
            assert_eq!(candidate, code);
            assert!(changes.is_empty());
        }
        // Preserve exceptional stack behavior too, although such cases cannot
        // pass the optimizer's success/revert-only differential validation.
        for height in [0, 1, 1023, 1024] {
            let mut code = vec![0x5f; height];
            code.extend(bytes("60020200"));
            let (candidate, _) = transform(&analyze(&code, false).unwrap()).unwrap();
            let left = execute(&code, &case("")).unwrap().result;
            let right = execute(&candidate, &case("")).unwrap().result;
            assert_eq!(left.is_halt(), right.is_halt());
            assert_eq!(left.is_halt(), matches!(height, 0 | 1024));
            if left.is_halt() {
                assert_eq!(left, right);
            }
        }
    }

    #[test]
    fn direct_ecrecover_keeps_call_fragment_and_accepts_literal_widths() {
        for width in [1u8, 2, 32] {
            // Solady's output-size/output-offset/input-size/input-offset setup.
            let mut call = bytes("60208060805f");
            call.push(0x5f + width);
            call.extend(std::iter::repeat_n(0, usize::from(width) - 1));
            call.extend([1, 0x5a, 0xfa, 0x00]);
            let mut code = bytes("600360020250"); // Independent local multiply.
            code.extend(&call);
            let (candidate, rewrites) = transform(&analyze(&code, false).unwrap()).unwrap();
            assert_eq!(rewrites.len(), 1);
            assert_eq!(&candidate[6..], call);
        }
    }

    #[test]
    fn precompile_restriction_rejects_other_targets_and_gas_uses() {
        for callee in [0u8, 2, 10, 255] {
            let mut code = bytes("60208060805f60");
            code.extend([callee, 0x5a, 0xfa, 0x00]);
            assert!(analyze(&code, false).is_err());
        }
        // Even an address-1 alias with nonzero high bits is outside the rule.
        let mut alias = bytes("60208060805f74"); // PUSH21.
        alias.push(1);
        alias.extend(std::iter::repeat_n(0, 19));
        alias.extend([1, 0x5a, 0xfa, 0x00]);
        assert!(analyze(&alias, false).is_err());
        for code in [
            "60015a805afa00",   // GAS duplicated, not immediately consumed.
            "60015a5000",       // GAS discarded rather than used by the call.
            "60015a5f5500",     // GAS stored.
            "60015a5f5200",     // GAS written to memory.
            "60015a60010100",   // GAS used in arithmetic.
            "60015a5600",       // GAS used as a jump destination.
            "60015afa5a00",     // A valid pair cannot exempt another GAS.
            "60015afa6001fa00", // Nor another STATICCALL without GAS.
            "60015af100",       // CALL remains unsupported.
            "60015bfafa00",     // A JUMPDEST cannot replace the GAS instruction.
            "60015b5afa00",     // Entry between literal callee and GAS.
            "60015a5bfa00",     // Entry between GAS and STATICCALL.
            "6260015a5afa00",   // Literal bytes inside PUSH3 cannot spoof callee.
            "6260015afa00",     // Embedded GAS cannot exempt a real STATICCALL.
        ] {
            assert!(analyze(&bytes(code), false).is_err(), "accepted {code}");
        }
    }

    #[test]
    fn dynamic_branches_cannot_enter_ecrecover_sequence() {
        // Only PC 3 is a valid branch entry. PCs 11, 12 and 13 are literal data,
        // GAS and STATICCALL respectively, so jumps to them halt before a call.
        let code = bytes("5f35565b60208060805f60015afa00");
        assert!(analyze(&code, false).is_ok());
        let valid = format!("{}03", "00".repeat(31));
        assert!(execute(&code, &case(&valid)).unwrap().result.is_success());
        for pc in [11u8, 12, 13] {
            let input = format!("{}{pc:02x}", "00".repeat(31));
            assert!(execute(&code, &case(&input)).unwrap().result.is_halt());
        }
    }

    #[test]
    fn computed_jumps_keep_offsets_and_invalid_destinations() {
        // The jump target is calldata-derived; the value 3 survives below it.
        let code = bytes("60035f35565b6002025f5260205ff3");
        assert!(super::super::analyze(&code).is_err());
        let analysis = analyze(&code, false).unwrap();
        let (candidate, changes) = transform(&analysis).unwrap();
        assert_eq!(changes.len(), 1);
        assert_eq!(analysis.jump_destinations, 1);
        let valid = format!("{}05", "00".repeat(31));
        compare(&code, &candidate, &case(&valid)).unwrap();
        for target in [0u8, 1, 6, 255] {
            let input = format!("{}{target:02x}", "00".repeat(31));
            let left = execute(&code, &case(&input)).unwrap().result;
            let right = execute(&candidate, &case(&input)).unwrap().result;
            assert!(left.is_halt());
            assert_eq!(left, right);
        }
    }

    #[test]
    fn reachability_preserves_sentinels_and_checks_both_conditional_edges() {
        // Sensitive bytes inside PUSH data and after STOP are preserved verbatim.
        let code = bytes("605b50605850605a50600260010200385a396101");
        let (candidate, changes) = transform(&analyze(&code, false).unwrap()).unwrap();
        assert_eq!(changes.len(), 1);
        assert_eq!(&candidate[..10], &code[..10]);
        assert_eq!(&candidate[14..], &code[14..]);
        assert_eq!(analyze(&code, false).unwrap().jump_destinations, 0);
        assert!(analyze(&bytes("5850385000"), false).is_ok()); // PC and CODESIZE.
        for op in [
            0x39, 0x3b, 0x3c, 0x3f, 0x5a, 0xf0, 0xf1, 0xf2, 0xf4, 0xf5, 0xfa, 0xff,
        ] {
            // A dynamic JUMPI conservatively reaches both its target and fallthrough.
            assert!(analyze(&[0x5f, 0x35, 0x5f, 0x35, 0x57, op, 0x00, 0x5b, 0x00], false).is_err());
            assert!(analyze(&[0x5f, 0x35, 0x56, 0x00, 0x5b, op], false).is_err());
        }
        assert!(analyze(&bytes("6101"), false).is_err());
        assert!(analyze(&bytes("ef00"), false).is_err());
        assert!(analyze(&vec![0; MAX_RUNTIME_BYTES + 1], false).is_err());
        assert!(analyze(&[], false).is_ok());
        // A real JUMPDEST splits the fragment and must prevent matching.
        let code = bytes("600260025b0200");
        assert!(
            transform(&analyze(&code, false).unwrap())
                .unwrap()
                .1
                .is_empty()
        );
        // A jump cycle visits each decoded PC at most once.
        assert_eq!(
            analyze(&bytes("5b5f3556"), false)
                .unwrap()
                .reachable_instructions,
            4
        );
    }
}
