//! Equal-length rewrites that preserve all possible legacy jump destinations.

use anyhow::{Context as _, Result, ensure};
use revm::{
    bytecode::opcode::OpCode,
    primitives::{U256, hex},
};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

use super::{Instruction, MAX_RUNTIME_BYTES, Rewrite, allowed, decode, push_value};

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
}

pub(super) fn analyze(code: &[u8]) -> Result<LayoutAnalysis> {
    ensure!(
        code.len() <= MAX_RUNTIME_BYTES,
        "runtime exceeds EIP-170 size limit"
    );
    ensure!(
        !code.starts_with(&[0xef, 0x00]),
        "EOF bytecode is unsupported"
    );
    let instructions = decode(code);
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
        let instruction =
            &instructions[*index.get(&pc).context("control flow enters PUSH data")?];
        let op = instruction.bytes[0];
        // PC and CODESIZE are stable because no instruction or byte is moved.
        // Code contents, GAS and external execution are still sensitive.
        ensure!(
            allowed(op) || matches!(op, 0x38 | 0x58),
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
        reachable,
    })
}

pub(super) fn transform(analysis: &LayoutAnalysis) -> Result<(Vec<u8>, Vec<Rewrite>)> {
    let mut instructions = analysis.instructions.clone();
    let mut rewrites = Vec::new();
    for i in 0..instructions.len().saturating_sub(1) {
        let a = &instructions[i];
        let b = &instructions[i + 1];
        if !analysis.reachable.contains(&a.pc)
            || !analysis.reachable.contains(&b.pc)
            || b.bytes[0] != 0x02
        {
            continue;
        }
        let Some(value) = push_value(&a.bytes) else {
            continue;
        };
        let (constant, operation) = if value.is_zero() {
            (0, 0x16) // x * 0 = x & 0.
        } else if value == U256::from(1) {
            (0, 0x01) // x * 1 = x + 0.
        } else if value == U256::from(2) {
            (1, 0x1b) // x * 2 = x << 1, including wrapping overflow.
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
    let decoded = decode(&candidate);
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
    Ok((candidate, rewrites))
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
    fn rewrites_keep_widths_stack_limits_and_word_boundaries() {
        for width in [0, 1, 2, 32] {
            for value in 0..=2u8 {
                if width == 0 && value != 0 {
                    continue;
                }
                let mut code = bytes("5f35");
                code.push(0x5f + width);
                if width > 0 {
                    code.extend(std::iter::repeat_n(0, usize::from(width) - 1));
                    code.push(value);
                }
                code.extend(bytes("025f5260205ff3"));
                let (candidate, rewrites) = transform(&analyze(&code).unwrap()).unwrap();
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
        // Preserve exceptional stack behavior too, although such cases cannot
        // pass the optimizer's success/revert-only differential validation.
        for height in [0, 1, 1023, 1024] {
            let mut code = vec![0x5f; height];
            code.extend(bytes("60020200"));
            let (candidate, _) = transform(&analyze(&code).unwrap()).unwrap();
            let (left, _) = execute(&code, &case("")).unwrap();
            let (right, _) = execute(&candidate, &case("")).unwrap();
            assert_eq!(left.is_halt(), right.is_halt());
            assert_eq!(left.is_halt(), matches!(height, 0 | 1024));
            if left.is_halt() {
                assert_eq!(left, right);
            }
        }
    }

    #[test]
    fn computed_jumps_keep_offsets_and_invalid_destinations() {
        // The jump target is calldata-derived; the value 3 survives below it.
        let code = bytes("60035f35565b6002025f5260205ff3");
        assert!(super::super::analyze(&code).is_err());
        let analysis = analyze(&code).unwrap();
        let (candidate, changes) = transform(&analysis).unwrap();
        assert_eq!(changes.len(), 1);
        assert_eq!(analysis.jump_destinations, 1);
        let valid = format!("{}05", "00".repeat(31));
        compare(&code, &candidate, &case(&valid)).unwrap();
        for target in [0u8, 1, 6, 255] {
            let input = format!("{}{target:02x}", "00".repeat(31));
            let (left, _) = execute(&code, &case(&input)).unwrap();
            let (right, _) = execute(&candidate, &case(&input)).unwrap();
            assert!(left.is_halt());
            assert_eq!(left, right);
        }
    }

    #[test]
    fn reachability_preserves_sentinels_and_checks_both_conditional_edges() {
        // Sensitive bytes inside PUSH data and after STOP are preserved verbatim.
        let code = bytes("605b50605850605a50600260010200385a396101");
        let (candidate, changes) = transform(&analyze(&code).unwrap()).unwrap();
        assert_eq!(changes.len(), 1);
        assert_eq!(&candidate[..10], &code[..10]);
        assert_eq!(&candidate[14..], &code[14..]);
        assert_eq!(analyze(&code).unwrap().jump_destinations, 0);
        assert!(analyze(&bytes("5850385000")).is_ok()); // PC and CODESIZE.
        for op in [
            0x39, 0x3b, 0x3c, 0x3f, 0x5a, 0xf0, 0xf1, 0xf2, 0xf4, 0xf5, 0xfa, 0xff,
        ] {
            // A dynamic JUMPI conservatively reaches both its target and fallthrough.
            assert!(analyze(&[0x5f, 0x35, 0x5f, 0x35, 0x57, op, 0x00, 0x5b, 0x00]).is_err());
            assert!(analyze(&[0x5f, 0x35, 0x56, 0x00, 0x5b, op]).is_err());
        }
        assert!(analyze(&bytes("6101")).is_err());
        assert!(analyze(&bytes("ef00")).is_err());
        assert!(analyze(&vec![0; MAX_RUNTIME_BYTES + 1]).is_err());
        assert!(analyze(&[]).is_ok());
        // A real JUMPDEST splits the fragment and must prevent matching.
        let code = bytes("600260025b0200");
        assert!(transform(&analyze(&code).unwrap()).unwrap().1.is_empty());
        // A jump cycle visits each decoded PC at most once.
        assert_eq!(
            analyze(&bytes("5b5f3556")).unwrap().reachable_instructions,
            4
        );
    }
}
