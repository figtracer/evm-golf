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
        // GAS is admitted only in the inseparable literal-1 ECRECOVER pattern.
        let supported = match op {
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
            let values = std::iter::once(U256::ZERO)
                .chain((0..usize::from(width) * 8).map(|shift| U256::from(1) << shift));
            for value in values {
                let mut code = bytes("5f35");
                code.push(0x5f + width);
                if width > 0 {
                    code.extend_from_slice(&value.to_be_bytes::<32>()[32 - usize::from(width)..]);
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
        // Values adjacent to powers must not be mistaken for shift rewrites.
        for literal in [
            "601f".into(),
            "6021".into(),
            "60ff".into(),
            format!("7f{}", "ff".repeat(32)),
        ] {
            let code = bytes(&format!("5f35{literal}025f5260205ff3"));
            let (candidate, changes) = transform(&analyze(&code).unwrap()).unwrap();
            assert_eq!(candidate, code);
            assert!(changes.is_empty());
        }
        // Preserve exceptional stack behavior too, although such cases cannot
        // pass the optimizer's success/revert-only differential validation.
        for height in [0, 1, 1023, 1024] {
            let mut code = vec![0x5f; height];
            code.extend(bytes("60020200"));
            let (candidate, _) = transform(&analyze(&code).unwrap()).unwrap();
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
            let (candidate, rewrites) = transform(&analyze(&code).unwrap()).unwrap();
            assert_eq!(rewrites.len(), 1);
            assert_eq!(&candidate[6..], call);
        }
    }

    #[test]
    fn precompile_restriction_rejects_other_targets_and_gas_uses() {
        for callee in [0u8, 2, 10, 255] {
            let mut code = bytes("60208060805f60");
            code.extend([callee, 0x5a, 0xfa, 0x00]);
            assert!(analyze(&code).is_err());
        }
        // Even an address-1 alias with nonzero high bits is outside the rule.
        let mut alias = bytes("60208060805f74"); // PUSH21.
        alias.push(1);
        alias.extend(std::iter::repeat_n(0, 19));
        alias.extend([1, 0x5a, 0xfa, 0x00]);
        assert!(analyze(&alias).is_err());
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
            assert!(analyze(&bytes(code)).is_err(), "accepted {code}");
        }
    }

    #[test]
    fn dynamic_branches_cannot_enter_ecrecover_sequence() {
        // Only PC 3 is a valid branch entry. PCs 11, 12 and 13 are literal data,
        // GAS and STATICCALL respectively, so jumps to them halt before a call.
        let code = bytes("5f35565b60208060805f60015afa00");
        assert!(analyze(&code).is_ok());
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
        let analysis = analyze(&code).unwrap();
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
