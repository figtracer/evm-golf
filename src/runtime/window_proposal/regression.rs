use super::certificate;
use crate::{
    proof,
    runtime::{Case, Rewrite, artifact, execute, from_hex},
};
use revm::{
    context::result::ExecutionResult,
    primitives::{U256, hex},
};
use std::{collections::BTreeMap, fs};
use tempfile::tempdir;

fn word_push(value: U256) -> Vec<u8> {
    let mut code = vec![0x7f];
    code.extend(value.to_be_bytes::<32>());
    code
}

fn closed_pairs() -> Vec<(Vec<u8>, Vec<u8>, U256)> {
    let high = U256::from(1) << 255;
    let mut cases = Vec::new();
    for (shift, expected) in [
        (U256::ZERO, U256::from(1)),
        (U256::from(1), U256::from(2)),
        (U256::from(255), high),
        (U256::from(256), U256::ZERO),
        (U256::from(257), U256::ZERO),
        (U256::MAX, U256::ZERO),
    ] {
        let before = [vec![0x60, 1], word_push(shift), vec![0x1b]].concat();
        let after = [word_push(expected), vec![0x60, 0, 0x50]].concat();
        cases.push((before, after, expected));
    }
    // SUB pops its first operand from the top, including modular underflow.
    for (next, top, expected) in [
        (1, U256::ZERO, U256::MAX),
        (0, U256::from(1), U256::from(1)),
        (1, U256::MAX, U256::MAX - U256::from(1)),
    ] {
        let before = [vec![0x60, next], word_push(top), vec![0x03]].concat();
        let after = [word_push(expected), vec![0x60, 0, 0x50]].concat();
        cases.push((before, after, expected));
    }
    cases
}

fn run(code: &[u8]) -> ExecutionResult {
    execute(
        code,
        &Case {
            calldata: String::new(),
            gas_limit: 200000,
            value: String::new(),
            storage: BTreeMap::new(),
        },
    )
    .unwrap()
    .result
}

#[test]
fn shift_and_subtraction_proposals_preserve_values_and_fault_boundaries() {
    for (before, after, expected) in closed_pairs() {
        certificate(&before, &after).unwrap();
        for fragment in [&before, &after] {
            let code = [fragment.as_slice(), &[0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]].concat();
            let result = run(&code);
            assert!(result.is_success());
            assert_eq!(U256::from_be_slice(result.output().unwrap()), expected);
        }
        for height in [0, 1, 1022, 1023, 1024] {
            let prefix = vec![0x5f; height];
            let left = run(&[prefix.as_slice(), &before, &[0]].concat());
            let right = run(&[prefix.as_slice(), &after, &[0]].concat());
            assert_eq!(left.is_halt(), height >= 1023);
            if left.is_halt() {
                assert_eq!(left, right);
            } else {
                assert!(right.is_success());
                assert_eq!(left.tx_gas_used() - right.tx_gas_used(), 1);
            }
        }
    }
    for opcode in [0x03, 0x1b] {
        let before = [from_hex("600150600250").unwrap(), vec![opcode]].concat();
        let after = [from_hex("630000000050").unwrap(), vec![opcode]].concat();
        certificate(&before, &after).unwrap();
        for height in [0, 1, 2, 1023, 1024] {
            let prefix = vec![0x5f; height];
            let left = run(&[prefix.as_slice(), &before, &[0]].concat());
            let right = run(&[prefix.as_slice(), &after, &[0]].concat());
            assert_eq!(left.is_halt(), height < 2 || height == 1024);
            if left.is_halt() {
                assert_eq!(left, right);
            } else {
                assert!(right.is_success());
                assert_eq!(left.tx_gas_used() - right.tx_gas_used(), 5);
            }
        }
    }
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn kernel_checks_closed_arithmetic_and_symbolic_shift_subtraction() {
    let directory = tempdir().unwrap();
    let mut cases: Vec<_> = closed_pairs().into_iter().map(|(a, b, _)| (a, b)).collect();
    // The new wider literal cannot use the old width-preserving SHL fold.
    cases.push((
        from_hex("600160081b").unwrap(),
        from_hex("6101005f50").unwrap(),
    ));
    for opcode in [0x03, 0x1b] {
        cases.push((
            [from_hex("600150600250").unwrap(), vec![opcode]].concat(),
            [from_hex("630000000050").unwrap(), vec![opcode]].concat(),
        ));
    }
    for (index, (before, after)) in cases.into_iter().enumerate() {
        let local = certificate(&before, &after).unwrap();
        let site = Rewrite {
            original_pc: 1,
            before: hex::encode(&before),
            after: hex::encode(&after),
            required_stack: local.required,
        };
        let original = [vec![0x5b], before, vec![0]].concat();
        let candidate = [vec![0x5b], after, vec![0]].concat();
        let (source, names) =
            artifact::proposal_certificate(&original, &candidate, &site, &[], local).unwrap();
        let path = directory.path().join(format!("Arithmetic{index}.lean"));
        fs::write(&path, source).unwrap();
        let checked = proof::verify_named(&path, &names, proof::AxiomPolicy::Foundational);
        assert!(
            checked.is_ok(),
            "{checked:?}\n{}",
            fs::read_to_string(path.with_extension("log")).unwrap_or_default()
        );
    }
}
