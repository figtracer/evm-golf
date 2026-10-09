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
        let (source, names) = artifact::proposal_batch_certificate(
            &original,
            &candidate,
            std::slice::from_ref(&site),
            &[],
        )
        .unwrap();
        let path = directory.path().join(format!("Arithmetic{index}.lean"));
        fs::write(&path, source).unwrap();
        let checked = proof::verify_named(&path, &names);
        assert!(
            checked.is_ok(),
            "{checked:?}\n{}",
            fs::read_to_string(path.with_extension("log")).unwrap_or_default()
        );
    }
}

#[test]
fn neutral_stack_aliases_preserve_every_word_and_fault_class() {
    for depth in 1usize..=8 {
        let before = vec![0x7f + depth as u8, 0x60, 0, 0x01];
        let after = vec![0x7f + depth as u8, 0x60, 0, 0x50];
        let local = certificate(&before, &after).unwrap();
        assert_eq!((local.required, local.delta, local.peak), (depth, 1, 2));
        let mut words = vec![U256::MAX, U256::ZERO, U256::from(1) << 255];
        words.extend((0..depth).map(|i| U256::from(i + 17)));
        let expected: Vec<u8> = std::iter::once(words[depth - 1])
            .chain(words.iter().copied())
            .flat_map(|word| word.to_be_bytes::<32>())
            .collect();
        for fragment in [&before, &after] {
            let mut code: Vec<u8> = words.iter().rev().copied().flat_map(word_push).collect();
            code.extend(fragment);
            for index in 0..=words.len() {
                code.extend(word_push(U256::from(index * 32)));
                code.push(0x52);
            }
            code.extend(word_push(U256::from(expected.len())));
            code.extend([0x5f, 0xf3]);
            let result = run(&code);
            assert!(result.is_success());
            assert_eq!(result.output().unwrap().as_ref(), expected.as_slice());
        }
        for height in [0, depth - 1, depth, depth + 3, 1022, 1023, 1024] {
            let prefix = vec![0x5f; height];
            let left = run(&[prefix.as_slice(), &before, &[0]].concat());
            let right = run(&[prefix.as_slice(), &after, &[0]].concat());
            assert_eq!(left.is_halt(), height < depth || height >= 1023);
            if left.is_halt() {
                assert_eq!(left, right);
            } else {
                assert!(right.is_success());
                assert_eq!(left.tx_gas_used() - right.tx_gas_used(), 1);
            }
        }
    }
    // Removing ADD without retaining a depth-establishing instruction loses the
    // required input and changes failure behavior at an empty stack.
    assert!(certificate(&from_hex("600001").unwrap(), &from_hex("600050").unwrap()).is_err());
    // A different DUP depth changes the alias and entry stack requirement.
    assert!(
        certificate(
            &from_hex("81600001").unwrap(),
            &from_hex("80600050").unwrap()
        )
        .is_err()
    );
    assert!(
        certificate(
            &from_hex("88600001").unwrap(),
            &from_hex("88600050").unwrap()
        )
        .is_err()
    );
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn kernel_checks_stack_aliases_neutral_addition_and_wrapping_addition() {
    let directory = tempdir().unwrap();
    let mut pairs: Vec<(Vec<u8>, Vec<u8>)> = (1u8..=8)
        .map(|depth| {
            (
                vec![0x7f + depth, 0x60, 0, 0x01],
                vec![0x7f + depth, 0x60, 0, 0x50],
            )
        })
        .collect();
    // Closed addition wraps independently of the neutral symbolic rules.
    pairs.push((
        [vec![0x60, 1], word_push(U256::MAX), vec![0x01]].concat(),
        [word_push(U256::ZERO), vec![0x60, 0, 0x50]].concat(),
    ));
    // Exercise the opposite zero operand order after a checked alias.
    pairs.push((from_hex("5f8101").unwrap(), from_hex("805f50").unwrap()));
    // Temporary growth permits DUP9 while still requiring only eight inputs.
    pairs.push((from_hex("5f8801").unwrap(), from_hex("875f50").unwrap()));
    for (index, (before, after)) in pairs.into_iter().enumerate() {
        let local = certificate(&before, &after).unwrap();
        let rewrite = Rewrite {
            original_pc: 1,
            before: hex::encode(&before),
            after: hex::encode(&after),
            required_stack: local.required,
        };
        let original = [vec![0x5b], before, vec![0]].concat();
        let candidate = [vec![0x5b], after, vec![0]].concat();
        let (source, names) = artifact::proposal_batch_certificate(
            &original,
            &candidate,
            std::slice::from_ref(&rewrite),
            &[],
        )
        .unwrap();
        let path = directory.path().join(format!("Alias{index}.lean"));
        fs::write(&path, source).unwrap();
        let result = proof::verify_named(&path, &names);
        assert!(
            result.is_ok(),
            "{result:?}\n{}",
            fs::read_to_string(path.with_extension("log")).unwrap_or_default()
        );
    }
}

struct PermutationCase {
    before: &'static str,
    after: &'static str,
    required: usize,
    peak: usize,
    saving: u64,
    destination: u64,
    surviving_inputs: &'static [usize],
}

const PERMUTATIONS: &[PermutationCase] = &[
    PermutationCase {
        before: "9092509050612270",
        after: "9150915062002270",
        required: 4,
        peak: 0,
        saving: 3,
        destination: 0x2270,
        surviving_inputs: &[0, 1],
    },
    PermutationCase {
        before: "9095509050611616",
        after: "9150945062001616",
        required: 7,
        peak: 0,
        saving: 3,
        destination: 0x1616,
        surviving_inputs: &[0, 3, 4, 5, 1],
    },
    PermutationCase {
        before: "939092909190614acf",
        after: "939190926300004acf",
        required: 5,
        peak: 1,
        saving: 6,
        destination: 0x4acf,
        surviving_inputs: &[3, 2, 4, 1, 0],
    },
];

#[test]
fn permutation_proposals_preserve_full_stack_and_fault_boundaries() {
    let mut words = vec![U256::MAX, U256::ZERO, U256::from(1) << 255];
    words.extend((0..7).map(|i| U256::from(i + 17)));
    for case in PERMUTATIONS {
        let before = from_hex(case.before).unwrap();
        let after = from_hex(case.after).unwrap();
        let local = certificate(&before, &after).unwrap();
        let delta = case.surviving_inputs.len() as isize + 1 - case.required as isize;
        assert_eq!(
            (local.required, local.delta, local.peak),
            (case.required, delta, case.peak)
        );
        let expected: Vec<u8> = std::iter::once(U256::from(case.destination))
            .chain(case.surviving_inputs.iter().map(|&i| words[i]))
            .chain(words[case.required..].iter().copied())
            .flat_map(|word| word.to_be_bytes::<32>())
            .collect();
        for fragment in [&before, &after] {
            let mut code: Vec<u8> = words.iter().rev().copied().flat_map(word_push).collect();
            code.extend(fragment);
            for i in 0..expected.len() / 32 {
                code.extend(word_push(U256::from(i * 32)));
                code.push(0x52);
            }
            code.extend(word_push(U256::from(expected.len())));
            code.extend([0x5f, 0xf3]);
            let result = run(&code);
            assert!(result.is_success());
            assert_eq!(result.output().unwrap().as_ref(), expected.as_slice());
        }
        for height in (0..=case.required + 1).chain([1022, 1023, 1024]) {
            let prefix = vec![0x5f; height];
            let left = run(&[prefix.as_slice(), &before, &[0]].concat());
            let right = run(&[prefix.as_slice(), &after, &[0]].concat());
            assert_eq!(
                left.is_halt(),
                height < case.required || height + case.peak > 1024
            );
            if left.is_halt() {
                assert_eq!(left, right);
            } else {
                assert!(right.is_success());
                assert_eq!(left.tx_gas_used() - right.tx_gas_used(), case.saving);
            }
        }
    }
    // Same profile and cost do not establish the same surviving aliases.
    let before = from_hex(PERMUTATIONS[0].before).unwrap();
    let wrong_alias = from_hex("9050915062002270").unwrap();
    let (_, before_profile) = super::inspect(&before).unwrap();
    let (_, wrong_profile) = super::inspect(&wrong_alias).unwrap();
    assert_eq!(
        (
            before_profile.required,
            before_profile.delta,
            before_profile.peak
        ),
        (
            wrong_profile.required,
            wrong_profile.delta,
            wrong_profile.peak
        )
    );
    assert!(
        certificate(&before, &wrong_alias)
            .err()
            .unwrap()
            .to_string()
            .contains("symbolic output equality")
    );
    // A straight SWAP8 requires nine inputs, beyond the existing window bound.
    assert!(certificate(&from_hex("975f01").unwrap(), &from_hex("975f50").unwrap()).is_err());
    // SWAP underflow must not be confused with missing-input DUP overflow.
    assert_ne!(
        super::fault(&super::decode(&[0x90]), 1),
        super::fault(&super::decode(&[0x80]), 0)
    );
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn kernel_checks_exact_stack_permutation_artifacts() {
    let directory = tempdir().unwrap();
    for (index, case) in PERMUTATIONS.iter().enumerate() {
        let before = from_hex(case.before).unwrap();
        let after = from_hex(case.after).unwrap();
        let local = certificate(&before, &after).unwrap();
        let rewrite = Rewrite {
            original_pc: 1,
            before: hex::encode(&before),
            after: hex::encode(&after),
            required_stack: local.required,
        };
        let original = [vec![0x5b], before, vec![0]].concat();
        let candidate = [vec![0x5b], after, vec![0]].concat();
        let (source, names) = artifact::proposal_batch_certificate(
            &original,
            &candidate,
            std::slice::from_ref(&rewrite),
            &[],
        )
        .unwrap();
        let path = directory.path().join(format!("Permutation{index}.lean"));
        fs::write(&path, source).unwrap();
        let result = proof::verify_named(&path, &names);
        assert!(
            result.is_ok(),
            "{result:?}\n{}",
            fs::read_to_string(path.with_extension("log")).unwrap_or_default()
        );
    }
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn kernel_checks_static_gas_against_revm_and_budget_boundaries() {
    use revm::{interpreter::instructions::gas_table_spec, primitives::hardfork::SpecId};
    use std::fmt::Write as _;

    let mut source = super::prelude().unwrap();
    source.push_str("\nnamespace GolfGasRegression\n");
    // These values come from the pinned interpreter, not the Rust proposal profiler.
    // Equal pure costs do not establish support for each fork's transaction rules.
    let mut costs = Vec::new();
    for fork in [SpecId::CANCUN, SpecId::PRAGUE, SpecId::OSAKA] {
        let table = gas_table_spec(fork);
        for op in [0x01, 0x02, 0x03, 0x16, 0x17, 0x18, 0x19, 0x1b, 0x50]
            .into_iter()
            .chain(0x5f..=0x9f)
        {
            costs.push(format!("({op},{})", table[op]));
        }
    }
    writeln!(source, "def costs : List (Nat × Nat) := [{}]\ntheorem revm_costs : costs.all (fun p => GolfGas.cancun p.1 == some p.2) = true := by decide +kernel", costs.join(",")).unwrap();
    // Opcode-looking PUSH data must not be charged as instructions.
    for width in 1u8..=32 {
        let code = [vec![0x5f + width], vec![0x50; usize::from(width)]].concat();
        writeln!(
            source,
            "example : GolfGas.cost {code:?} = some 3 := by decide +kernel"
        )
        .unwrap();
    }
    source.push_str("example : GolfGas.cost [95] = some 2 := by decide +kernel\nexample : GolfGas.cost [97,80] = none := by decide +kernel\nexample : GolfGas.cost [90] = none := by decide +kernel\nexample : GolfGas.cost [241] = none := by decide +kernel\n");
    let before = from_hex("600050600050").unwrap();
    let after = from_hex("630000000050").unwrap();
    for gas in [0, 4, 5, 9, 10, 20] {
        for (code, cost) in [(&before, 10), (&after, 5)] {
            let executed = execute(
                code,
                &Case {
                    calldata: String::new(),
                    gas_limit: 21_000 + gas,
                    value: String::new(),
                    storage: BTreeMap::new(),
                },
            )
            .unwrap()
            .result;
            assert_eq!(executed.is_success(), gas >= cost);
            if executed.is_success() {
                assert_eq!(executed.tx_gas_used(), 21_000 + cost);
            }
            let expected = if gas < cost {
                "none".to_owned()
            } else {
                format!("some ([], {})", gas - cost)
            };
            writeln!(source, "example : GolfGas.run GolfGas.cancun {} {code:?} [] {gas} 0 0 = {expected} := by decide +kernel", code.len()+1).unwrap();
        }
    }
    source.push_str("end GolfGasRegression\n#print axioms GolfGasRegression.revm_costs\n#print axioms GolfGas.sufficient\n#print axioms GolfGas.Improvement.refines\n");
    let directory = tempdir().unwrap();
    let path = directory.path().join("Gas.lean");
    fs::write(&path, &source).unwrap();
    let names = [
        "GolfGasRegression.revm_costs".to_owned(),
        "GolfGas.sufficient".to_owned(),
        "GolfGas.Improvement.refines".to_owned(),
    ];
    let checked = proof::verify_named(&path, &names);
    assert!(
        checked.is_ok(),
        "{checked:?}\n{}",
        fs::read_to_string(path.with_extension("log")).unwrap_or_default()
    );

    // Kernel rejection must not depend on the Rust cheaper-cost prefilter.
    let local = certificate(&before, &after).unwrap();
    let path = directory.path().join("LocalGas.lean");
    fs::write(&path, &local.source).unwrap();
    let checked = proof::verify_named(&path, &local.names);
    assert!(
        checked.is_ok(),
        "{checked:?}\n{}",
        fs::read_to_string(path.with_extension("log")).unwrap_or_default()
    );
    for (name, changed) in [
        (
            "FalseCost",
            local
                .source
                .replacen("beforeCost := 10", "beforeCost := 9", 1),
        ),
        (
            "EqualCost",
            local
                .source
                .replacen("afterCost := 5", "afterCost := 10", 1),
        ),
        (
            "FreePadding",
            local.source.replace(
                "if op = 80 ∨ op = 95 then some 2",
                "if op = 80 ∨ op = 95 then some 0",
            ),
        ),
    ] {
        assert_ne!(changed, local.source);
        let path = directory.path().join(format!("{name}.lean"));
        fs::write(&path, changed).unwrap();
        assert!(
            proof::verify_named(&path, &local.names).is_err(),
            "accepted {name}"
        );
        let log = fs::read_to_string(path.with_extension("log")).unwrap();
        assert!(
            log.contains("error:"),
            "expected a Lean rejection, not a timeout: {log}"
        );
    }
}

fn bitwise_pairs() -> Vec<(Vec<u8>, Vec<u8>)> {
    let mut pairs = [
        ("80600017", "80600050"),
        ("80600018", "80600050"),
        ("5f8117", "805f50"),
        ("5f8118", "805f50"),
        ("8017", "8050"),
        ("80801850", "805f5050"),
        ("805f501919", "8061000050"),
        ("600f60f017", "6100ff5f50"),
        ("60aa605518", "6100ff5f50"),
    ]
    .map(|(a, b)| (from_hex(a).unwrap(), from_hex(b).unwrap()))
    .to_vec();
    let literal: U256 = (U256::from(1) << 248) - U256::from(1);
    pairs.push((
        [vec![0x7e], vec![0xff; 31], vec![0x19]].concat(),
        word_push(!literal),
    ));
    pairs
}

#[test]
fn bitwise_proposals_preserve_words_and_stack_faults() {
    for (before, after) in bitwise_pairs() {
        let local = certificate(&before, &after).unwrap();
        for word in [
            U256::ZERO,
            U256::MAX,
            U256::from(1) << 255,
            U256::from(0xdeadbeefu64),
        ] {
            let lower = word_push(!word);
            let prefix = word_push(word);
            // Return both the result and the unmodified word below it.
            let suffix = from_hex("5f5260205260405ff3").unwrap();
            let left = run(&[lower.as_slice(), prefix.as_slice(), &before, &suffix].concat());
            let right = run(&[lower.as_slice(), prefix.as_slice(), &after, &suffix].concat());
            assert!(left.is_success() && right.is_success());
            assert_eq!(left.output(), right.output());
            assert!(right.tx_gas_used() < left.tx_gas_used());
        }
        for height in [0, 1, 1022, 1023, 1024] {
            let prefix = vec![0x5f; height];
            let left = run(&[prefix.as_slice(), &before, &[0]].concat());
            let right = run(&[prefix.as_slice(), &after, &[0]].concat());
            assert_eq!(
                left.is_halt(),
                height < local.required || height + local.peak > 1024
            );
            if left.is_halt() {
                assert_eq!(left, right);
            } else {
                assert!(right.is_success());
                assert!(right.tx_gas_used() < left.tx_gas_used());
            }
        }
    }
    // XOR is not OR, and removing NOT's input requirement changes underflow.
    assert!(certificate(&from_hex("8018").unwrap(), &from_hex("8050").unwrap()).is_err());
    assert!(certificate(&from_hex("1919").unwrap(), &from_hex("5f50").unwrap()).is_err());
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn kernel_checks_bitwise_proposals_and_rejects_wrong_results() {
    let directory = tempdir().unwrap();
    for (index, (before, after)) in bitwise_pairs().into_iter().enumerate() {
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
            artifact::proposal_batch_certificate(&original, &candidate, &[site], &[]).unwrap();
        let path = directory.path().join(format!("Bitwise{index}.lean"));
        fs::write(&path, &source).unwrap();
        let checked = proof::verify_named(&path, &names);
        assert!(
            checked.is_ok(),
            "{checked:?}\n{}",
            fs::read_to_string(path.with_extension("log")).unwrap_or_default()
        );
        if index == 4 {
            // Keep the claimed output and profile but replace OR with XOR in the model.
            let changed = source.replace("(a ||| b)", "(a ^^^ b)");
            assert_ne!(changed, source);
            let path = directory.path().join("WrongBitwise.lean");
            fs::write(&path, changed).unwrap();
            assert!(proof::verify_named(&path, &names).is_err());
            assert!(
                fs::read_to_string(path.with_extension("log"))
                    .unwrap()
                    .contains("error:")
            );
        }
    }
}

fn multiplication_pairs() -> Vec<(Vec<u8>, Vec<u8>, u64)> {
    let mut pairs = [
        ("600102", "600001", 2),
        ("60018102", "60008101", 2),
        ("805f02", "5f8150", 3),
        ("5f8102", "5f8150", 3),
        ("6002600302", "6006600050", 3),
        ("8090026001", "8002610001", 3),
        ("819090026001", "810262000001", 6),
    ]
    .map(|(before, after, saving)| (from_hex(before).unwrap(), from_hex(after).unwrap(), saving))
    .to_vec();
    for (value, expected) in [
        (U256::MAX, U256::MAX - U256::ONE),
        (U256::ONE << 255, U256::ZERO),
    ] {
        pairs.push((
            [vec![0x60, 2], word_push(value), vec![0x02]].concat(),
            [word_push(expected), vec![0x60, 0, 0x50]].concat(),
            3,
        ));
    }
    pairs
}

#[test]
fn multiplication_proposals_preserve_words_gas_and_stack_faults() {
    for (before, after, saving) in multiplication_pairs() {
        let local = certificate(&before, &after).unwrap();
        for word in [U256::ZERO, U256::ONE, U256::MAX, U256::ONE << 255] {
            let lower = word_push(!word);
            let prefix = word_push(word);
            let suffix = from_hex("5f5260205260405ff3").unwrap();
            let left = run(&[lower.as_slice(), prefix.as_slice(), &before, &suffix].concat());
            let right = run(&[lower.as_slice(), prefix.as_slice(), &after, &suffix].concat());
            assert!(left.is_success() && right.is_success());
            assert_eq!(left.output(), right.output());
            assert_eq!(left.tx_gas_used() - right.tx_gas_used(), saving);
        }
        for height in [0, 1, 1022, 1023, 1024] {
            let prefix = vec![0x5f; height];
            let left = run(&[prefix.as_slice(), &before, &[0]].concat());
            let right = run(&[prefix.as_slice(), &after, &[0]].concat());
            assert_eq!(
                left.is_halt(),
                height < local.required || height + local.peak > 1024
            );
            if left.is_halt() {
                assert_eq!(left, right);
            } else {
                assert!(right.is_success());
                assert_eq!(left.tx_gas_used() - right.tx_gas_used(), saving);
            }
        }
    }
    assert!(certificate(&from_hex("600202").unwrap(), &from_hex("600001").unwrap()).is_err());
    assert!(certificate(&from_hex("5f02").unwrap(), &from_hex("505f").unwrap()).is_err());
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn kernel_checks_multiplication_proposals_and_rejects_wrong_semantics() {
    let directory = tempdir().unwrap();
    for (index, (before, after, _)) in multiplication_pairs().into_iter().enumerate() {
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
            artifact::proposal_batch_certificate(&original, &candidate, &[site], &[]).unwrap();
        let path = directory.path().join(format!("Multiplication{index}.lean"));
        fs::write(&path, &source).unwrap();
        let checked = proof::verify_named(&path, &names);
        assert!(
            checked.is_ok(),
            "{checked:?}\n{}",
            fs::read_to_string(path.with_extension("log")).unwrap_or_default()
        );
        if index == 0 {
            let wrong = source.replace("(a * b)", "(a + b)");
            assert_ne!(source, wrong);
            let path = directory.path().join("WrongMultiplication.lean");
            fs::write(&path, wrong).unwrap();
            assert!(proof::verify_named(&path, &names).is_err());
            assert!(
                fs::read_to_string(path.with_extension("log"))
                    .unwrap()
                    .contains("error:")
            );
        }
    }
}
