use evm_golf::{
    evm::{Program, cross_check},
    expr::{RULES, evaluate, optimize, parse},
};
use revm::primitives::U256;

#[test]
fn compiler_matches_evm_at_word_boundaries() {
    for text in [
        "(+ x y)",
        "(- x y)",
        "(* x y)",
        "(and x y)",
        "(or x y)",
        "(xor x y)",
        "(not x)",
        "(shl1 x)",
        "0",
        "255",
        "256",
        "65536",
        "115792089237316195423570985008687907853269984665640564039457584007913129639935",
    ] {
        let expr = parse(text).unwrap();
        let program = Program::compile(&expr).unwrap();
        assert_eq!(cross_check(&expr, &expr, &program, &program).unwrap(), 128);
    }
    let subtraction = Program::compile(&parse("(- x y)").unwrap()).unwrap();
    assert_eq!(
        subtraction.execute(U256::from(2), U256::from(7)).unwrap().0,
        U256::MAX - U256::from(4)
    );
    assert_eq!(
        evaluate(&parse("(+ x 1)").unwrap(), U256::MAX, U256::ZERO),
        U256::ZERO
    );
}

#[test]
fn search_reduces_cost_without_changing_concrete_results() {
    let original = parse("(+ (* x 2) (- y y))").unwrap();
    let candidate = optimize(&original);
    let baseline = Program::compile(&original).unwrap();
    let optimized = Program::compile(&candidate).unwrap();
    assert_eq!(candidate.to_string(), "(shl1 x)");
    assert_eq!((baseline.body_gas, optimized.body_gas), (28, 11));
    cross_check(&original, &candidate, &baseline, &optimized).unwrap();
}

#[test]
fn parser_rejects_unsupported_or_unbounded_inputs() {
    for input in [
        "",
        "z",
        "-1",
        "(+ x)",
        "(div x y)",
        "115792089237316195423570985008687907853269984665640564039457584007913129639936",
    ] {
        assert!(parse(input).is_err(), "unexpectedly accepted {input:?}");
    }
    assert!(parse(&" ".repeat(4097)).is_err());
}

#[test]
fn constant_folding_preserves_full_width_wrapping_and_evm_results() {
    let max = U256::MAX;
    let high_bit = U256::from(1) << 255;
    let cases = [
        (format!("(+ {max} 1)"), U256::ZERO),
        ("(- 0 1)".to_owned(), max),
        (format!("(* {max} 2)"), max - U256::from(1)),
        (format!("(and {max} 255)"), U256::from(255)),
        ("(or 256 255)".to_owned(), U256::from(511)),
        (format!("(xor {max} 255)"), max ^ U256::from(255)),
        ("(not 0)".to_owned(), max),
        (format!("(shl1 {high_bit})"), U256::ZERO),
        ("(+ (* 7 9) (- 3 2))".to_owned(), U256::from(64)),
        // A rewrite exposes a constant even though the input depends on x.
        ("(not (- x x))".to_owned(), max),
    ];
    for (text, expected) in cases {
        let original = parse(&text).unwrap();
        let candidate = optimize(&original);
        assert_eq!(candidate.to_string(), expected.to_string(), "{text}");
        let baseline = Program::compile(&original).unwrap();
        let optimized = Program::compile(&candidate).unwrap();
        assert!(
            (optimized.body_gas, optimized.runtime_bytes)
                <= (baseline.body_gas, baseline.runtime_bytes),
            "{text}"
        );
        cross_check(&original, &candidate, &baseline, &optimized).unwrap();
    }
}

#[test]
fn all_rules_and_composed_constants_preserve_compiled_score_and_outputs() {
    let mut inputs = Vec::new();
    for &(_, left, right) in RULES {
        let left = parse(&left.replace('?', "")).unwrap();
        let right = parse(&right.replace('?', "")).unwrap();
        cross_check(
            &left,
            &right,
            &Program::compile(&left).unwrap(),
            &Program::compile(&right).unwrap(),
        )
        .unwrap();
        inputs.push(left.to_string());
    }
    inputs.extend([
        "(+ x (- (+ 255 1) 256))".to_owned(),
        "(* (+ 2 3) x)".to_owned(),
        "(- (* (+ x 1) (+ x 1)) (* y y))".to_owned(),
    ]);
    for text in inputs {
        let original = parse(&text).unwrap();
        let candidate = optimize(&original);
        assert!(parse(&candidate.to_string()).is_ok(), "{text}");
        let baseline = Program::compile(&original).unwrap();
        let optimized = Program::compile(&candidate).unwrap();
        assert!(
            (optimized.body_gas, optimized.runtime_bytes)
                <= (baseline.body_gas, baseline.runtime_bytes),
            "{text} -> {candidate}"
        );
        cross_check(&original, &candidate, &baseline, &optimized).unwrap();
    }
    for (text, expected) in [
        ("(+ x (- (+ 255 1) 256))", "x"),
        ("(- (* x (+ y 1)) (* x y))", "x"),
    ] {
        assert_eq!(optimize(&parse(text).unwrap()).to_string(), expected);
    }
    for (text, expected_gas) in [
        ("(+ (xor x y) (shl1 (and x y)))", 14),
        ("(- (* x x) (* y y))", 30),
    ] {
        let candidate = optimize(&parse(text).unwrap());
        assert_eq!(Program::compile(&candidate).unwrap().body_gas, expected_gas);
    }
}

#[test]
fn optimizer_keeps_the_incumbent_when_sibling_reuse_beats_tree_extraction() {
    for (text, expected_score) in [
        ("(+ x x)", (11, 10)),
        ("(- (* x x) (* y y))", (30, 16)),
        ("(+ (shl1 x) (shl1 x))", (17, 13)),
    ] {
        let original = parse(text).unwrap();
        let candidate = optimize(&original);
        assert_eq!(candidate.to_string(), original.to_string());
        let baseline = Program::compile(&original).unwrap();
        let optimized = Program::compile(&candidate).unwrap();
        assert_eq!(
            (optimized.body_gas, optimized.runtime_bytes),
            expected_score
        );
        cross_check(&original, &candidate, &baseline, &optimized).unwrap();
    }
}
