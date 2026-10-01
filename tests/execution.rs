use evm_golf::{
    evm::{Program, cross_check},
    expr::{evaluate, optimize, parse},
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
    assert_eq!((baseline.body_gas, optimized.body_gas), (31, 11));
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
