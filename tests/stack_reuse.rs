use egg::{Id, RecExpr};
use evm_golf::{
    evm::{Program, cross_check},
    expr::{Expr, parse},
    proof,
};
use revm::primitives::U256;
use std::fs;
use tempfile::tempdir;

#[test]
fn repeated_operands_use_dup1_only_when_it_improves_the_score() {
    for (text, bytes, gas) in [
        ("(+ x x)", "5f358001", 11),
        ("(+ y y)", "6020358001", 12),
        ("(- x x)", "5f358003", 11),
        ("(* x x)", "5f358002", 13),
        ("(and x x)", "5f358016", 11),
        ("(or x x)", "5f358017", 11),
        ("(xor x x)", "5f358018", 11),
        ("(+ 0 0)", "5f5f01", 7),
        ("(+ 1 1)", "60018001", 9),
        ("(+ 255 255)", "60ff8001", 9),
        ("(+ 256 256)", "6101008001", 9),
        ("(+ x y)", "6020355f3501", 14),
        ("(+ 255 256)", "61010060ff01", 9),
        ("(+ x (not x))", "5f35195f3501", 16),
    ] {
        // Compile the parsed expression directly so constant folding cannot hide reuse.
        let expr = parse(text).unwrap();
        let program = Program::compile(&expr).unwrap();
        assert_eq!(program.body_hex, bytes, "{text}");
        assert_eq!(program.body_gas, gas, "{text}");
        assert_eq!(program.runtime_bytes, bytes.len() / 2 + 6, "{text}");
        assert_eq!(cross_check(&expr, &expr, &program, &program).unwrap(), 128);
    }
    let text = format!("(+ {} {})", U256::MAX, U256::MAX);
    let expr = parse(&text).unwrap();
    let program = Program::compile(&expr).unwrap();
    assert_eq!(program.body_hex, format!("7f{}8001", "ff".repeat(32)));
    assert_eq!((program.body_gas, program.runtime_bytes), (9, 41));
    cross_check(&expr, &expr, &program, &program).unwrap();
}

#[test]
fn structural_comparison_handles_distinct_node_ids_without_semantic_shortcuts() {
    let expr = RecExpr::from(vec![
        Expr::Var("x".into()),
        Expr::Var("x".into()),
        Expr::Add([Id::from(0), Id::from(1)]),
    ]);
    assert_ne!(Id::from(0), Id::from(1));
    assert_eq!(Program::compile(&expr).unwrap().body_hex, "5f358001");

    // These subtrees are equivalent, but their syntax differs. Reuse must not apply.
    let expr = parse("(+ (+ x y) (+ y x))").unwrap();
    let program = Program::compile(&expr).unwrap();
    assert!(!program.body().contains(&0x80));
    assert_eq!((program.body_gas, program.runtime_bytes), (31, 19));
    cross_check(&expr, &expr, &program, &program).unwrap();
}

#[test]
fn nested_reuse_preserves_operand_order_and_wrapping_shifts() {
    for (text, bytes, gas) in [
        ("(- x (+ y y))", "60203580015f3503", 20),
        ("(- (+ y y) x)", "5f35602035800103", 20),
        ("(shl1 (+ x x))", "5f35800160011b", 17),
        ("(+ (shl1 x) (shl1 x))", "5f3560011b8001", 17),
        (
            "(* (+ (+ x y) (+ x y)) (+ (+ x y) (+ x y)))",
            "6020355f350180018002",
            28,
        ),
    ] {
        let expr = parse(text).unwrap();
        let program = Program::compile(&expr).unwrap();
        assert_eq!(program.body_hex, bytes, "{text}");
        assert_eq!(program.body_gas, gas, "{text}");
        assert_eq!(program.runtime_bytes, bytes.len() / 2 + 6, "{text}");
        cross_check(&expr, &expr, &program, &program).unwrap();
    }
    let forward = Program::compile(&parse("(- x (+ y y))").unwrap()).unwrap();
    let reverse = Program::compile(&parse("(- (+ y y) x)").unwrap()).unwrap();
    assert_eq!(
        forward.execute(U256::from(2), U256::from(7)).unwrap().0,
        U256::MAX - U256::from(11)
    );
    assert_eq!(
        reverse.execute(U256::from(2), U256::from(7)).unwrap().0,
        U256::from(12)
    );
    for text in ["(shl1 (+ x x))", "(+ (shl1 x) (shl1 x))"] {
        let program = Program::compile(&parse(text).unwrap()).unwrap();
        assert_eq!(
            program.execute(U256::from(1) << 254, U256::ZERO).unwrap().0,
            U256::ZERO
        );
    }
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn lean_certifies_reused_bodies_by_definitional_reduction() {
    let dir = tempdir().unwrap();
    let mut texts = vec![
        "(+ x x)".to_owned(),
        "(+ y y)".to_owned(),
        "(- x (+ y y))".to_owned(),
        "(- (+ y y) x)".to_owned(),
        "(shl1 (+ x x))".to_owned(),
        "(+ (shl1 x) (shl1 x))".to_owned(),
        "(* (+ (+ x y) (+ x y)) (+ (+ x y) (+ x y)))".to_owned(),
    ];
    for word in [
        U256::ZERO,
        U256::from(1),
        U256::from(255),
        U256::from(256),
        U256::MAX,
    ] {
        texts.push(format!("(+ {word} {word})"));
    }
    for (index, text) in texts.iter().enumerate() {
        let expr = parse(text).unwrap();
        let program = Program::compile(&expr).unwrap();
        let source = proof::candidate(&expr, &expr, &program, &program);
        assert!(source.contains("some ["));
        assert!(source.contains(" := by\n  rfl"));
        let path = dir.path().join(format!("Reuse{index}.lean"));
        fs::write(&path, source).unwrap();
        proof::verify(&path).unwrap();
    }
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn lean_rejects_wrong_reused_bytes_with_the_expression_claim_unchanged() {
    let dir = tempdir().unwrap();
    let expr = parse("(+ x x)").unwrap();
    let program = Program::compile(&expr).unwrap();
    let source = proof::candidate(&expr, &expr, &program, &program);
    let split = source.find("theorem candidate_correct").unwrap();
    let correct = "Golf.run 5 [95, 53, 128, 1]";
    assert!(source[split..].contains(correct));
    for (name, wrong) in [
        ("WrongOpcode", "Golf.run 5 [95, 53, 128, 3]"),
        ("WrongVariable", "Golf.run 6 [96, 32, 53, 128, 1]"),
        ("MissingDup", "Golf.run 4 [95, 53, 1]"),
    ] {
        let mutated = format!(
            "{}{}",
            &source[..split],
            source[split..].replacen(correct, wrong, 1)
        );
        assert_eq!(&mutated[..split], &source[..split]);
        let path = dir.path().join(format!("{name}.lean"));
        fs::write(&path, mutated).unwrap();
        assert!(
            proof::verify(&path)
                .unwrap_err()
                .to_string()
                .contains("Lean rejected")
        );
        let log = fs::read_to_string(path.with_extension("log")).unwrap();
        assert!(log.contains("error:"));
        assert!(log.contains("'baseline_correct' depends on axioms:"));
    }
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn model_dup1_checks_underflow_and_preserves_the_existing_tail() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("DupSemantics.lean");
    let source = format!(
        "{}\n{}",
        include_str!("../lean/Model.lean"),
        r#"
theorem expression_equivalent (x y : Golf.Word) : Golf.run 2 [128] [] x y = none := by rfl
theorem baseline_correct (x y : Golf.Word) : Golf.run 2 [128] [x, y] x y = some [x, x, y] := by rfl
theorem candidate_correct (x y sentinel : Golf.Word) :
    Golf.run 10 [96, 32, 53, 95, 53, 1, 128, 1, 128, 2] [sentinel] x y =
      some [((x + y) + (x + y)) * ((x + y) + (x + y)), sentinel] := by rfl
#print axioms expression_equivalent
#print axioms baseline_correct
#print axioms candidate_correct
"#
    );
    fs::write(&path, source).unwrap();
    proof::verify(&path).unwrap();
}
