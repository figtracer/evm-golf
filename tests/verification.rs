use evm_golf::{evm::Program, expr::parse, proof};
use std::{fs, process::Command};
use tempfile::tempdir;

#[test]
#[ignore = "requires Lean 4.34.0; run cargo test --test verification -- --ignored"]
fn cli_accepts_verified_result_and_refuses_false_claim() {
    let dir = tempdir().unwrap();
    let accepted = dir.path().join("accepted");
    let success = Command::new(env!("CARGO_BIN_EXE_evm-golf"))
        .args(["optimize", "(* x 2)", "--out"])
        .arg(&accepted)
        .output()
        .unwrap();
    assert!(
        success.status.success(),
        "{}",
        String::from_utf8_lossy(&success.stderr)
    );
    let result: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(accepted.join("result.json")).unwrap()).unwrap();
    assert_eq!(result["candidate"], "(+ x x)");
    assert_eq!(result["optimized"]["runtime_bytes"], 10);
    assert_eq!(result["gas_saved"], 2);
    assert_eq!(result["concrete_cases"], 128);

    let rejected = dir.path().join("rejected");
    let failure = Command::new(env!("CARGO_BIN_EXE_evm-golf"))
        .args(["check", "(+ x 1)", "x", "--out"])
        .arg(&rejected)
        .output()
        .unwrap();
    assert!(!failure.status.success());
    assert!(String::from_utf8_lossy(&failure.stderr).contains("Lean rejected"));
    assert!(!rejected.join("result.json").exists());

    let existing = Command::new(env!("CARGO_BIN_EXE_evm-golf"))
        .args(["check", "x", "x", "--out"])
        .arg(&accepted)
        .output()
        .unwrap();
    assert!(!existing.status.success());
    let unchanged: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(accepted.join("result.json")).unwrap()).unwrap();
    assert_eq!(result, unchanged);
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn proof_rejects_mismatched_expressions_and_bytecode() {
    let dir = tempdir().unwrap();
    let original = parse("(- x y)").unwrap();
    let correct = Program::compile(&original).unwrap();
    let different = parse("(+ x y)").unwrap();
    let wrong = Program::compile(&different).unwrap();
    for (name, expression, baseline, candidate) in [
        ("WrongCandidate", &original, &correct, &wrong),
        ("WrongBaseline", &original, &wrong, &correct),
        ("WrongExpression", &different, &correct, &correct),
    ] {
        let path = dir.path().join(format!("{name}.lean"));
        fs::write(
            &path,
            proof::candidate(&original, expression, baseline, candidate),
        )
        .unwrap();
        let error = proof::verify(&path).unwrap_err().to_string();
        assert!(error.contains("Lean rejected"), "{error}");
    }
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn cli_accepts_reverse_expansion_with_reused_expression_proof() {
    let dir = tempdir().unwrap();
    let out = dir.path().join("expanded");
    let result = Command::new(env!("CARGO_BIN_EXE_evm-golf"))
        .args(["check", "x", "(+ (* x 1) 0)", "--out"])
        .arg(&out)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let report: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(out.join("result.json")).unwrap()).unwrap();
    assert_eq!(report["candidate"], "(+ (* x 1) 0)");
    assert_eq!(report["gas_saved"], -13);
    assert_eq!(report["concrete_cases"], 128);
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn bytecode_composition_preserves_unsimplified_expression_shapes() {
    let dir = tempdir().unwrap();
    for (index, (left, right)) in [
        ("(+ x x)", "(* x 2)"),
        ("0", "(xor x x)"),
        ("x", "(xor (xor x y) y)"),
        ("(- 0 x)", "(+ (- 0 x) 0)"),
    ]
    .into_iter()
    .enumerate()
    {
        evm_golf::check(left, right, &dir.path().join(index.to_string())).unwrap();
    }
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn all_rewrite_rules_have_full_width_proofs() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("Rules.lean");
    fs::write(&path, proof::rules().unwrap()).unwrap();
    proof::verify(&path).unwrap();
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn model_handles_general_arithmetic_and_push32() {
    let dir = tempdir().unwrap();
    let expression = parse("(+ (* x y) (- (not y) 115792089237316195423570985008687907853269984665640564039457584007913129639935))").unwrap();
    let program = Program::compile(&expression).unwrap();
    let path = dir.path().join("Arithmetic.lean");
    fs::write(
        &path,
        proof::candidate(&expression, &expression, &program, &program),
    )
    .unwrap();
    proof::verify(&path).unwrap();
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn portfolio_certifies_polynomials_and_preserves_bitwise_fallback() {
    let dir = tempdir().unwrap();
    for (index, (left, right)) in [
        ("(+ (* x y) (* x x))", "(* x (+ y x))"),
        ("(- (* x (+ y 1)) (* x y))", "x"),
        ("(- (* x x) (* y y))", "(* (- x y) (+ x y))"),
        (
            "(- (* (+ x y) (+ x y)) (+ (* x x) (* y y)))",
            "(* 2 (* x y))",
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let out = dir.path().join(index.to_string());
        evm_golf::check(left, right, &out).unwrap();
        let source = fs::read_to_string(out.join("Proof.lean")).unwrap();
        assert!(source.starts_with("-- Verification strategy: algebra."));
        assert!(
            !fs::read_to_string(out.join("Proof.log"))
                .unwrap()
                .contains("_native")
        );
    }
    let out = dir.path().join("carry");
    evm_golf::check("(+ (xor x y) (shl1 (and x y)))", "(+ x y)", &out).unwrap();
    assert!(out.join("Proof.algebra.log").exists());
    assert!(out.join("Proof.bitvector.log").exists());
    assert!(
        fs::read_to_string(out.join("Proof.lean"))
            .unwrap()
            .starts_with("-- Verification strategy: bitvector.")
    );
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn verification_rejects_missing_reports_and_custom_axioms() {
    let dir = tempdir().unwrap();
    let expression = parse("x").unwrap();
    let program = Program::compile(&expression).unwrap();
    let source = proof::candidate(&expression, &expression, &program, &program);
    let path = dir.path().join("Missing.lean");
    fs::write(
        &path,
        source.replace("#print axioms baseline_correct\n", ""),
    )
    .unwrap();
    assert!(
        proof::verify(&path)
            .unwrap_err()
            .to_string()
            .contains("missing theorem axiom reports")
    );
    let path = dir.path().join("Custom.lean");
    fs::write(&path, "import Std\naxiom injected : False\ntheorem expression_equivalent : True := False.elim injected\ntheorem baseline_correct : True := by trivial\ntheorem candidate_correct : True := by trivial\n#print axioms expression_equivalent\n#print axioms baseline_correct\n#print axioms candidate_correct\n").unwrap();
    assert!(
        proof::verify(&path)
            .unwrap_err()
            .to_string()
            .contains("unexpected axiom dependency: injected")
    );
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn shift_normalization_certifies_polynomials_and_rejects_false_variant() {
    let dir = tempdir().unwrap();
    let original = "(- (* (+ x 1) (+ x 1)) (* x x))";
    for (index, (left, right)) in [
        (original, "(+ (shl1 x) 1)"),
        ("(shl1 x)", "(* x 2)"),
        ("(* x 2)", "(shl1 x)"),
        (
            "(* (+ (shl1 y) (shl1 y)) (+ (shl1 y) (shl1 y)))",
            "(* (* y 4) (* y 4))",
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let out = dir.path().join(index.to_string());
        evm_golf::check(left, right, &out).unwrap();
        assert!(
            fs::read_to_string(out.join("Proof.lean"))
                .unwrap()
                .starts_with("-- Verification strategy: algebra.")
        );
        assert!(
            !fs::read_to_string(out.join("Proof.log"))
                .unwrap()
                .contains("_native")
        );
    }
    let out = dir.path().join("false-shift");
    let error = evm_golf::check("(shl1 (shl1 x))", "(* x 3)", &out)
        .unwrap_err()
        .to_string();
    assert!(error.contains("Lean rejected"));
    assert!(!out.join("result.json").exists());
    assert!(
        error.len() < 1024,
        "proof diagnostics should remain in logs"
    );
    assert!(fs::read_to_string(out.join("Proof.log")).unwrap().len() > error.len());
}
