//! Generate matched expression-only proof obligations for a reviewed research corpus.
//!
//! Proof strings are trusted, manually reviewed tactics, not public submissions.
//! This example does not alter the production verifier. Separate bytecode files
//! transfer guided proofs into the existing small EVM model.

use anyhow::{Context, Result, anyhow, ensure};
use egg::{Id, RecExpr};
use evm_golf::{
    evm::{Program, cross_check},
    expr::{Expr, evaluate, lean, parse},
};
use revm::primitives::U256;
use serde::{Deserialize, Serialize};
use std::{collections::HashSet, env, fs, path::PathBuf};

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Case {
    id: String,
    left: String,
    right: String,
    valid: bool,
    proof: String,
}

#[derive(Serialize)]
struct ManifestEntry {
    #[serde(flatten)]
    case: Case,
    baseline: Program,
    candidate: Program,
    concrete_cases: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    witness: Option<Witness>,
}

#[derive(Serialize)]
struct Witness {
    x: String,
    y: String,
    left: String,
    right: String,
    baseline_output: String,
    candidate_output: String,
    baseline_gas: u64,
    candidate_gas: u64,
}

fn main() -> Result<()> {
    let mut args = env::args_os().skip(1);
    let first = args
        .next()
        .context("usage: proof_cases CASES_JSON OUTPUT_DIR SAT_TIMEOUT_SECONDS, or --replay CASES_JSON CASE_ID X Y")?;
    if first == "--replay" {
        let input = PathBuf::from(args.next().context("missing cases JSON path")?);
        let id = args
            .next()
            .context("missing case ID")?
            .into_string()
            .map_err(|_| anyhow!("case ID must be UTF-8"))?;
        let x = args
            .next()
            .context("missing decimal x")?
            .into_string()
            .map_err(|_| anyhow!("x must be UTF-8"))?;
        let y = args
            .next()
            .context("missing decimal y")?
            .into_string()
            .map_err(|_| anyhow!("y must be UTF-8"))?;
        ensure!(
            args.next().is_none(),
            "replay expects CASES_JSON CASE_ID X Y"
        );
        ensure!(
            !x.is_empty()
                && x.bytes().all(|byte| byte.is_ascii_digit())
                && !y.is_empty()
                && y.bytes().all(|byte| byte.is_ascii_digit()),
            "replay inputs must be unsigned decimal words"
        );
        let x = x.parse::<U256>().context("invalid 256-bit x")?;
        let y = y.parse::<U256>().context("invalid 256-bit y")?;
        let cases: Vec<Case> = serde_json::from_str(&fs::read_to_string(input)?)?;
        let mut matching = cases.iter().filter(|case| case.id == id);
        let case = matching.next().context("unknown case ID")?;
        ensure!(matching.next().is_none(), "duplicate case ID");
        let left = parse(&case.left)?;
        let right = parse(&case.right)?;
        let baseline = Program::compile(&left)?;
        let candidate = Program::compile(&right)?;
        let witness = replay_witness(&left, &right, &baseline, &candidate, x, y)?;
        println!("{}", serde_json::to_string_pretty(&witness)?);
        return Ok(());
    }
    let input = PathBuf::from(first);
    let out = PathBuf::from(
        args.next()
            .context("usage: proof_cases CASES_JSON OUTPUT_DIR SAT_TIMEOUT_SECONDS")?,
    );
    let sat_timeout = args.next().context("missing SAT timeout in seconds")?;
    let sat_timeout = sat_timeout
        .to_str()
        .context("invalid SAT timeout")?
        .parse::<u64>()?;
    ensure!(sat_timeout > 0, "SAT timeout must be positive");
    ensure!(args.next().is_none(), "expected exactly three arguments");
    let bv_decide = format!("bv_decide (config := {{ timeout := {sat_timeout} }})");
    let cases: Vec<Case> = serde_json::from_str(&fs::read_to_string(input)?)?;
    ensure!(!cases.is_empty(), "case list must not be empty");
    let mut ids = HashSet::new();
    for case in &cases {
        ensure!(
            !case.id.is_empty()
                && case
                    .id
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_')),
            "case IDs must be nonempty ASCII letters, digits, hyphens or underscores"
        );
        ensure!(ids.insert(&case.id), "duplicate case ID: {}", case.id);
        ensure!(!case.proof.trim().is_empty(), "empty proof for {}", case.id);
        parse(&case.left).with_context(|| format!("left expression for {}", case.id))?;
        parse(&case.right).with_context(|| format!("right expression for {}", case.id))?;
    }
    fs::create_dir(&out).context("output directory must be fresh and its parent must exist")?;
    let mut manifest = Vec::new();
    for case in cases {
        // Only the controls request bare bv_decide; structural proofs are preserved.
        let guided = if case.proof == "bv_decide" {
            &bv_decide
        } else {
            &case.proof
        };
        let left = parse(&case.left)?;
        let right = parse(&case.right)?;
        let baseline = Program::compile(&left)?;
        let candidate = Program::compile(&right)?;
        let (concrete_cases, witness) = if case.valid {
            (cross_check(&left, &right, &baseline, &candidate)?, None)
        } else {
            // The negative control is deliberately falsifiable at x = y = 1.
            (
                1,
                Some(replay_witness(
                    &left,
                    &right,
                    &baseline,
                    &candidate,
                    U256::from(1),
                    U256::from(1),
                )?),
            )
        };
        let smt = format!(
            "; Exact wrapping 256-bit equality; unsat proves the claim.\n(set-logic QF_BV)\n(declare-fun x () (_ BitVec 256))\n(declare-fun y () (_ BitVec 256))\n(assert (not (= {} {})))\n(check-sat)\n",
            smt_expression(&left),
            smt_expression(&right)
        );
        fs::write(out.join(format!("{}.smt2", case.id)), smt)?;
        fs::write(
            out.join(format!("{}.auto.lean", case.id)),
            lean_obligation(
                &left,
                &right,
                &format!("(try simp [BitVec.mul_comm]) <;> {bv_decide}"),
            ),
        )?;
        fs::write(
            out.join(format!("{}.guided.lean", case.id)),
            lean_obligation(&left, &right, guided),
        )?;
        fs::write(
            out.join(format!("{}.bytecode.lean", case.id)),
            bytecode_obligation(&left, &right, &baseline, &candidate, guided),
        )?;
        manifest.push(ManifestEntry {
            case,
            baseline,
            candidate,
            concrete_cases,
            witness,
        });
    }
    fs::write(
        out.join("manifest.json"),
        serde_json::to_string_pretty(&manifest)? + "\n",
    )?;
    println!(
        "Generated {} matched cases in {}",
        manifest.len(),
        out.display()
    );
    Ok(())
}

fn replay_witness(
    left: &RecExpr<Expr>,
    right: &RecExpr<Expr>,
    baseline: &Program,
    candidate: &Program,
    x: U256,
    y: U256,
) -> Result<Witness> {
    let left_value = evaluate(left, x, y);
    let right_value = evaluate(right, x, y);
    ensure!(
        left_value != right_value,
        "inputs do not witness inequality"
    );
    let (baseline_output, baseline_gas) = baseline.execute(x, y)?;
    let (candidate_output, candidate_gas) = candidate.execute(x, y)?;
    ensure!(
        baseline_output == left_value && candidate_output == right_value,
        "witness expression and EVM outputs disagree"
    );
    ensure!(
        baseline_gas == baseline.body_gas && candidate_gas == candidate.body_gas,
        "witness gas model disagrees with revm"
    );
    Ok(Witness {
        x: x.to_string(),
        y: y.to_string(),
        left: left_value.to_string(),
        right: right_value.to_string(),
        baseline_output: baseline_output.to_string(),
        candidate_output: candidate_output.to_string(),
        baseline_gas,
        candidate_gas,
    })
}

fn smt_expression(expression: &RecExpr<Expr>) -> String {
    let mut values = Vec::<String>::new();
    for node in expression.as_ref() {
        let get = |id: Id| &values[usize::from(id)];
        let value = match *node {
            Expr::Num(value) => format!("(_ bv{value} 256)"),
            Expr::Var(name) => name.to_string(),
            Expr::Not(child) => format!("(bvnot {})", get(child)),
            Expr::Shl1(child) => format!("(bvshl {} (_ bv1 256))", get(child)),
            Expr::Add([a, b]) => format!("(bvadd {} {})", get(a), get(b)),
            Expr::Sub([a, b]) => format!("(bvsub {} {})", get(a), get(b)),
            Expr::Mul([a, b]) => format!("(bvmul {} {})", get(a), get(b)),
            Expr::And([a, b]) => format!("(bvand {} {})", get(a), get(b)),
            Expr::Or([a, b]) => format!("(bvor {} {})", get(a), get(b)),
            Expr::Xor([a, b]) => format!("(bvxor {} {})", get(a), get(b)),
        };
        values.push(value);
    }
    values.pop().expect("expressions are validated by parse")
}

fn lean_obligation(left: &RecExpr<Expr>, right: &RecExpr<Expr>, tactic: &str) -> String {
    format!(
        "import Std\n\nnamespace Golf\nabbrev Word := BitVec 256\nend Golf\n\n{}\n#print axioms claim\n",
        lean_claim(left, right, tactic)
    )
}

fn bytecode_obligation(
    left: &RecExpr<Expr>,
    right: &RecExpr<Expr>,
    baseline: &Program,
    candidate: &Program,
    tactic: &str,
) -> String {
    let mut source = format!(
        "{}\n{}",
        include_str!("../lean/Model.lean"),
        lean_claim(left, right, tactic)
    );
    for (name, program) in [
        ("baseline_correct", baseline),
        ("candidate_correct", candidate),
    ] {
        let bytes = program
            .body()
            .iter()
            .map(u8::to_string)
            .collect::<Vec<_>>()
            .join(", ");
        let proof = if name == "baseline_correct" {
            "  rfl\n".to_owned()
        } else {
            format!(
                "  change some [{}] = some [{}]\n  rw [claim x y]\n",
                lean(right),
                lean(left)
            )
        };
        source.push_str(&format!(
            "\ntheorem {name} (x y : Golf.Word) : Golf.run {} [{bytes}] [] x y = some [{}] := by\n{proof}",
            program.body().len() + 1, lean(left)
        ));
    }
    source.push_str(
        "\n#print axioms claim\n#print axioms baseline_correct\n#print axioms candidate_correct\n",
    );
    source
}

fn lean_claim(left: &RecExpr<Expr>, right: &RecExpr<Expr>, tactic: &str) -> String {
    let tactic = tactic
        .lines()
        .map(|line| format!("  {line}\n"))
        .collect::<String>();
    format!(
        "-- External wall-clock limits govern both Lean lanes.\nset_option maxHeartbeats 0\nset_option maxRecDepth 4096\nset_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\n\ntheorem claim (x y : Golf.Word) : {} = {} := by\n{tactic}",
        lean(left),
        lean(right)
    )
}

#[cfg(test)]
mod tests {
    use super::{lean_obligation, replay_witness, smt_expression};
    use evm_golf::{
        evm::Program,
        expr::{evaluate, parse},
    };
    use revm::primitives::U256;

    #[test]
    fn subtraction_keeps_expression_operand_order() {
        let expression = parse("(- x y)").unwrap();
        assert_eq!(smt_expression(&expression), "(bvsub x y)");
        assert_eq!(evaluate(&expression, U256::ZERO, U256::from(1)), U256::MAX);
    }

    #[test]
    fn full_width_literal_and_addition_keep_wrapping_semantics() {
        let expression = parse(&format!("(+ {} 1)", U256::MAX)).unwrap();
        assert_eq!(
            smt_expression(&expression),
            format!("(bvadd (_ bv{} 256) (_ bv1 256))", U256::MAX)
        );
        assert_eq!(evaluate(&expression, U256::ZERO, U256::ZERO), U256::ZERO);
    }

    #[test]
    fn bitwise_and_shift_forms_use_bitvector_operators() {
        let expression = parse("(xor (and x (not y)) (or (shl1 y) 1))").unwrap();
        assert_eq!(
            smt_expression(&expression),
            "(bvxor (bvand x (bvnot y)) (bvor (bvshl y (_ bv1 256)) (_ bv1 256)))"
        );
    }

    #[test]
    fn both_lean_lanes_keep_the_same_fixed_theorem() {
        let left = parse("(+ x 0)").unwrap();
        let right = parse("x").unwrap();
        for tactic in ["simp", "bv_decide"] {
            let source = lean_obligation(&left, &right, tactic);
            assert!(
                source
                    .contains("theorem claim (x y : Golf.Word) : (x + (0 : Golf.Word)) = x := by")
            );
            assert!(source.contains("#print axioms claim"));
        }
    }

    #[test]
    fn replay_accepts_actual_counterexamples_and_rejects_equal_outputs() {
        let left = parse("(+ x y)").unwrap();
        let right = parse("x").unwrap();
        let baseline = Program::compile(&left).unwrap();
        let candidate = Program::compile(&right).unwrap();
        let witness = replay_witness(
            &left,
            &right,
            &baseline,
            &candidate,
            U256::from(1),
            U256::from(1),
        )
        .unwrap();
        assert_eq!(witness.left, "2");
        assert_eq!(witness.right, "1");
        assert_eq!(witness.baseline_output, "2");
        assert_eq!(witness.candidate_output, "1");
        assert!(
            replay_witness(
                &left,
                &right,
                &baseline,
                &candidate,
                U256::from(1),
                U256::ZERO
            )
            .is_err()
        );
    }
}
