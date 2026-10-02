//! Pure wrapping 256-bit expressions and bounded equality saturation.

use anyhow::{Context, Result, bail, ensure};
use egg::{
    Analysis, CostFunction, DidMerge, EGraph, Extractor, Id, Language, RecExpr, Rewrite, Runner,
    Symbol, define_language,
};
use revm::primitives::U256;
use std::time::Duration;

use crate::evm::Program;

// This is a small-puzzle prototype. These caps bound expression expansion and
// search resources; reaching a cap limits optimization, not proof validity.
const MAX_INPUT_BYTES: usize = 4096;
const MAX_NODES: usize = 128;
const SEARCH_NODES: usize = 10_000;
const SEARCH_ITERATIONS: usize = 30;
const SEARCH_SECONDS: u64 = 2;

define_language! {
    pub enum Expr {
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "and" = And([Id; 2]),
        "or" = Or([Id; 2]),
        "xor" = Xor([Id; 2]),
        "not" = Not(Id),
        "shl1" = Shl1(Id),
        Num(U256),
        Var(Symbol),
    }
}

/// Rules are shared by Rust search and the generated Lean theorem suite.
pub const RULES: &[(&str, &str, &str)] = &[
    ("add-zero", "(+ ?x 0)", "?x"),
    ("sub-zero", "(- ?x 0)", "?x"),
    ("sub-self", "(- ?x ?x)", "0"),
    ("mul-zero", "(* ?x 0)", "0"),
    ("mul-one", "(* ?x 1)", "?x"),
    ("add-commute", "(+ ?x ?y)", "(+ ?y ?x)"),
    ("mul-commute", "(* ?x ?y)", "(* ?y ?x)"),
    ("and-commute", "(and ?x ?y)", "(and ?y ?x)"),
    ("or-commute", "(or ?x ?y)", "(or ?y ?x)"),
    ("xor-commute", "(xor ?x ?y)", "(xor ?y ?x)"),
    ("double-add", "(+ ?x ?x)", "(shl1 ?x)"),
    ("double-mul", "(* ?x 2)", "(shl1 ?x)"),
    ("shift-add", "(shl1 ?x)", "(+ ?x ?x)"),
    ("nested-shift", "(shl1 (shl1 ?x))", "(* ?x 4)"),
    ("add-sub-cancel", "(- (+ ?x ?y) ?y)", "?x"),
    ("sub-add-cancel", "(- ?x (+ ?x ?y))", "(- 0 ?y)"),
    ("and-zero", "(and ?x 0)", "0"),
    ("and-self", "(and ?x ?x)", "?x"),
    ("or-zero", "(or ?x 0)", "?x"),
    ("or-self", "(or ?x ?x)", "?x"),
    ("xor-zero", "(xor ?x 0)", "?x"),
    ("xor-self", "(xor ?x ?x)", "0"),
    ("xor-cancel", "(xor (xor ?x ?y) ?y)", "?x"),
    ("not-not", "(not (not ?x))", "?x"),
    ("mask-partition", "(or (and ?x ?y) (and ?x (not ?y)))", "?x"),
    ("demorgan", "(or (not ?x) (not ?y))", "(not (and ?x ?y))"),
    (
        "carry-add",
        "(+ (xor ?x ?y) (shl1 (and ?x ?y)))",
        "(+ ?x ?y)",
    ),
    ("mul-cancel", "(- (* ?x (+ ?y 1)) (* ?x ?y))", "?x"),
    (
        "difference-squares",
        "(- (* ?x ?x) (* ?y ?y))",
        "(* (- ?x ?y) (+ ?x ?y))",
    ),
];

/// Constants discovered by either evaluation or rewriting remain available to
/// parents, without discarding cheaper equivalent nodes from their e-classes.
#[derive(Default)]
struct ConstantFold;

impl Analysis<Expr> for ConstantFold {
    type Data = Option<U256>;

    fn make(egraph: &mut EGraph<Expr, Self>, node: &Expr, _id: Id) -> Self::Data {
        constant_value(node, |id| egraph[id].data)
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        egg::merge_option(to, from, |a, b| {
            assert_eq!(*a, b, "equivalent e-class contains conflicting constants");
            DidMerge(false, false)
        })
    }

    fn modify(egraph: &mut EGraph<Expr, Self>, id: Id) {
        if let Some(value) = egraph[id].data {
            let constant = egraph.add(Expr::Num(value));
            egraph.union(id, constant);
        }
    }
}

/// Body gas/bytes including identical-sibling DUP1; exact compilation remains the final guard.
#[derive(Default)]
struct EvmCost;

impl CostFunction<Expr> for EvmCost {
    type Cost = (u64, usize);

    fn cost<C>(&mut self, enode: &Expr, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let own = match enode {
            Expr::Num(n) if n.is_zero() => (2, 1),
            Expr::Num(n) => (3, 1 + n.byte_len()),
            Expr::Var(name) if name.as_str() == "x" => (5, 2),
            Expr::Var(_) => (6, 3),
            Expr::Mul(_) => (5, 1),
            Expr::Shl1(_) => (6, 3),
            _ => (3, 1),
        };
        if let [a, b] = enode.children()
            && a == b
        {
            // One e-class is reconstructed as the same selected expression at
            // both occurrences, matching the compiler's structural DUP1 test.
            let child = costs(*a);
            let second = child.min((3, 1));
            return (own.0 + child.0 + second.0, own.1 + child.1 + second.1);
        }
        enode.children().iter().fold(own, |(gas, size), &id| {
            let child = costs(id);
            (gas + child.0, size + child.1)
        })
    }
}

pub fn parse(input: &str) -> Result<RecExpr<Expr>> {
    ensure!(
        input.len() <= MAX_INPUT_BYTES,
        "expression exceeds {MAX_INPUT_BYTES} bytes"
    );
    let expr = input
        .parse::<RecExpr<Expr>>()
        .context("invalid expression")?;
    ensure!(!expr.as_ref().is_empty(), "expression is empty");
    ensure!(
        expr.as_ref().len() <= MAX_NODES,
        "expression exceeds {MAX_NODES} nodes"
    );
    for node in expr.as_ref() {
        if let Expr::Var(name) = node
            && !matches!(name.as_str(), "x" | "y")
        {
            bail!("unsupported symbol {name:?}; use x, y, or unsigned 256-bit constants");
        }
    }
    Ok(expr)
}

pub fn optimize(expr: &RecExpr<Expr>) -> RecExpr<Expr> {
    let rules = RULES
        .iter()
        .map(|&(name, left, right)| {
            Rewrite::new(
                name,
                left.parse::<egg::Pattern<Expr>>().unwrap(),
                right.parse::<egg::Pattern<Expr>>().unwrap(),
            )
            .unwrap()
        })
        .collect::<Vec<_>>();
    let runner = Runner::<Expr, ConstantFold, ()>::default()
        .with_node_limit(SEARCH_NODES)
        .with_iter_limit(SEARCH_ITERATIONS)
        .with_time_limit(Duration::from_secs(SEARCH_SECONDS))
        .with_expr(expr)
        .run(&rules);
    let candidate = Extractor::new(&runner.egraph, EvmCost)
        .find_best(runner.roots[0])
        .1;
    // Preserve the accepted input as an incumbent: extraction must remain valid
    // for the public parser and cannot worsen the actual emitted contest score.
    if parse(&candidate.to_string()).is_err() {
        return expr.clone();
    }
    match (Program::compile(expr), Program::compile(&candidate)) {
        (Ok(baseline), Ok(optimized))
            if (optimized.body_gas, optimized.runtime_bytes)
                <= (baseline.body_gas, baseline.runtime_bytes) =>
        {
            candidate
        }
        _ => expr.clone(),
    }
}

pub fn evaluate(expr: &RecExpr<Expr>, x: U256, y: U256) -> U256 {
    let mut values = Vec::<U256>::with_capacity(expr.as_ref().len());
    for node in expr.as_ref() {
        let value = if let Expr::Var(name) = node {
            if name.as_str() == "x" { x } else { y }
        } else {
            constant_value(node, |id| Some(values[usize::from(id)])).unwrap()
        };
        values.push(value);
    }
    *values.last().unwrap()
}

// Share canonical U256 operations between concrete evaluation and e-graph
// folding, including wrapping overflow, operand order, and discarded shift bits.
fn constant_value(node: &Expr, get: impl Fn(Id) -> Option<U256>) -> Option<U256> {
    Some(match *node {
        Expr::Num(value) => value,
        Expr::Var(_) => return None,
        Expr::Add([a, b]) => get(a)?.wrapping_add(get(b)?),
        Expr::Sub([a, b]) => get(a)?.wrapping_sub(get(b)?),
        Expr::Mul([a, b]) => get(a)?.wrapping_mul(get(b)?),
        Expr::And([a, b]) => get(a)? & get(b)?,
        Expr::Or([a, b]) => get(a)? | get(b)?,
        Expr::Xor([a, b]) => get(a)? ^ get(b)?,
        Expr::Not(a) => !get(a)?,
        Expr::Shl1(a) => get(a)? << 1,
    })
}

pub fn lean(expr: &RecExpr<Expr>) -> String {
    let mut values = Vec::<String>::with_capacity(expr.as_ref().len());
    for node in expr.as_ref() {
        let get = |id: Id| &values[usize::from(id)];
        let value = match *node {
            Expr::Num(n) => format!("({n} : Golf.Word)"),
            Expr::Var(name) => name.to_string(),
            Expr::Not(a) => format!("(~~~{})", get(a)),
            Expr::Shl1(a) => format!("({} <<< 1)", get(a)),
            _ => {
                let op = match node {
                    Expr::Add(_) => "+",
                    Expr::Sub(_) => "-",
                    Expr::Mul(_) => "*",
                    Expr::And(_) => "&&&",
                    Expr::Or(_) => "|||",
                    Expr::Xor(_) => "^^^",
                    _ => unreachable!(),
                };
                let args = node.children();
                format!("({} {op} {})", get(args[0]), get(args[1]))
            }
        };
        values.push(value);
    }
    values.pop().unwrap()
}

#[cfg(test)]
mod tests {
    use super::{EvmCost, Expr, parse};
    use crate::evm::Program;
    use egg::{Extractor, Runner, rewrite};

    #[test]
    fn extraction_estimate_matches_compiled_sibling_reuse() {
        // Disable constant analysis so PUSH0/PUSHn duplicates reach extraction.
        let rules = [rewrite!("add-zero"; "(+ ?x 0)" => "?x")];
        for text in [
            "(+ x x)",
            "(* y y)",
            "(* 0 0)",
            "(* 1 1)",
            "(* 256 256)",
            "(- x y)",
            "(+ x (+ x 0))",
        ] {
            let expression = parse(text).unwrap();
            let runner = Runner::<Expr, (), ()>::default()
                .with_expr(&expression)
                .run(&rules);
            let (estimate, candidate) =
                Extractor::new(&runner.egraph, EvmCost).find_best(runner.roots[0]);
            let program = Program::compile(&candidate).unwrap();
            assert_eq!(
                estimate,
                (program.body_gas, program.body().len()),
                "{text} -> {candidate}"
            );
        }
    }
}
