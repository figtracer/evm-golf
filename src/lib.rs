//! A bounded e-graph search and independent checker for small EVM expressions.

pub mod campaign;
pub mod contest;
pub mod evm;
pub mod expr;
pub mod proof;

use anyhow::{Result, ensure};
use serde::Serialize;
use std::{fs, path::Path};

use crate::{evm::Program, expr::parse};

/// Evidence written only after Lean verification and concrete revm checks pass.
#[derive(Debug, Serialize)]
pub struct Report {
    pub original: String,
    pub candidate: String,
    pub evm_version: &'static str,
    pub baseline: Program,
    pub optimized: Program,
    pub gas_saved: i64,
    pub lean_version: String,
    pub verification: &'static str,
    pub concrete_cases: usize,
}

/// Check a proposed expression and preserve the proof, checker log and measured result.
pub fn check(original: &str, candidate: &str, out: &Path) -> Result<Report> {
    let original = parse(original)?;
    let candidate = parse(candidate)?;
    let baseline = Program::compile(&original)?;
    let optimized = Program::compile(&candidate)?;
    fs::create_dir(out)?;
    let source = proof::candidate(&original, &candidate, &baseline, &optimized);
    fs::write(out.join("Proof.lean"), &source)?;
    let lean_version = proof::verify(&out.join("Proof.lean"))?;
    let concrete_cases = evm::cross_check(&original, &candidate, &baseline, &optimized)?;
    let report = Report {
        original: original.to_string(),
        candidate: candidate.to_string(),
        evm_version: "Cancun",
        gas_saved: baseline.body_gas as i64 - optimized.body_gas as i64,
        baseline,
        optimized,
        lean_version,
        verification: "Lean: expression equality and both bytecode bodies match the reference; revm: concrete cross-check",
        concrete_cases,
    };
    fs::write(
        out.join("result.json"),
        serde_json::to_string_pretty(&report)? + "\n",
    )?;
    Ok(report)
}

/// Optimize using the bounded search, then independently check the selected candidate.
pub fn optimize(original: &str, out: &Path) -> Result<Report> {
    let expression = parse(original)?;
    let candidate = expr::optimize(&expression);
    ensure!(
        Program::compile(&candidate)?.body_gas <= Program::compile(&expression)?.body_gas,
        "extraction increased gas cost"
    );
    check(original, &candidate.to_string(), out)
}
