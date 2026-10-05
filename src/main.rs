use anyhow::{Context as _, Result, bail};
use clap::{Parser, Subcommand};
use evm_golf::runtime::{self, project};
use std::{fs, path::PathBuf};

/// Optimize deployed EVM contracts with Lean-checked rewrites and replay of
/// your transactions. See README.md for the workflow.
#[derive(Parser)]
#[command(version, about)]
struct Cli {
    #[command(subcommand)]
    command: Action,
}

#[derive(Subcommand)]
enum Action {
    /// Print discovered, unverified patches for each contract as proposals JSON.
    Inspect {
        /// project.json listing contracts and their transaction fixtures.
        project: PathBuf,
        /// Only these contract IDs (repeatable; default: all).
        #[arg(long)]
        contract: Vec<String>,
    },
    /// Search for verified savings per contract and write the results to --out.
    Optimize {
        project: PathBuf,
        #[arg(long)]
        contract: Vec<String>,
        /// Maximum rounds of built-in rewrites plus discovery.
        #[arg(long, default_value_t = 8)]
        rounds: usize,
        /// New output directory.
        #[arg(long)]
        out: PathBuf,
    },
    /// Check exact patches (proposals JSON); every patch for a contract must pass.
    Verify {
        project: PathBuf,
        #[arg(long)]
        proposals: PathBuf,
        /// New output directory.
        #[arg(long)]
        out: PathBuf,
    },
    #[command(hide = true)]
    /// Compare arbitrary Cancun runtimes on supplied account/transaction fixtures.
    /// This is concrete replay, not a Lean or whole-contract equivalence proof.
    CheckRuntime {
        #[arg(long)]
        original: PathBuf,
        #[arg(long)]
        candidate: PathBuf,
        #[arg(long)]
        scenarios: PathBuf,
        #[arg(long)]
        out: PathBuf,
    },
    #[command(hide = true)]
    /// Prove whole-program refinement of a runtime pair against pinned upstream
    /// EVM semantics. Supported opcode profile only; no calls or creation.
    CertifyRuntimeWhole {
        #[arg(long)]
        original: PathBuf,
        #[arg(long)]
        candidate: PathBuf,
        #[arg(long)]
        out: PathBuf,
    },
    #[command(hide = true)]
    /// Certify a supported internal region with pinned upstream EVM semantics.
    /// Supports arithmetic, bitwise and memory spans; not whole-contract equivalence.
    CertifyRuntimeRegion {
        #[arg(long)]
        original: PathBuf,
        #[arg(long)]
        candidate: PathBuf,
        #[arg(long)]
        entry_pc: usize,
        /// Execute the region's trailing JUMP with checked destination proofs.
        #[arg(long)]
        through_jump: bool,
        /// Execute the explicit STOP, RETURN or REVERT at --exit-pc.
        #[arg(long, requires = "exit_pc", conflicts_with = "through_jump")]
        through_halt: bool,
        /// Prove fresh canonical call entry through the selected terminal instruction.
        #[arg(long, requires = "through_halt")]
        from_call_entry: bool,
        /// Exclusive span end; terminal modes execute the instruction at this PC.
        #[arg(long)]
        exit_pc: Option<usize>,
        #[arg(long)]
        out: PathBuf,
    },
}

fn main() -> Result<()> {
    match Cli::parse().command {
        Action::Inspect { project, contract } => {
            let contracts = project::load(&project, &contract)?;
            let proposals = project::inspect(&contracts)?;
            for entry in &proposals.contracts {
                eprintln!("{}: {} unverified sites", entry.id, entry.sites.len());
            }
            println!("{}", serde_json::to_string_pretty(&proposals)?);
        }
        Action::Optimize {
            project,
            contract,
            rounds,
            out,
        } => {
            if rounds == 0 {
                bail!("--rounds must be positive");
            }
            let contracts = project::load(&project, &contract)?;
            prepare_parent(&out)?;
            report(project::optimize(&contracts, rounds, &out)?, &out)?;
        }
        Action::Verify {
            project,
            proposals,
            out,
        } => {
            let proposals: project::Proposals =
                serde_json::from_str(&runtime::input::read_json(&proposals)?)
                    .context("invalid proposals JSON")?;
            let ids: Vec<String> = proposals.contracts.iter().map(|c| c.id.clone()).collect();
            let contracts = project::load(&project, &ids)?;
            prepare_parent(&out)?;
            report(project::verify(&contracts, &proposals, &out)?, &out)?;
        }
        Action::CheckRuntime {
            original,
            candidate,
            scenarios,
            out,
        } => {
            let original = runtime::input::read_bytecode(&original)?;
            let candidate = runtime::input::read_bytecode(&candidate)?;
            let scenarios: Vec<runtime::scenario::Scenario> =
                serde_json::from_str(&runtime::input::read_json(&scenarios)?)?;
            prepare_parent(&out)?;
            runtime::scenario::check(&original, &candidate, &scenarios, &out)?;
            println!(
                "Supplied scenarios passed concrete replay. No whole-contract equivalence proof.\nEvidence: {}",
                out.display()
            );
        }
        Action::CertifyRuntimeWhole {
            original,
            candidate,
            out,
        } => {
            let original = runtime::input::read_bytecode(&original)?;
            let candidate = runtime::input::read_bytecode(&candidate)?;
            prepare_parent(&out)?;
            let report = runtime::whole::certify(&original, &candidate, &out)?;
            println!(
                "Whole-program refinement proved for {} instructions ({} power, {} threading sites); Ξ and X level, supported opcode profile, conditioned on original success or revert.\nEvidence: {}",
                report.covered_instructions,
                report.power_sites.len(),
                report.thread_sites.len(),
                out.display()
            );
        }
        Action::CertifyRuntimeRegion {
            original,
            candidate,
            entry_pc,
            exit_pc,
            through_jump,
            through_halt,
            from_call_entry,
            out,
        } => {
            let original = runtime::input::read_bytecode(&original)?;
            let candidate = runtime::input::read_bytecode(&candidate)?;
            if !through_jump && !through_halt {
                prepare_parent(&out)?;
            }
            let (exit_pc, boundary) = if through_halt {
                let exit = exit_pc.context("--through-halt requires --exit-pc")?;
                let report = if from_call_entry {
                    runtime::region::certify_selected_span_from_call_entry(
                        &original, &candidate, entry_pc, exit, &out,
                    )?
                } else {
                    runtime::region::certify_selected_span_through_halt(
                        &original, &candidate, entry_pc, exit, &out,
                    )?
                };
                (
                    report.span.exit_pc,
                    if report.terminal == "REVERT" {
                        "Proves paired canonical revert, equal output and related remaining gas; rollback is excluded"
                    } else if from_call_entry {
                        "Proves paired canonical call-entry success and equal output; transaction validation is excluded"
                    } else {
                        "Executes STOP or RETURN with paired success and equal canonical output"
                    },
                )
            } else if let (Some(jump_pc), true) = (exit_pc, through_jump) {
                let report = runtime::region::certify_selected_span_through_jump(
                    &original, &candidate, entry_pc, jump_pc, &out,
                )?;
                (
                    match report {
                        runtime::region::SelectedSpanJumpCertificate::Pure(report) => {
                            report.span.exit_pc
                        }
                        runtime::region::SelectedSpanJumpCertificate::Memory(report) => {
                            report.span.exit_pc
                        }
                    },
                    "Stops before executing the destination JUMPDEST",
                )
            } else if through_jump {
                let report =
                    runtime::region::certify_through_jump(&original, &candidate, entry_pc, &out)?;
                (
                    report.exit_pc,
                    "Stops before executing the destination JUMPDEST",
                )
            } else if let Some(exit_pc) = exit_pc {
                runtime::region::certify_selected_span(
                    &original, &candidate, entry_pc, exit_pc, &out,
                )?;
                (exit_pc, "Stops at the selected exit PC")
            } else {
                let report =
                    runtime::region::certify_selected(&original, &candidate, entry_pc, &out)?;
                match report {
                    runtime::region::SelectedRegionCertificate::Power(report) => {
                        (report.exit_pc, "Stops before JUMP")
                    }
                    runtime::region::SelectedRegionCertificate::Mask(report) => {
                        (report.exit_pc, "Stops after the mask replacement")
                    }
                }
            };
            println!(
                "Region {entry_pc}..{exit_pc} certified under stated stack, gas and state conditions. {boundary}; no whole-contract equivalence proof.\nEvidence: {}",
                out.display()
            );
        }
    }
    Ok(())
}

fn report(result: project::ProjectResult, out: &std::path::Path) -> Result<()> {
    for contract in &result.contracts {
        if contract.accepted {
            eprintln!(
                "{}: {} -> {} gas over {} transactions ({} rewrites)",
                contract.id,
                contract.baseline_gas,
                contract.candidate_gas,
                contract.transactions,
                contract.rewrites
            );
        } else {
            eprintln!(
                "{}: rejected: {}",
                contract.id,
                contract.error.as_deref().unwrap_or("")
            );
        }
    }
    eprintln!(
        "{}\nResults: {}\nNext baseline: {}",
        result.scope,
        out.join("result.json").display(),
        out.join("baseline/project.json").display()
    );
    println!("{}", serde_json::to_string_pretty(&result)?);
    if result.contracts.iter().any(|c| !c.accepted) {
        bail!("some contracts were rejected");
    }
    Ok(())
}

fn prepare_parent(path: &std::path::Path) -> Result<()> {
    if let Some(parent) = path.parent()
        && !parent.as_os_str().is_empty()
    {
        fs::create_dir_all(parent)?;
    }
    Ok(())
}
