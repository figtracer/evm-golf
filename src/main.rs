use anyhow::Result;
use clap::{Parser, Subcommand};
use evm_golf::{
    Report, campaign, check,
    contest::{self, RULESET, Submission},
    expr::RULES,
    optimize, proof, runtime,
};
use std::{fs, path::PathBuf};

#[derive(Parser)]
#[command(version, about)]
struct Cli {
    #[command(subcommand)]
    command: Action,
}

#[derive(Subcommand)]
enum Action {
    /// Analyze supported Cancun runtime control flow.
    AnalyzeRuntime {
        #[arg(long)]
        bytecode: PathBuf,
        /// Analyze fixed-layout rewrites without resolving dynamic jumps.
        #[arg(long)]
        preserve_layout: bool,
    },
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
    /// Certify a supported internal region with pinned upstream EVM semantics.
    /// Ends before JUMP; does not prove whole-contract equivalence.
    CertifyRuntimeRegion {
        #[arg(long)]
        original: PathBuf,
        #[arg(long)]
        candidate: PathBuf,
        #[arg(long)]
        entry_pc: usize,
        #[arg(long)]
        out: PathBuf,
    },
    /// Optimize runtime bytecode with local Lean proofs and supplied execution cases.
    OptimizeRuntime {
        #[arg(long)]
        bytecode: PathBuf,
        #[arg(
            long,
            required_unless_present_any = ["sequences", "scenarios"],
            conflicts_with_all = ["sequences", "scenarios"]
        )]
        cases: Option<PathBuf>,
        /// JSON transaction sequences with persistent state between calls.
        #[arg(long, required_unless_present_any = ["cases", "scenarios"], conflicts_with_all = ["cases", "scenarios"])]
        sequences: Option<PathBuf>,
        /// JSON account fixtures and transaction sequences, including initialized state.
        #[arg(long, required_unless_present_any = ["cases", "sequences"], conflicts_with_all = ["cases", "sequences"])]
        scenarios: Option<PathBuf>,
        /// Preserve byte offsets and allow dynamic jumps, PC and CODESIZE.
        #[arg(long)]
        preserve_layout: bool,
        #[arg(long)]
        out: PathBuf,
    },
    /// Verify a batch of proposals, rank accepted entries, and compare e-graph search.
    Campaign {
        #[arg(long)]
        proposals: PathBuf,
        #[arg(long)]
        out: PathBuf,
    },
    /// List fixed puzzle specifications as JSON.
    Challenges,
    /// Verify a candidate against a fixed puzzle and save a submission.
    Submit {
        challenge: String,
        candidate: String,
        #[arg(long)]
        author: String,
        #[arg(long)]
        out: PathBuf,
    },
    /// Reverify all submission directories and generate Markdown + JSON rankings.
    Leaderboard {
        #[arg(long, default_value = "submissions")]
        submissions: PathBuf,
        #[arg(long)]
        out: PathBuf,
    },
    /// Find a cheaper equivalent expression, then verify it.
    Optimize {
        expression: String,
        /// New directory for proof, checker log, and accepted result.
        #[arg(long)]
        out: PathBuf,
    },
    /// Verify a human- or agent-proposed candidate against a reference.
    Check {
        original: String,
        candidate: String,
        #[arg(long)]
        out: PathBuf,
    },
    /// Prove every e-graph rewrite rule at the full 256-bit width.
    Rules {
        #[arg(long)]
        out: PathBuf,
    },
    /// Run five puzzles and save a local score table.
    Demo {
        #[arg(long, default_value = "runs/demo")]
        out: PathBuf,
    },
}

fn main() -> Result<()> {
    match Cli::parse().command {
        Action::AnalyzeRuntime {
            bytecode,
            preserve_layout,
        } => {
            let code = runtime::input::read_bytecode(&bytecode)?;
            let analysis = if preserve_layout {
                serde_json::to_string_pretty(&runtime::analyze_layout(&code)?)?
            } else {
                serde_json::to_string_pretty(&runtime::analyze(&code)?)?
            };
            println!("{analysis}");
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
        Action::CertifyRuntimeRegion {
            original,
            candidate,
            entry_pc,
            out,
        } => {
            let original = runtime::input::read_bytecode(&original)?;
            let candidate = runtime::input::read_bytecode(&candidate)?;
            prepare_parent(&out)?;
            let report = runtime::region::certify(&original, &candidate, entry_pc, &out)?;
            println!(
                "Region {}..{} certified under stated stack, gas and state conditions. Stops before JUMP; no whole-contract equivalence proof.\nEvidence: {}",
                report.entry_pc,
                report.exit_pc,
                out.display()
            );
        }
        Action::OptimizeRuntime {
            bytecode,
            cases,
            sequences,
            scenarios,
            preserve_layout,
            out,
        } => {
            let code = runtime::input::read_bytecode(&bytecode)?;
            prepare_parent(&out)?;
            let mode = if preserve_layout {
                runtime::RuntimeMode::PreserveLayout
            } else {
                runtime::RuntimeMode::Compact
            };
            let report = if let Some(cases) = cases {
                let cases: Vec<runtime::Case> =
                    serde_json::from_str(&runtime::input::read_json(&cases)?)?;
                runtime::optimize_with(&code, runtime::ExecutionInputs::Cases(&cases), &out, mode)?
            } else if let Some(sequences) = sequences {
                let sequences: Vec<runtime::Sequence> =
                    serde_json::from_str(&runtime::input::read_json(&sequences)?)?;
                runtime::optimize_with(
                    &code,
                    runtime::ExecutionInputs::Sequences(&sequences),
                    &out,
                    mode,
                )?
            } else {
                let scenarios: Vec<runtime::scenario::Scenario> = serde_json::from_str(
                    &runtime::input::read_json(&scenarios.expect("clap requires one input"))?,
                )?;
                runtime::optimize_scenarios(&code, &scenarios, &out, mode)?
            };
            println!(
                "Runtime bytes: {} → {}; {} local rewrites; {} execution cases passed.\n{}\nEvidence: {}",
                report.baseline_bytes,
                report.candidate_bytes,
                report.rewrites.len(),
                report.cases.len(),
                report.verification,
                out.display()
            );
        }
        Action::Campaign { proposals, out } => {
            prepare_parent(&out)?;
            eprintln!(
                "Progress will be saved to {}",
                out.join("campaign.json").display()
            );
            let result = campaign::run(&proposals, &out)?;
            println!(
                "Campaign complete: {} verified, {} unverified. Report: {}",
                result.verified,
                result.unverified,
                out.join("README.md").display()
            );
        }
        Action::Challenges => {
            println!("{}", serde_json::to_string_pretty(&contest::challenges()?)?)
        }
        Action::Submit {
            challenge,
            candidate,
            author,
            out,
        } => {
            prepare_parent(&out)?;
            let submission = Submission {
                ruleset: RULESET.to_owned(),
                challenge,
                candidate,
                author,
            };
            print_report(&contest::submit(&submission, &out)?);
            println!("Submission: {}", out.display());
        }
        Action::Leaderboard { submissions, out } => {
            prepare_parent(&out)?;
            let entries = contest::leaderboard(&submissions, &out)?;
            println!(
                "Reverified {} submissions. Leaderboard: {}",
                entries.len(),
                out.join("README.md").display()
            );
        }
        Action::Optimize { expression, out } => {
            prepare_parent(&out)?;
            print_report(&optimize(&expression, &out)?);
            println!("Evidence: {}", out.display());
        }
        Action::Check {
            original,
            candidate,
            out,
        } => {
            prepare_parent(&out)?;
            print_report(&check(&original, &candidate, &out)?);
            println!("Evidence: {}", out.display());
        }
        Action::Rules { out } => {
            prepare_parent(&out)?;
            fs::create_dir(&out)?;
            let path = out.join("Rules.lean");
            fs::write(&path, proof::rules()?)?;
            proof::verify(&path)?;
            println!(
                "Verified all {} rewrite rules over 256-bit words.\nEvidence: {}",
                RULES.len(),
                out.display()
            );
        }
        Action::Demo { out } => {
            prepare_parent(&out)?;
            fs::create_dir(&out)?;
            let mut reports = Vec::new();
            for (name, expression) in [
                ("double", "(* x 2)"),
                ("xor-cancel", "(xor (xor x y) y)"),
                ("mask-partition", "(or (and x y) (and x (not y)))"),
                ("demorgan", "(or (not x) (not y))"),
                ("combined", "(+ (* x 2) (- y y))"),
            ] {
                println!("\n{name}");
                let report = optimize(expression, &out.join(name))?;
                print_report(&report);
                reports.push((name, report));
            }
            fs::write(
                out.join("scores.json"),
                serde_json::to_string_pretty(&reports)? + "\n",
            )?;
            println!("\nAll five puzzles verified. Evidence: {}", out.display());
        }
    }
    Ok(())
}

fn print_report(report: &Report) {
    println!("  {} → {}", report.original, report.candidate);
    println!(
        "  Body gas: {} → {} (saved {}); runtime bytes: {} → {}",
        report.baseline.body_gas,
        report.optimized.body_gas,
        report.gas_saved,
        report.baseline.runtime_bytes,
        report.optimized.runtime_bytes
    );
    println!(
        "  Lean verified; revm checked {} input pairs.",
        report.concrete_cases
    );
}

fn prepare_parent(path: &std::path::Path) -> Result<()> {
    if let Some(parent) = path.parent()
        && !parent.as_os_str().is_empty()
    {
        fs::create_dir_all(parent)?;
    }
    Ok(())
}
