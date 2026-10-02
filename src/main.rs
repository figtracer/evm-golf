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
    /// Analyze the supported static-control-flow Cancun runtime subset.
    AnalyzeRuntime {
        #[arg(long)]
        bytecode: PathBuf,
    },
    /// Optimize runtime bytecode with local Lean proofs and supplied execution cases.
    OptimizeRuntime {
        #[arg(long)]
        bytecode: PathBuf,
        #[arg(long)]
        cases: PathBuf,
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
        Action::AnalyzeRuntime { bytecode } => {
            let code = runtime::from_hex(&fs::read_to_string(bytecode)?)?;
            println!(
                "{}",
                serde_json::to_string_pretty(&runtime::analyze(&code)?)?
            );
        }
        Action::OptimizeRuntime {
            bytecode,
            cases,
            out,
        } => {
            let code = runtime::from_hex(&fs::read_to_string(bytecode)?)?;
            let cases: Vec<runtime::Case> = serde_json::from_str(&fs::read_to_string(cases)?)?;
            prepare_parent(&out)?;
            let report = runtime::optimize(&code, &cases, &out)?;
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
