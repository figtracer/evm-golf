//! Fixed puzzles and reproducible ranking from verified submission inputs.

use anyhow::{Context, Result, ensure};
use serde::{Deserialize, Serialize};
use std::{fs, path::Path};

use crate::{Report, check, evm::Program, expr::parse};

/// Development ruleset identifier; entries are always reverified by this checker.
pub const RULESET: &str = "evm-golf-cancun";

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Challenge {
    pub id: String,
    pub title: String,
    pub reference: String,
    pub description: String,
}

/// A submission contains no claimed score and cannot choose its reference.
#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Submission {
    pub ruleset: String,
    pub challenge: String,
    pub author: String,
    pub candidate: String,
}

#[derive(Serialize)]
pub struct Entry {
    pub id: String,
    pub submission: Submission,
    pub result: Report,
}

pub fn challenges() -> Result<Vec<Challenge>> {
    let puzzles: Vec<Challenge> = serde_json::from_str(include_str!("../challenges.json"))?;
    for (index, puzzle) in puzzles.iter().enumerate() {
        validate_label(&puzzle.id)?;
        parse(&puzzle.reference)?;
        ensure!(
            !puzzles[..index].iter().any(|other| other.id == puzzle.id),
            "duplicate challenge ID"
        );
    }
    Ok(puzzles)
}

pub fn submit(submission: &Submission, out: &Path) -> Result<Report> {
    ensure!(
        submission.ruleset == RULESET,
        "unsupported ruleset: {}",
        submission.ruleset
    );
    validate_label(&submission.author)?;
    let challenge = challenges()?
        .into_iter()
        .find(|puzzle| puzzle.id == submission.challenge)
        .context("unknown challenge ID; run `evm-golf challenges`")?;
    let result = check(&challenge.reference, &submission.candidate, out)?;
    fs::write(
        out.join("submission.json"),
        serde_json::to_string_pretty(submission)? + "\n",
    )?;
    Ok(result)
}

/// Re-run the current verifier for every submission. Saved scores are ignored.
pub fn leaderboard(submissions: &Path, out: &Path) -> Result<Vec<Entry>> {
    fs::create_dir(out)?;
    let mut paths = fs::read_dir(submissions)?
        .map(|entry| entry.map(|entry| entry.path()))
        .collect::<std::io::Result<Vec<_>>>()?;
    paths.sort();
    let mut entries = Vec::new();
    for path in paths {
        if !path.is_dir() || !path.join("submission.json").is_file() {
            continue;
        }
        let id = path
            .file_name()
            .and_then(|name| name.to_str())
            .context("invalid submission directory name")?;
        validate_label(id)?;
        let submission: Submission =
            serde_json::from_str(&fs::read_to_string(path.join("submission.json"))?)
                .with_context(|| format!("invalid submission: {id}"))?;
        let result = submit(&submission, &out.join(id))
            .with_context(|| format!("submission {id} failed"))?;
        entries.push(Entry {
            id: id.to_owned(),
            submission,
            result,
        });
    }
    entries.sort_by(|a, b| {
        (
            &a.submission.challenge,
            a.result.optimized.body_gas,
            a.result.optimized.runtime_bytes,
            &a.id,
        )
            .cmp(&(
                &b.submission.challenge,
                b.result.optimized.body_gas,
                b.result.optimized.runtime_bytes,
                &b.id,
            ))
    });
    let mut markdown = format!(
        "# EVM Golf leaderboard\n\nRuleset: `{RULESET}`. Lower body gas wins; runtime bytes break ties.\nEvery row was freshly verified with Lean and cross-checked with revm.\nThese are synthetic expression puzzles, not comparisons against solc.\n\n"
    );
    for puzzle in challenges()? {
        let baseline = Program::compile(&parse(&puzzle.reference)?)?;
        markdown.push_str(&format!(
            "## {}\n\n`{}` — baseline: {} gas, {} runtime bytes.\n\n",
            puzzle.title, puzzle.id, baseline.body_gas, baseline.runtime_bytes
        ));
        let rows = entries
            .iter()
            .filter(|entry| entry.submission.challenge == puzzle.id)
            .collect::<Vec<_>>();
        if rows.is_empty() {
            markdown.push_str("No submissions yet.\n\n");
            continue;
        }
        markdown.push_str("| Rank | Author | Gas | Bytes | Saved gas | Candidate | Evidence |\n| ---: | --- | ---: | ---: | ---: | --- | --- |\n");
        let mut rank = 0;
        let mut previous = None;
        for (index, entry) in rows.iter().enumerate() {
            let score = (
                entry.result.optimized.body_gas,
                entry.result.optimized.runtime_bytes,
            );
            if previous != Some(score) {
                rank = index + 1;
            }
            previous = Some(score);
            markdown.push_str(&format!("| {rank} | {} | {} | {} | {} | `{}` | [proof]({}/Proof.lean) · [result]({}/result.json) |\n",
                entry.submission.author, score.0, score.1, entry.result.gas_saved,
                entry.result.candidate, entry.id, entry.id));
        }
        markdown.push('\n');
    }
    fs::write(
        out.join("leaderboard.json"),
        serde_json::to_string_pretty(&entries)? + "\n",
    )?;
    fs::write(out.join("README.md"), markdown.trim_end().to_owned() + "\n")?;
    Ok(entries)
}

fn validate_label(label: &str) -> Result<()> {
    // Short ASCII labels keep directory names and generated Markdown portable.
    ensure!(
        !label.is_empty()
            && label.len() <= 64
            && label
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_')),
        "labels must contain 1–64 ASCII letters, digits, hyphens or underscores"
    );
    Ok(())
}
