//! Replay a bounded batch of proposals and preserve success and failure evidence.

use anyhow::{Context, Result, ensure};
use serde::Serialize;
use std::{fs, path::Path};

use crate::{
    Report,
    contest::{self, RULESET, Submission},
    optimize,
};

// Enough for several agents to submit one or more rounds on seven puzzles,
// while keeping local proof batches bounded. No model calls are made here.
const MAX_PROPOSALS: usize = 64;
const MAX_PROPOSAL_FILE_BYTES: u64 = 1024 * 1024;

#[derive(Serialize)]
pub struct Attempt {
    pub id: String,
    pub submission: Submission,
    pub result: Option<Report>,
    pub error: Option<String>,
}

#[derive(Serialize)]
pub struct Campaign {
    pub ruleset: &'static str,
    pub attempted: usize,
    pub verified: usize,
    pub unverified: usize,
    pub attempts: Vec<Attempt>,
}

/// Continue past individual unverified proposals, but only rank accepted ones.
/// Operational failures also mean unverified, never a claim of inequivalence.
pub fn run(proposals: &Path, out: &Path) -> Result<Campaign> {
    ensure!(
        fs::metadata(proposals)?.len() <= MAX_PROPOSAL_FILE_BYTES,
        "proposal file exceeds 1 MiB"
    );
    let submissions: Vec<Submission> = serde_json::from_str(&fs::read_to_string(proposals)?)
        .context("expected a JSON array of submissions")?;
    ensure!(
        !submissions.is_empty() && submissions.len() <= MAX_PROPOSALS,
        "campaign requires 1–{MAX_PROPOSALS} proposals"
    );
    fs::create_dir(out)?;
    fs::create_dir(out.join("attempts"))?;
    fs::create_dir(out.join("accepted"))?;
    // Preserve exactly the parsed inputs used for this run, independent of edits
    // to the input file while the checker is running.
    fs::write(
        out.join("proposals.json"),
        serde_json::to_string_pretty(&submissions)? + "\n",
    )?;
    let mut attempts = Vec::new();
    for (index, submission) in submissions.into_iter().enumerate() {
        let id = format!("attempt-{:03}", index + 1);
        let evidence = out.join("attempts").join(&id);
        let (result, error) = match contest::submit(&submission, &evidence) {
            Ok(result) => {
                let accepted = out.join("accepted").join(&id);
                fs::create_dir(&accepted)?;
                fs::write(
                    accepted.join("submission.json"),
                    serde_json::to_string_pretty(&submission)? + "\n",
                )?;
                (Some(result), None)
            }
            Err(error) => (None, Some(format!("{error:#}"))),
        };
        attempts.push(Attempt {
            id,
            submission,
            result,
            error,
        });
    }
    let verified = attempts
        .iter()
        .filter(|attempt| attempt.result.is_some())
        .count();
    let campaign = Campaign {
        ruleset: RULESET,
        attempted: attempts.len(),
        verified,
        unverified: attempts.len() - verified,
        attempts,
    };
    fs::write(
        out.join("campaign.json"),
        serde_json::to_string_pretty(&campaign)? + "\n",
    )?;
    // Use the same standalone ranking path as maintainers. This deliberately
    // rechecks accepted inputs instead of trusting the campaign's saved scores.
    contest::leaderboard(&out.join("accepted"), &out.join("leaderboard"))?;
    fs::create_dir(out.join("egraph"))?;
    let mut markdown = format!(
        "# Campaign results\n\nRuleset: `{RULESET}`. {} proposals: {} verified, {} unverified.\n\n[Rankings and proofs](leaderboard/README.md) · [Machine-readable results](campaign.json) · [Replay inputs](proposals.json)\n\nUnverified includes invalid inputs, failed proofs, timeouts and operational failures.\nIt does not by itself establish inequivalence. Only verified candidates are ranked.\n\n## Best verified score per puzzle\n\nBody gas; ties are broken by runtime byte size. The baseline is the fixed\nreference expression compiled by this prototype, not optimized Solidity.\n\n| Puzzle | Reference gas | E-graph gas | Best proposal gas | Proposal bytes |\n| --- | ---: | ---: | ---: | ---: |\n",
        campaign.attempted, campaign.verified, campaign.unverified
    );
    for puzzle in contest::challenges()? {
        let egraph = optimize(&puzzle.reference, &out.join("egraph").join(&puzzle.id))?;
        let best = campaign
            .attempts
            .iter()
            .filter(|attempt| attempt.submission.challenge == puzzle.id)
            .filter_map(|attempt| attempt.result.as_ref())
            .min_by_key(|result| (result.optimized.body_gas, result.optimized.runtime_bytes));
        let (gas, bytes) = best
            .map(|result| {
                (
                    result.optimized.body_gas.to_string(),
                    result.optimized.runtime_bytes.to_string(),
                )
            })
            .unwrap_or_else(|| ("—".into(), "—".into()));
        markdown.push_str(&format!(
            "| [{}](egraph/{}/result.json) | {} | {} | {gas} | {bytes} |\n",
            puzzle.id, puzzle.id, egraph.baseline.body_gas, egraph.optimized.body_gas
        ));
    }
    markdown.push_str(
        "\n## Attempts\n\n| ID | Author | Puzzle | Outcome |\n| --- | --- | --- | --- |\n",
    );
    for attempt in &campaign.attempts {
        // Metadata in unverified proposals may contain arbitrary Markdown.
        let author = escape_cell(&attempt.submission.author);
        let challenge = escape_cell(&attempt.submission.challenge);
        let outcome = if attempt.result.is_some() {
            "verified"
        } else {
            "unverified (see campaign.json)"
        };
        markdown.push_str(&format!(
            "| {} | {author} | {challenge} | {outcome} |\n",
            attempt.id
        ));
    }
    fs::write(out.join("README.md"), markdown)?;
    Ok(campaign)
}

fn escape_cell(value: &str) -> String {
    value
        .replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('\\', "&#92;")
        .replace('|', "&#124;")
        .replace('`', "&#96;")
        .replace('[', "&#91;")
        .replace(']', "&#93;")
        .replace('*', "&#42;")
        .replace('_', "&#95;")
        .replace(['\n', '\r'], " ")
}
