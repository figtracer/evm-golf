# EVM Golf agent guide

This is an experimental competition for cheaper 256-bit EVM expressions.
Read docs/cli.md for the grammar and docs/verification.md for the proof boundary
before participating. See docs/dev/README.md for repository ownership and checks.

## Solve a puzzle

1. Run `cargo run --locked -- challenges` and select a fixed challenge ID.
2. Read its reference expression and description in `challenges.json`.
3. Propose an equivalent expression using the supported grammar.
4. Try `cargo run --locked -- optimize '<reference>' --out runs/search-1`
   for an e-graph baseline. Reasoning beyond the built-in rules is welcome.
5. Submit with `cargo run --locked -- submit <id> '<candidate>' --author <name> --out runs/entry-1`.
6. Inspect `Proof.log` and `result.json`. A failed proof or timeout does not count.
7. For a contribution, add only `submissions/<unique-id>/submission.json`.
   The maintainer regenerates proofs and scores from the trusted checker.

Use a new output directory for every attempt. Author and directory labels use
1–64 ASCII letters, digits, hyphens or underscores. Author labels are attribution,
not authenticated identities. Never put credentials in submissions.

## Fair comparisons

The current ruleset is `evm-golf-v2-cancun`. Score is expression-body gas, then
runtime bytes; exact ties share rank. You may submit a correct result that does
not improve the baseline, but it will rank below cheaper ones.

Do not change puzzle references, checker code, cost accounting, or proof policy
to improve your submission. Propose checker or challenge changes separately.
Do not submit raw Lean source or arbitrary executable code: this first version
accepts expression strings and generates the proof statements itself.

To recreate the board:
`cargo run --locked -- leaderboard --submissions submissions --out runs/board-1`.
Every submission is reverified; saved result.json scores are ignored. One failed
submission prevents generation of the final board. Failure artifacts remain for
diagnosis. The command reads immediate child directories with submission.json.

## Batch experiments

A coordinator can collect proposal JSON objects into an array and use
`cargo run --locked -- campaign --proposals <array.json> --out runs/campaign-1`.
This records individual unverified attempts and continues to later proposals.
Only verified entries reach the board. The command does not launch model agents.

Keep exploratory scripts, benchmark runs, agent transcripts, and research reports
outside this repository. Publish product changes only when explicitly requested.

## Develop the tool

Keep the existing CLI commands compatible. Run `cargo fmt --check`,
`cargo clippy --locked --all-targets -- -D warnings`, `cargo test --locked`,
and `cargo test --locked -- --ignored` after behavioral changes.

Bump RULESET in src/contest.rs for changes to puzzle semantics, compiler,
scoring, or proof policy. Reverify entries before regenerating leaderboard/.
Keep all proofs within the documented model; do not claim full EVM verification
or an advantage over Z3/cvc5 without evidence.
