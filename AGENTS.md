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
7. Collect candidate inputs in local `submissions/<unique-id>/submission.json`
   directories. Generate the leaderboard with the trusted checker; do not commit
   entries, scores, generated proofs, or logs to the source repository.

Use a new output directory for every attempt. Author and directory labels use
1–64 ASCII letters, digits, hyphens or underscores. Author labels are attribution,
not authenticated identities. Never put credentials in submissions.

## Fair comparisons

The current ruleset is `evm-golf-cancun`. Score is expression-body gas, then
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

## Runtime bytecode

Read docs/runtime.md before using runtime commands. `optimize-runtime` checks
local stack proofs and supplied transaction tests; `--preserve-layout` supports
dynamic jumps without moving byte offsets and binds local proofs to the complete
output artifact in Lean. Use `--scenarios` for explicit deployed-account state.
`--proposal` accepts a hash-bound local PUSH/DUP/ADD/AND/POP/SHL/SUB byte pair with generated Lean
proofs and guarded scenario replay. Use `--proposals` to verify up to 32 disjoint
pairs against one original image as an all-or-nothing batch; read docs/runtime.md
for the bounds. This is
separate from expression leaderboard submissions.
`check-runtime` instead compares arbitrary proposed runtimes using account fixtures and has no Lean proof gate.
Neither establishes whole-contract equivalence or produces expression leaderboard
entries. `certify-runtime-region` separately checks a supported internal prefix
against pinned upstream semantics; read docs/regions.md for its explicit premises
and excluded jump/suffix behavior. Keep runtime input corpora and generated results local too.

## Batch experiments

A coordinator can collect proposal JSON objects into an array and use
`cargo run --locked -- campaign --proposals <array.json> --out runs/campaign-1`.
This records individual unverified attempts and continues to later proposals.
Only verified entries reach the board. The command does not launch model agents.

Keep exploratory scripts, benchmark runs, agent transcripts, and research reports
outside this repository. Publish product changes only when explicitly requested.

## Develop the tool

Update the README after major capability or CLI changes; keep it short.

Keep the existing CLI commands compatible. Run `cargo fmt --check`,
`cargo clippy --locked --all-targets -- -D warnings`, `cargo test --locked`,
and `cargo test --locked -- --ignored` after behavioral changes.

This tool is unreleased; keep the development ruleset identifier stable.
Reverify entries after checker or compiler changes before regenerating the board.
Keep all proofs within the documented model; do not claim full EVM verification
or an advantage over Z3/cvc5 without evidence.
