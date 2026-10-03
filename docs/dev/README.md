# Developer documentation

## Repository layout

| Path | Responsibility |
| --- | --- |
| `src/expr.rs` | Grammar, wrapping evaluation, rewrite rules, cost-guided search |
| `src/evm.rs` | Bytecode generation, revm execution, gas checks |
| `src/proof.rs` | Lean source generation and pinned-toolchain verification |
| `src/runtime.rs` | Runtime CFG, local rewriting, relocation, and differential execution |
| `src/runtime/` | Fixed-layout certificates, layout analysis, bounded inputs, account fixtures, precompile replay guards |
| `src/contest.rs` | Fixed puzzles, submissions, ranking |
| `src/campaign.rs` | Batch attempts, failure evidence, optimizer comparisons |
| `src/main.rs` | CLI arguments and output |
| `lean/Model.lean` | The limited bytecode semantics used by the proofs |
| `lean/Stack.lean` | Operational instruction-boundary stack limits for local fragments |
| `lean/Composition.lean` | Decoded boundaries, fuel and contextual substitution in the bounded model |
| `lean/Layout.lean` | Exact fixed-layout artifact reconstruction and local proof binding |
| `tests/` | Execution, CLI, proof, and campaign regression tests |
| `challenges.json` | Puzzle IDs, descriptions, and reference expressions |
| `scripts/` | Toolchain setup and repository checks |

This is a single Cargo package. The library exposes the optimizer, checker,
contest, and campaign modules used by the CLI.

## Building and testing

Follow the [setup guide](../getting-started.md), then run:

```sh
cargo build --locked
bash scripts/check.sh
```

The check script runs formatting, Clippy, the normal tests, and the tests that
require Lean. GitHub Actions runs the same script with pinned Rust and Lean on
Ubuntu, including the proof suite. The individual commands are:

```sh
cargo fmt --check
cargo clippy --locked --all-targets -- -D warnings
cargo test --locked
cargo test --locked -- --ignored
```

The normal suite covers expression validation, arithmetic boundaries, gas and
bytecode execution, and submission schemas. The Lean suite covers valid proofs,
false equivalences, incorrect bytecode, overwrite refusal, rule verification,
score recomputation, ranking, and campaigns containing failed proposals. Runtime
certificate regressions reject altered untouched bytes, overlapping or missing
sites, replacements inside PUSH data, and mismatched local proofs.

Do not treat a normal `cargo test` run as validation of the Lean path. Those
integration tests are explicitly ignored until requested with `--ignored`.

## Compatibility

Keep existing CLI arguments and persisted submission formats compatible.
Preserve accepted evidence when generating new output: use a fresh directory,
then review the regenerated leaderboard. Entries and generated results are not
checked in; `submissions/`, `leaderboard/`, and `runs/` are ignored local directories.

While the tool is unreleased, keep the development ruleset identifier stable.
Reverify entries after changes to the compiler, scoring, or proof policy; do not
compare saved scores produced by different checker revisions.

## Research

Useful extensions include general stack scheduling, realistic compiler fragments, and
agent-written proof lemmas. The current checker does not accept custom proof
programs and does not benchmark Z3 or cvc5.

For solver comparisons, preserve the exact rule, word width, preconditions,
versions, invocation, resource limits, and observed result. Use the same statement
for every method and distinguish proof-generation time from checking time.
Keep counterexamples, timeouts, unknown results, and verified proofs separate.

Keep exploratory scripts, benchmark artifacts, and research reports outside
this repository. Publish product changes only when explicitly requested.
