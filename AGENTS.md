# EVM Golf agent guide

EVM Golf makes deployed contracts cheaper to run. You propose exact byte patches;
the checker accepts a patch only if Lean proves it locally and your transactions
replay with identical results and no more gas. Read docs/cli.md for the formats.

## Optimize a project

1. `cargo run --release --locked -- optimize project.json --out runs/opt-1` applies the
   built-in rewrites and discovery until nothing changes. Start from its
   `baseline/project.json` to avoid redoing that work. Failed built-in and
   discovered batches are split; individual rejected patches are skipped.
2. `cargo run --release --locked -- inspect project.json > proposals.json` prints
   discovered patches. They are unverified suggestions.
3. Edit or write your own `proposals.json`: per contract, `original_keccak256`
   from inspect plus `sites` of `{original_pc, before, after}` hex byte windows.
   `before` and `after` have equal length; keep offsets fixed by widening PUSH
   immediates. Supported window opcodes: PUSH, DUP, SWAP, POP, ADD, MUL, SUB, SHL,
   AND, OR, XOR and NOT.
4. `cargo run --release --locked -- verify project.json --proposals proposals.json --out runs/check-1`.
   Every site of a contract must pass, or that contract is rejected unchanged.
   Accepted results are in `result.json`; continue from `baseline/project.json`.

Read `summary.txt` for accepted changes, gas savings, verification status and limits.
The contract-wide proof is separate from local proofs and replay.
Use a new `--out` directory every time. Failed runs keep diagnostics
(`failure.log`, `Rewrites.log`) but no accepted candidate.

## Rules

- Never weaken generated Lean or the checker to get a patch through. Use an
  upstream timeout override only at the user's explicit request; record it in
  the proof evidence. A timeout or failed proof is still a rejection.
- Gas is measured per supplied transaction; improve the fixtures you were given,
  do not weaken them.
- Results cover the supplied transactions only, not whole-contract equivalence.
- Keep runs, corpora and reports out of the repository.

## Develop the tool

Read docs/dev/README.md. After behavioral changes run `cargo fmt --check`,
`cargo clippy --locked --all-targets -- -D warnings`, `cargo test --locked` and
`cargo test --locked -- --ignored --test-threads=1`. Keep the README short and
update it after capability or CLI changes. Do not claim full EVM verification.
