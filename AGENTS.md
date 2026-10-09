# EVM Golf agent guide

EVM Golf makes deployed contracts cheaper to run. You propose exact byte patches;
the checker accepts a patch only if Lean proves it locally and your transactions
replay with identical results and no more gas. Read docs/cli.md for the formats.

## Optimize a project

1. `cargo run --locked -- optimize project.json --out runs/opt-1` applies the
   built-in rewrites and discovery until nothing changes. Start from its
   `baseline/project.json` to avoid redoing that work.
2. `cargo run --locked -- inspect project.json > proposals.json` prints
   discovered patches. They are unverified suggestions.
3. Edit or write your own `proposals.json`: per contract, `original_keccak256`
   from inspect plus `sites` of `{original_pc, before, after}` hex byte windows.
   `before` and `after` have equal length; keep offsets fixed by widening PUSH
   immediates. Supported window opcodes: PUSH, DUP, SWAP, POP, ADD, SUB, SHL,
   AND, OR, XOR and NOT.
4. `cargo run --locked -- verify project.json --proposals proposals.json --out runs/check-1`.
   Every site of a contract must pass, or that contract is rejected unchanged.
   Accepted results are in `result.json`; continue from `baseline/project.json`.

Use a new `--out` directory every time. Failed runs keep diagnostics
(`failure.log`, `Rewrites.log`) but no accepted candidate.

## Rules

- Never edit generated Lean, the checker, or proof limits to get a patch through.
  A timeout or failed proof is a rejection.
- Gas is measured per supplied transaction; improve the fixtures you were given,
  do not weaken them.
- Results cover the supplied transactions only, not whole-contract equivalence.
- Keep runs, corpora and reports out of the repository.

## Develop the tool

Read docs/dev/README.md. After behavioral changes run `cargo fmt --check`,
`cargo clippy --locked --all-targets -- -D warnings`, `cargo test --locked` and
`cargo test --locked -- --ignored --test-threads=1`. Keep the README short and
update it after capability or CLI changes. Do not claim full EVM verification.
