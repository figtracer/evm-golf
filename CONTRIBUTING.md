# Contributing

Contributions to EVM Golf are welcome. This includes optimizer improvements,
verification fixes, and new puzzles. Puzzle solutions belong in leaderboard
submissions, outside the source repository.

## Getting started

Read the [setup guide](docs/getting-started.md),
[repository layout](docs/dev/README.md), and
[verification model](docs/verification.md). Check existing
[issues](https://github.com/figtracer/evm-golf/issues) before starting a larger change.

For bug reports, include a minimal expression or proposal file, the command,
Rust and Lean versions, and the relevant checker output. For features, explain
the intended use and how it fits the supported execution model.

## Code changes

Keep changes focused and add regression coverage for new behavior. Run:

```sh
bash scripts/check.sh
```

Describe the concrete problem and resulting behavior in the pull request. Include
measurements for performance claims and explain changes to semantics, scoring,
or proof assumptions. Preserve existing command and submission contracts where
possible. See [compatibility](docs/dev/README.md#compatibility) for ruleset changes.

## Puzzle solutions

Keep puzzle entries and generated results out of pull requests. Verify a candidate
and generate a local leaderboard:

```sh
cargo run --locked -- submit double '(shl1 x)' --author your-name --out submissions/entry-1
cargo run --locked -- leaderboard --submissions submissions --out runs/board-1
```

Use a trusted checkout of the checker. It reads expression strings from each
`submission.json`, regenerates proofs and scores, and ignores saved scores.
Custom Lean programs and arbitrary bytecode are outside the submission format.
Author names are self-reported; all verified entries appear, including ties.
See [leaderboards](docs/cli.md#leaderboards) for the output format.

## AI assistance

Disclose AI assistance in pull requests and describe its extent. The initial
implementation was developed with OpenAI Codex. AI-generated candidates use the
same verification path as human-written candidates.

## Proof research

Rules that are difficult for existing solvers are useful contributions. Include
the exact statement and enough information to reproduce the solver result.
See the [research guidelines](docs/dev/README.md#research) for comparison criteria.

## License

By contributing, you agree that your contributions are licensed under the
repository's [MIT License](LICENSE).
