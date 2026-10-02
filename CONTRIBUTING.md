# Contributing

Contributions to EVM Golf are welcome. This includes optimizer improvements,
verification fixes, new puzzles, and cheaper solutions to existing challenges.

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

Validate a candidate against a fixed challenge:

```sh
cargo run --locked -- submit double '(shl1 x)' --author your-name --out runs/entry-1
```

Add the resulting `submission.json` under `submissions/<unique-id>/` in a pull
request. Explain the replacement. The checker accepts expression strings; custom
Lean programs and arbitrary bytecode are outside the current submission format.

Contributors only need to supply the input JSON. Maintainers use a trusted checkout
of the checker, review and copy the new inputs, and regenerate the board:

```sh
cargo run --locked -- leaderboard --submissions submissions --out runs/board-1
```

Review the fresh output before updating `leaderboard/`. Saved score files are
ignored. Changes to the checker, puzzle definitions, toolchain, or dependencies
need separate review. Public submissions are not automatically executed by a
GitHub Actions workflow.

The board lists every verified submission, including ties and candidates worse
than the reference. Author names are self-reported. Entries labeled `reference`
are project examples.

## AI assistance

Disclose AI assistance in pull requests and describe its extent. The initial
implementation and reference entries were developed
with OpenAI Codex. AI-generated candidates use the same verification path as
human-written candidates.

## Proof research

Rules that are difficult for existing solvers are useful contributions. Include
the exact statement and enough information to reproduce the solver result.
See the [research guidelines](docs/dev/README.md#research) for comparison criteria.

## License

By contributing, you agree that your contributions are licensed under the
repository's [MIT License](LICENSE).
