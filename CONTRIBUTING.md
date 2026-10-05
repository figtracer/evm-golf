# Contributing

Contributions are welcome: new verified rewrite families, faster certificates,
broader contract support and bug fixes. Read the [developer guide](docs/dev/README.md)
and [verification](docs/verification.md) first, and check existing
[issues](https://github.com/figtracer/evm-golf/issues) before larger changes.

Bug reports should include the runtime and scenarios (or a minimal reduction),
the command, Rust and Lean versions, and the relevant `failure.log` or
`Rewrites.log`.

## Pull requests

Keep changes focused, add regression tests and run `bash scripts/check.sh`.
Explain any change to the proof boundary, include measurements for performance
claims, and keep generated results out of the diff.

Disclose AI assistance and its extent. AI-generated proposals go through the same
checker as everything else.

## License

By contributing, you agree that your contributions are licensed under the
[MIT License](LICENSE).
