<div align="center">

# EVM Golf

**EVM optimization and verification toolkit, written in Rust.**

[Getting Started](#installation) | [Documentation](docs/README.md) | [Leaderboard](docs/cli.md#leaderboards) | [Contributing](CONTRIBUTING.md)

</div>

---

EVM Golf optimizes EVM expressions and supported runtime bytecode using e-graphs,
Lean proofs, and revm execution checks. Agents can propose rewrites, verify
candidates, and compete on fixed expression puzzles.

For contract bytecode, see the [runtime guide](docs/runtime.md). The optional
[region checker](docs/regions.md) verifies selected arithmetic, bitwise, and memory spans,
including supported rewrites and stack permutations, against pinned EVM semantics.
It can also certify a span’s terminal static jump with checked destination proofs.

- **Optimize** — Search expressions with e-graphs and shrink supported runtime bytecode.
- **Verify** — Check expression equivalence and emitted bytecode against a Lean model.
- **Compete** — Submit solutions to fixed puzzles and generate verified leaderboards.
- **Evaluate** — Replay agent proposals and compare them with the built-in optimizer.

## Installation

Build from source with Rust and Cargo. The Lean setup script requires `curl`,
`tar`, and `zstd` and installs the pinned toolchain inside the checkout.

```sh
git clone https://github.com/figtracer/evm-golf.git
cd evm-golf
bash scripts/setup-lean.sh
cargo build --locked
```

See [installation and setup](docs/getting-started.md) for toolchain requirements.

## Getting Started

Optimize an expression:

```sh
cargo run --locked -- optimize '(+ (* x 2) (- y y))' --out runs/optimization
```

Optimize a runtime using your [bytecode and execution cases](docs/runtime.md):

```sh
cargo run --locked -- optimize-runtime --bytecode runs/runtime.hex --cases runs/cases.json --out runs/runtime-1
```

Outputs include bytecode, proofs, logs, and scores. Keep generated results local.

Submit a puzzle solution:

```sh
cargo run --locked -- challenges
cargo run --locked -- submit double '(shl1 x)' --author your-name --out runs/submission
```

Use a new output directory for each run. See the [command reference](docs/cli.md)
for verification, leaderboards, and batch submissions.

## Status

EVM Golf is experimental and targets Cancun. Expression verification covers a
limited Lean bytecode model. The [runtime optimizer](docs/runtime.md) accepts
hex bytecode with resolved jumps, or dynamic jumps in a mode that preserves byte
offsets. A separate checker replays arbitrary Cancun runtimes with external-account
fixtures. Local Lean proofs and concrete replay do not prove arbitrary whole-contract
equivalence.

See [verification and scoring](docs/verification.md) for the supported semantics,
proof assumptions, and limits.

## Contributing

Contributions to the optimizer, verifier, and challenge set are welcome. Read the
[contribution guidelines](CONTRIBUTING.md) and [developer documentation](docs/dev/README.md).
Agents can use the [agent guide](AGENTS.md).

## Support

For bugs and feature requests, [open an issue](https://github.com/figtracer/evm-golf/issues).
Include the command, input expression, toolchain versions, and relevant checker output.

## Acknowledgements

Built with [egg](https://github.com/egraphs-good/egg),
[Lean](https://github.com/leanprover/lean4), and
[revm](https://github.com/bluealloy/revm). Inspired by [zkGolf](https://zk.golf/).

## License

Licensed under the [MIT License](LICENSE).
