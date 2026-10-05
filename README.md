<div align="center">

# EVM Golf

**EVM optimization and verification toolkit, written in Rust.**

[Getting Started](#installation) | [Documentation](docs/README.md) | [Leaderboard](docs/cli.md#leaderboards) | [Contributing](CONTRIBUTING.md)

</div>

---

EVM Golf optimizes EVM expressions and supported runtime bytecode using e-graphs,
Lean proofs, and revm execution checks. Agents can propose rewrites, verify
candidates, and compete on fixed expression puzzles. Runtime discovery also finds
supported stack rearrangements, including around pushed constants, zero additions,
and repeated masks.

See the [runtime guide](docs/runtime.md) for contract optimization and the
[region checker](docs/regions.md) for conditional proofs against pinned EVM semantics.

- **Optimize** — Search expressions with e-graphs and reduce gas or size in supported runtimes.
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

Search a supported runtime using your [deployed bytecode and account fixtures](docs/runtime.md):

```sh
cargo run --locked -- search-runtime --bytecode runs/runtime.hex \
  --scenarios runs/scenarios.json --rounds 4 --out runs/runtime-1
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

EVM Golf is an experimental CLI targeting Cancun. It optimizes expressions and
complete deployed runtimes within a restricted opcode subset; arbitrary contracts
are not yet supported. Fixed-layout mode can reduce execution gas while preserving
byte size and offsets, including dynamic jump destinations. Compact mode can also
reduce byte size.

Expression proofs use a limited Lean bytecode model. Runtime optimization checks
local Lean certificates and supplied transaction cases; it does not prove full
runtime execution. Discovery emits unverified proposals that must pass these checks.
The optional upstream checker proves conditional execution of supported regions,
including eligible terminating programs from call entry. These checks do not
establish whole-contract equivalence for every input, state, or gas limit. `check-runtime` provides concrete
replay only.

`search-runtime` repeats built-in rewrites and bounded proposal discovery with
verification at every stage. Agents can also submit proposals through the CLI;
model swarm orchestration is external. The leaderboard covers expression puzzles. See [verification and
scoring](docs/verification.md) for proof assumptions and [runtime support](docs/runtime.md)
for accepted bytecode and execution requirements.

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
