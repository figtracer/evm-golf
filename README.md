<div align="center">

# EVM Golf

**Verified gas optimization for deployed EVM contracts.**

[Quick start](#quick-start) | [Commands](docs/cli.md) | [Verification](docs/verification.md) | [Agent guide](AGENTS.md)

</div>

---

EVM Golf rewrites deployed runtime bytecode to use less gas. Every accepted change
is checked twice: Lean proves the rewritten instructions equivalent in a bounded
model, and revm replays your transactions against both versions with guarded
calls and effects. Byte offsets never move, so jump tables and code copies stay
valid.

Bring your own agents: they read a contract, propose exact byte patches, and the
checker accepts only what it can prove and replay.

## Quick start

```sh
git clone https://github.com/figtracer/evm-golf.git
cd evm-golf
bash scripts/setup-lean.sh   # pinned Lean 4.34.0 inside the checkout
cargo build --locked
```

Describe your contracts in a `project.json`. Paths are relative to the file:

```json
{
  "version": 1,
  "contracts": [
    { "id": "token", "runtime": "token.hex", "scenarios": "token.scenarios.json" }
  ]
}
```

`runtime` is the deployed bytecode in hex. `scenarios` lists accounts and
transactions to replay ([format](docs/cli.md#scenarios)). Then:

```sh
evm-golf optimize project.json --out runs/opt-1        # built-in search, verified
evm-golf inspect project.json > proposals.json         # discovered, unverified patches
evm-golf verify project.json --proposals proposals.json --out runs/check-1
```

Each run writes `result.json` (gas before and after per contract) and
`baseline/project.json`, a ready-to-use project pointing at the accepted bytecode.
Use `cargo run --locked --` in place of `evm-golf` if it is not installed.
Try it on [examples/quickstart](examples/quickstart):
`cargo run --locked -- optimize examples/quickstart/project.json --out runs/demo`.

## Results

`optimize` with default settings, aggregated over the supplied transactions
(every stage proved and replayed, no failed batches):

| Workload | Baseline | Transactions | Gas saved |
| --- | --- | ---: | ---: |
| 36 ERC20 and ERC4626 builds | solc output | 1,026 | 8,981 |
| Balancer vault token info | already optimized runtime | 23 | 219 more |
| Uniswap V3 pool, tick crossing | already optimized runtime | 37 | 228 more |
| Uniswap V3 pool, no crossing | already optimized runtime | 40 | 407 more |

The 36 builds cover OpenZeppelin, Solady and Solmate, legacy and via-IR pipelines,
and optimizer off, 200 and 10,000 runs. Rows are separate baselines; do not add
them. Savings are execution gas only: they are about 0.03% of total transaction
gas here, which is dominated by intrinsic and storage costs. Unoptimized via-IR
builds gain most (300 to 550 gas each), mostly from jump threading. Typical
accepted rewrites:

| Before | After | Saved per execution |
| --- | --- | ---: |
| `PUSH1 0x20 DUP2 SWAP1` | `DUP1 PUSH2 0x0020` | 3 |
| `PUSH1 a PUSH1 0x20 SWAP1` | `PUSH1 0x20 PUSH2 a` | 3 |
| `POP PUSH2 c SWAP3 POP POP POP` | `POP POP POP POP PUSH3 c` | 3 |
| `PUSH2 X JUMPI`, X: `JUMPDEST PUSH2 Y JUMP` | `PUSH2 Y JUMPI` | 12 when taken |

Widened PUSH immediates keep every byte offset unchanged.

## What is and is not proven

Accepted changes carry local Lean certificates over bounded stack and control-flow
models, bound to the exact full bytecode, plus replay of your transactions. That is
not whole-contract equivalence: inputs, states and gas limits outside your
scenarios are not covered, and contracts are optimized independently.
Only a subset of opcodes and control flow is supported. See
[verification](docs/verification.md) for the exact boundary and
[runtime support](docs/runtime.md) for what can be optimized.

## Documentation

[Commands and formats](docs/cli.md), [runtime support](docs/runtime.md),
[verification](docs/verification.md), [development](docs/dev/README.md) and
[contributing](CONTRIBUTING.md).

## License

[MIT](LICENSE). Built with [Lean](https://github.com/leanprover/lean4) and
[revm](https://github.com/bluealloy/revm).
