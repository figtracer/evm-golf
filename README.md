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

Each run prints and writes the gas saved per call for each function, for
example `transfer(address,uint256): 0 to 15 gas saved per call (5 calls)`. A
function can save different amounts on different paths, so the report gives a
range.
`result.json` also has the totals, and `baseline/project.json` is a ready-to-use
project pointing at the accepted bytecode.
Use `cargo run --locked --` in place of `evm-golf` if it is not installed.
Try it on [examples/quickstart](examples/quickstart):
`cargo run --locked -- optimize examples/quickstart/project.json --out runs/demo`.

## Results

`optimize` with default settings on 36 ERC20 and ERC4626 builds: OpenZeppelin,
Solady and Solmate; legacy and via-IR pipelines; optimizer off, 200 and 10,000
runs. Every stage was proved and replayed. Gas saved per call, as the median
over the builds whose transactions call the function, and the largest:

| Function | Builds | Median | Largest |
| --- | ---: | ---: | ---: |
| `transfer` | 18 | 14 | 33 |
| `transferFrom` | 18 | 15.5 | 44 |
| `approve` | 18 | 9 | 23 |
| `balanceOf` | 36 | 3 | 15 |
| `deposit` | 18 | 6 | 128 |
| `mint` | 18 | 10 | 116 |
| `withdraw` | 18 | 10.5 | 182 |
| `redeem` | 18 | 10.5 | 118 |

A call saves different amounts on different paths. Unoptimized builds gain
most, mostly from jump threading. On runtimes that were already optimized
(Balancer vault token info, Uniswap V3 pool swaps) the search still saves 6 to
10 gas per transaction on average. Savings are execution gas only; intrinsic
and storage costs dominate total transaction gas. Typical accepted rewrites:

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
Only a subset of opcodes and control flow is supported. A developer command
proves whole-program refinement against EVMYulLean (interpreter, code execution,
message call and transaction level), but only for call-free runtimes with the
power, JUMPI-threading and stack-window rewrites. That proof carries facts
about the stack across jumps, so a window can drop, for example, a mask on a
`CALLER` value. See
[verification](docs/verification.md) for the exact boundary and
[runtime support](docs/runtime.md) for what can be optimized.

## Documentation

[Commands and formats](docs/cli.md), [runtime support](docs/runtime.md),
[verification](docs/verification.md), [development](docs/dev/README.md) and
[contributing](CONTRIBUTING.md).

## License

[MIT](LICENSE). Built with [Lean](https://github.com/leanprover/lean4) and
[revm](https://github.com/bluealloy/revm).
