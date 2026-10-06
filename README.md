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

We ran `optimize` with default settings on 36 builds of real token contracts:
ERC20 and ERC4626 vaults from OpenZeppelin, Solady and Solmate, compiled with
legacy and via-IR, optimizer off, 200 and 10,000 runs. Every change was proved
and replayed.

**Gas saved each time a function is called**

| Function | Usual saving | Best saving | Builds tested |
| --- | ---: | ---: | ---: |
| `transfer` | 14 gas | 33 gas | 18 |
| `transferFrom` | 15.5 gas | 44 gas | 18 |
| `approve` | 9 gas | 23 gas | 18 |
| `balanceOf` | 3 gas | 15 gas | 36 |
| `deposit` | 6 gas | 128 gas | 18 |
| `mint` | 10 gas | 116 gas | 18 |
| `withdraw` | 10.5 gas | 182 gas | 18 |
| `redeem` | 10.5 gas | 118 gas | 18 |

How to read a row: on a usual build, each `transfer` call costs 14 gas less
after optimization. On the best build, it costs 33 gas less. "Usual" is the
median over the builds whose test transactions call that function.

Builds compiled without the optimizer save the most, mostly from jump
threading. Code that was already optimized (Balancer vault, Uniswap V3 pool)
still saves 6 to 10 gas per transaction. These numbers are execution gas only.
The fixed transaction cost and storage writes stay the same.

**Examples of accepted rewrites**

| Before | After | Gas saved each time it runs |
| --- | --- | ---: |
| `PUSH1 0x20 DUP2 SWAP1` | `DUP1 PUSH2 0x0020` | 3 |
| `PUSH1 a PUSH1 0x20 SWAP1` | `PUSH1 0x20 PUSH2 a` | 3 |
| `POP PUSH2 c SWAP3 POP POP POP` | `POP POP POP POP PUSH3 c` | 3 |
| `PUSH2 X JUMPI`, X: `JUMPDEST PUSH2 Y JUMP` | `PUSH2 Y JUMPI` | 12, if the jump is taken |

The wider PUSH keeps every byte offset unchanged.

## What is and is not proven

| Guarantee | |
| --- | :---: |
| Each rewritten piece of code gives the same result (Lean proof) | ✅ |
| Byte offsets, jump targets and code copies stay valid | ✅ |
| Your transactions give the same results and use no more gas (revm replay) | ✅ |
| Inputs and states that your transactions do not cover | ❌ |
| Behavior that depends on the remaining gas | ❌ |
| Contracts that call each other, optimized together | ❌ |
| The whole contract is equivalent to the original | ⚠️ developer command only, for contracts without calls |

Only a subset of opcodes and control flow is supported. The developer command
proves the whole contract against EVMYulLean, a formal model of the EVM. See
[verification](docs/verification.md) for the exact boundary and
[runtime support](docs/runtime.md) for what can be optimized.

## Documentation

[Commands and formats](docs/cli.md), [runtime support](docs/runtime.md),
[verification](docs/verification.md), [development](docs/dev/README.md) and
[contributing](CONTRIBUTING.md).

## License

[MIT](LICENSE). Built with [Lean](https://github.com/leanprover/lean4) and
[revm](https://github.com/bluealloy/revm).
