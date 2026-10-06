<div align="center">

# EVM Golf

**Verified gas optimization for deployed EVM contracts.**

[Quick start](#quick-start) | [Results](docs/results.md) | [Commands](docs/cli.md) | [Verification](docs/verification.md) | [Agent guide](AGENTS.md)

</div>

---

EVM Golf rewrites deployed runtime bytecode to use less gas. It accepts a change
only if Lean proves it and revm replays your transactions with the same results.

## Highlights

- Saves 14 gas per `transfer` on a usual ERC20 build, and up to 182 gas per
  `withdraw` on an unoptimized ERC4626 vault ([results](docs/results.md)).
- Every change is proved in Lean and replayed in revm before it is accepted.
- Byte offsets never move, so jump tables and code copies stay valid.
- Bring your own agents: they propose byte patches, and the checker keeps
  only what it can prove and replay.

## Quick start

```sh
git clone https://github.com/figtracer/evm-golf.git
cd evm-golf
bash scripts/setup-lean.sh   # pinned Lean 4.34.0 inside the checkout
cargo build --locked
cargo run --locked -- optimize examples/quickstart/project.json --out runs/demo
```

The last command optimizes [a small example](examples/quickstart) and prints
what it saved:

```text
demo: 21030 -> 21024 gas over 1 transactions (1 rewrites)
  fallback: 6 gas saved per call (1 calls)
Results: runs/demo/result.json
Next baseline: runs/demo/baseline/project.json
```

## Use your own contracts

Describe your contracts in a `project.json`. Paths are relative to the file:

```json
{
  "version": 1,
  "contracts": [
    { "id": "token", "runtime": "token.hex", "scenarios": "token.scenarios.json" }
  ]
}
```

`runtime` is the deployed bytecode in hex. `scenarios` lists the accounts and
transactions to replay ([format](docs/cli.md#scenarios)). Then run one of:

```sh
evm-golf optimize project.json --out runs/opt-1        # built-in search, verified
evm-golf inspect project.json > proposals.json         # discovered, unverified patches
evm-golf verify project.json --proposals proposals.json --out runs/check-1
```

Each run prints the gas saved per call for each function. A function can save
different amounts on different paths, so the report gives a range, for example
`transfer(address,uint256): 0 to 15 gas saved per call (5 calls)`.
`result.json` has the same data and the totals. `baseline/project.json` points
at the accepted bytecode, so you can continue from it.
Use `cargo run --locked --` in place of `evm-golf` if it is not installed.

## What is and is not proven

| Guarantee | |
| --- | :---: |
| Each rewritten piece of code gives the same result (Lean proof) | Yes |
| Byte offsets, jump targets and code copies stay valid | Yes |
| Your transactions give the same results and use no more gas (revm replay) | Yes |
| Inputs and states that your transactions do not cover | No |
| Behavior that depends on the remaining gas | No |
| Contracts that call each other, optimized together | No |
| The whole contract is equivalent to the original | Partly: developer command only; calls need stated assumptions |

Only a subset of opcodes and control flow is supported. The developer command
proves the whole contract against EVMYulLean, a formal model of the EVM; for
`CALL` and `STATICCALL` it states its assumptions about the callees. See
[verification](docs/verification.md) for the exact boundary and
[runtime support](docs/runtime.md) for what can be optimized.

## Documentation

[Commands and formats](docs/cli.md), [results](docs/results.md), [runtime support](docs/runtime.md),
[verification](docs/verification.md), [development](docs/dev/README.md) and
[contributing](CONTRIBUTING.md).

## License

[MIT](LICENSE). Built with [Lean](https://github.com/leanprover/lean4) and
[revm](https://github.com/bluealloy/revm).
