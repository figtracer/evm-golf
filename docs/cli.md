# Commands and formats

```text
evm-golf inspect  PROJECT [--contract ID]...
evm-golf optimize PROJECT [--contract ID]... [--rounds N] --out DIR
evm-golf verify   PROJECT --proposals FILE --out DIR
```

Use `cargo run --release --locked --` in place of `evm-golf` when running from a checkout.
JSON results go to stdout and progress to stderr. Every `--out` must be a new
directory. A command exits with an error if any contract is rejected; its
`result.json` still records which ones passed.

## inspect

Prints a [proposals](#proposals) document with bounded, unverified patches found
for each contract. It does not run Lean or transactions. An empty `sites` list
means the search found nothing.

## optimize

Runs up to `--rounds` (default 8) rounds per contract. Each round applies the
built-in rewrites, threads jumps past trampolines, then discovers and verifies
proposals. Every stage is proved
and replayed, and the final bytecode is replayed against the original. A failed
proposal batch is retried with half its sites; a site that fails alone is skipped.
A failed threading stage is recorded and threading is not retried.
Contracts are independent jobs.

## verify

Checks the exact patches in `--proposals`. Every site for a contract must pass
the proof and replay, otherwise that contract is rejected unchanged. Contracts
not listed in the file are not loaded.

## Project

```json
{
  "version": 1,
  "contracts": [
    { "id": "token", "runtime": "token.hex", "scenarios": "token.scenarios.json" }
  ]
}
```

`id`: 1 to 64 ASCII letters, digits, `-` or `_`, unique. `runtime`: deployed
bytecode as hex (immutables already filled in, at most 24,576 bytes). Paths are
relative to the project file. Unknown fields are rejected.

## Scenarios

A JSON array. Each scenario starts from fresh state and runs its transactions in
order, committing state between them.

```json
[
  {
    "caller": "0x1111111111111111111111111111111111111111",
    "target": "0x2222222222222222222222222222222222222222",
    "accounts": {
      "0x1111111111111111111111111111111111111111": { "balance": "1000000" },
      "0x2222222222222222222222222222222222222222": { "nonce": 1, "storage": { "0": "7" } }
    },
    "transactions": [{ "calldata": "0x", "gas_limit": 100000, "value": "0" }],
    "environment": { "number": 1, "timestamp": 1 }
  }
]
```

- `target` receives the runtime under test. Other accounts may carry `code`,
  `balance`, `nonce` and `storage`; contracts called by the target must be listed.
- A transaction may set `to` to call another listed account first.
- `environment` is optional: `number`, `timestamp`, `gas_limit`, `beneficiary`,
  `prevrandao`, `chain_id`, `blob_excess_gas`, `block_hashes`.
- Numbers are decimal or `0x` strings. Duplicate keys are rejected.
- Limits: 1 MiB per file, 256 transactions, 30,000,000 gas per transaction and
  300,000,000 in total.

Both versions must produce the same success or revert, output, logs, storage,
balances and nonces, and the candidate must not use more gas. Exceptional halts
(including out of gas) are rejected. See [runtime support](runtime.md#replay).

## Proposals

```json
{
  "version": 1,
  "contracts": [
    {
      "id": "token",
      "original_keccak256": "0x...",
      "sites": [{ "original_pc": 6, "before": "6004909250905061227050", "after": "6122705091505062000004" }]
    }
  ]
}
```

`original_keccak256` binds the patches to the exact runtime; a stale hash is
rejected. Sites are disjoint windows of whole instructions (at most 32 per
contract), `before` must match the runtime at `original_pc`, and `after` must have
the same length. The checker derives stack requirements and generates the proof;
proposals carry no proof or metadata.

## Output

```text
DIR/result.json              per contract: accepted, gas before/after, rewrites,
                             gas saved per call for each called function
DIR/baseline/project.json    next project: accepted bytecode, same scenarios
DIR/<id>/                    evidence: candidate.hex, Rewrites.lean/.log,
                             rewrites.json, scenario traces, failure.log
```

`optimize` stores one subdirectory per search stage under `DIR/<id>/`.
