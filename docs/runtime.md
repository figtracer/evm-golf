# Runtime bytecode

The runtime optimizer works directly on deployed Cancun bytecode. It can shrink
complete contracts within a conservative subset: resolved jumps and internal returns, storage, memory,
logs, returns, and reverts. Creation code, unresolved computed jumps, calls,
creation, selfdestruct, code introspection, and gas introspection are unsupported.
An unsupported reachable instruction or unresolvable jump rejects the input.

## Run

Save runtime bytecode as hexadecimal in `runs/runtime.hex` (an optional `0x`
prefix and surrounding whitespace are accepted). Use the deployed runtime,
not constructor bytecode or a whole compiler artifact. Constructor-set immutables
must already be patched: unpatched compiler templates are not concrete runtime
images. For contracts without immutables, solc's
`--evm-version cancun --bin-runtime` output contains the appropriate hex section.

Analyze it first:

```sh
cargo run --locked -- analyze-runtime --bytecode runs/runtime.hex
```

Supply a JSON array of isolated transaction cases in `runs/cases.json`:

```json
[
  {"calldata": "0x", "gas_limit": 200000},
  {"calldata": "0x12345678", "gas_limit": 200000, "value": "1", "storage": {"0": "7"}}
]
```

Each case starts from fresh state. Calldata is hex; value and storage keys/values
are decimal or `0x` strings. Duplicate numeric storage keys are rejected. Missing value means zero; missing storage means empty.
Gas limits are explicit. The caller is `0x1111…1111`, the contract is
`0x2222…2222`, and the caller starts funded. Gas price is zero; other environment
fields use revm defaults. Cases do not exercise arbitrary environments, external
account state, or sequences of transactions. Use selectors and boundary values
that exercise your contract's branches, storage changes, events, and reverts.

```sh
cargo run --locked -- optimize-runtime \
  --bytecode runs/runtime.hex --cases runs/cases.json --out runs/runtime-1
```

Use a new output directory. Successful runs write `candidate.hex` and
`result.json`. Inputs, exact rewrite pairs, and Lean diagnostics remain local;
execution failures leave `failure.log` without an accepted candidate or score.
A run with no applicable rewrites may return the original runtime. Results are
not committed, and runtime cases are not expression leaderboard entries.

## Transformation boundary

The decoder distinguishes instructions from PUSH data and preserves unreachable
bytes, including metadata, in their original order. Reachable truncated PUSHs
are rejected. Input size is bounded by EIP-170's 24,576-byte deployed-code limit;
EOF input is unsupported.

Every reachable JUMP or JUMPI must resolve to a PUSH of a valid JUMPDEST offset.
The analysis tracks the originating PUSH through DUP and SWAP, including internal
function return addresses and shared helpers reached from different callers.
It rejects labels also used as numeric data and destinations computed by arithmetic.
Equal-valued constants from distinct PUSH instructions retain distinct identities.

Both conditional edges and distinct stack-provenance states are analyzed, with
underflow and the 1,024-item EVM limit checked on each path. Shared blocks may have
multiple incoming heights. Stack-changing loops can be rejected even when
particular inputs would terminate safely. Analysis fails closed at 65,536 retained
states or 1,048,576 compact stack cells to bound combinatorial path growth. These
are operational limits, not permission to omit paths.

The pass repeatedly shortens constant pushes, folds supported constant arithmetic
and bitwise operations, removes selected stack identities, and replaces doubling
with DUP1/ADD. It does not rewrite across control-flow or side-effect boundaries.
Proven jump-label PUSHs are protected and relocated after shortening, preserving
their immediate widths. The emitted runtime is decoded and analyzed again.

## What is verified

Lean checks that each pair of **exact local byte fragments** produces the same
successful stack result, over arbitrary tails with the required stack prefix.
Two failing executions cannot satisfy the certificate. The model excludes gas
and stack limits; Rust analysis separately checks stack heights. These are local proofs,
not a Lean proof of the CFG, relocation implementation, or full EVM execution.

For every supplied case, revm compares success/revert status, return or revert
data, logs, balances, nonces, and final storage (initial slots overlaid with
journal changes). Exceptional halts, including out-of-gas, fail validation. Reported gas is transaction receipt gas:
it includes intrinsic gas and applies refunds and the refund cap. Candidate gas
must not increase in any supplied case. Cases are concrete tests and do not
establish equivalence for all inputs or states. No global gas saving is inferred from byte-size savings.

Code identity changes. Deployment behavior, EXTCODEHASH observations by other
contracts, transaction fee effects, and equivalence at every gas limit are not
preserved claims. Removing gas consumption can change out-of-gas behavior and
SSTORE's gas-left check even without a GAS instruction. Do not treat the output
as universally equivalent deployed code.
