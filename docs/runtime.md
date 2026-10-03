# Runtime bytecode

The runtime optimizer works directly on deployed Cancun bytecode. It can shrink
complete contracts within a conservative subset: resolved jumps and internal
returns, storage, memory, logs, returns, and reverts. `--preserve-layout` also
supports dynamic jumps, PC, and CODESIZE by keeping every byte offset unchanged.
Both modes admit restricted ECRECOVER precompile calls described below. Other
reachable calls, creation, selfdestruct, code-content introspection, and gas
introspection remain unsupported. The separate `check-runtime` command can
execute these operations against supplied account fixtures; it does not optimize
or formally prove the proposed candidate.

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
are decimal or `0x` strings. Duplicate literal or numeric storage keys are rejected.
Missing value means zero; missing storage means empty.
Gas limits are explicit. The caller is `0x1111…1111`, the contract is
`0x2222…2222`, and the caller starts funded. Gas price is zero; other environment
fields use revm defaults. These inputs do not exercise arbitrary environments or
external account state. Use selectors and boundary values
that exercise your contract's branches, storage changes, events, and reverts.

```sh
cargo run --locked -- optimize-runtime \
  --bytecode runs/runtime.hex --cases runs/cases.json --out runs/runtime-1
```

For stateful workflows, use `--sequences` instead of `--cases`. Save an array in
`runs/sequences.json`:

```json
[
  {
    "storage": {"0": "7"},
    "transactions": [
      {"calldata": "0x12345678", "gas_limit": 200000, "value": "1"},
      {"calldata": "0xabcdef01", "gas_limit": 200000}
    ]
  }
]
```

Replace these placeholder selectors with calls to your contract. Each sequence
starts fresh, applies its initial storage once, and commits state between calls.
Every transaction uses the same funded caller and fixed environment described
above; steps do not advance the block number or timestamp. Nonces advance
automatically. Reverts roll back contract effects and value
transfers while advancing the caller nonce; later transactions still run.
Transient storage, access warmth, and refunds reset for each transaction.
Per-transaction storage overrides and empty sequences are rejected.

```sh
cargo run --locked -- optimize-runtime \
  --bytecode runs/runtime.hex --sequences runs/sequences.json --out runs/sequence-1
```

For real deployment state, use `--scenarios` instead of `--cases` or `--sequences`.
This accepts the [account-fixture format](#general-runtime-replay), preserving the
caller, deployed address, constructor-initialized storage, balances, nonces, and
explicit block environment. Supply the actual deployed runtime with immutables
resolved. The CLI does not execute constructors or fetch chain state.

```sh
cargo run --locked -- optimize-runtime --bytecode runs/runtime.hex \
  --scenarios runs/scenarios.json --preserve-layout --out runs/fixture-1
```

Choose exactly one input format. Fixtures use the same optimization, Lean proof,
and replay gates; they do not permit additional opcodes. Contracts with reachable
external calls other than the restricted ECRECOVER pattern remain unsupported,
even though `check-runtime` can replay them. Scenario runs save `scenarios.json` and order report cases by
scenario, then transaction.

Use a new output directory. Successful runs write `candidate.hex` and
`result.json`. Inputs, exact rewrite pairs, and Lean diagnostics remain local;
execution failures leave `failure.log` without an accepted candidate or score.
A run with no applicable rewrites may return the original runtime. Results are
not committed, and runtime cases are not expression leaderboard entries.
Input evidence is saved as compact JSON. Sequence runs save `sequences.json`;
`result.json` keeps the existing `cases` array, ordered by input sequence and then transaction. Failure messages use
zero-based sequence and transaction indices.

## Input limits

Runtime hex and JSON files are limited to 1 MiB each, including whitespace.
Library fixture inputs have the same limit when serialized as compact JSON.
Each batch accepts at most 256 transactions, at most 30,000,000 gas per transaction,
and at most 300,000,000 total gas for each of the original and candidate programs.
These operational budgets permit bounded local replay; they are not Ethereum
protocol limits. Oversized batches and duplicate JSON map keys are rejected before
execution. Earlier versions could silently replace duplicate storage keys in cases
or sequences; those ambiguous inputs are now errors.

## Transformation boundary

The decoder distinguishes instructions from PUSH data and preserves unreachable
bytes, including metadata, in their original order. Reachable truncated PUSHs
are rejected. Input size is bounded by EIP-170's 24,576-byte deployed-code limit;
EOF input is unsupported.

Every reachable JUMP or JUMPI must resolve to a PUSH of a valid JUMPDEST offset.
The analysis tracks the originating PUSH through DUP and SWAP, including internal
function return addresses and shared helpers reached from different callers.
It rejects labels also used as numeric data.
Identity arithmetic (`+ 0`, `| 0`, `^ 0`, `* 1`) can preserve a label's source,
in either operand order. The neutral operand is numeric data and cannot also be
relocated. Other arithmetic-derived targets remain unsupported in compact mode.
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

## Signature precompile calls

The optimizer admits `GAS; STATICCALL` only when the callee is provably the exact
word `1` (ECRECOVER) on every analyzed path. GAS must be consumed immediately;
it cannot be stored, copied or used by arithmetic. Compact mode follows PUSH
provenance through existing stack operations. Fixed-layout mode requires the
literal sequence `PUSH1..32 1; GAS; STATICCALL`. Neither mode rewrites the call.
Other callees, call types, and gas-forwarding patterns are rejected.

Optimization replay requires every observed ECRECOVER call to succeed on both
sides, including calls whose result is discarded or whose parent later reverts.
It compares ordered effective inputs (the first 128 zero-padded bytes), input
length/region, output region, and returned bytes. An invalid signature is a
successful call with empty returndata; it remains supported. Forwarded gas may
differ, but underfunded calls reject the run even if outer results match.

This is a concrete replay guard, not an all-gas proof: savings can move a call
across ECRECOVER's 3,000-gas threshold. Supplied cases cannot establish that all
other executions remain above that threshold. The general `check-runtime`
command retains ordinary failed-subcall behavior without this optimizer guard.

## Preserve byte offsets

Use `--preserve-layout` with `analyze-runtime` or `optimize-runtime`. This mode
follows fallthrough and conservatively considers every decoded JUMPDEST reachable
from any jump. It does not resolve jump values or prove global stack heights.
It preserves instruction boundaries, all JUMPDEST positions, and total length,
so PC, CODESIZE, and computed jump offsets remain stable.

The initial rules replace multiplication by zero, one, or two with AND zero,
ADD zero, or SHL one, retaining the original PUSH width. Each has the same input
stack requirement, peak growth, and final height, and saves two opcode gas before
refunds. Lean checks each exact fragment and a certificate containing the complete,
independently embedded original and candidate byte arrays. The certificate checks
that sorted, nonoverlapping replacements reconstruct the candidate, that every
other byte is unchanged, and that instruction boundaries, JUMPDEST positions,
length, and local stack profiles agree. Replacements inside PUSH data are rejected.
The artifact model is [lean/Layout.lean](../lean/Layout.lean). Each site's
certificate also executes its exact fragments under
[lean/Stack.lean](../lean/Stack.lean), which enforces the 1,024-word bound at every
instruction boundary. It proves equal successful results for incoming heights
1–1,023, underflow on an empty stack, and overflow at height 1,024. These local
properties do not establish the heights reached by the surrounding program.

This structural certificate requires Lean even when no rewrite applies. Its closed
checks use `decide +kernel`, and runtime certificates permit only Lean's standard
foundational axioms. Expression-specific native proof dependencies are rejected.
The existing 60-second proof budget still applies: any timeout is rejected, even within the byte-size
limit. Kernel checking avoids repeated elaborator work on dense artifacts; no
universal completion-time guarantee follows. It does not prove reachability,
whole-program stack safety, gas behavior, or correspondence between the Lean model
and all EVM semantics.
Gas-limit effects and code-content observations remain outside the equivalence claim.
No byte-size reduction is expected.

## General runtime replay

`check-runtime` accepts supplied original/candidate deployed legacy bytecode,
including dynamic jumps, external calls, creation, selfdestruct, precompiles,
and gas/code introspection. Revm executes the operations under Cancun; this
command does not run the optimizer's CFG analysis or Lean proofs.

```sh
cargo run --locked -- check-runtime --original runs/original.hex \
  --candidate runs/proposed.hex --scenarios runs/scenarios.json --out runs/checked-1
```

A scenario defines complete local starting state and a sequence of calls:

```json
[
  {
    "target": "0x2222222222222222222222222222222222222222",
    "caller": "0x1111111111111111111111111111111111111111",
    "accounts": {
      "0x1111111111111111111111111111111111111111": {"balance": "1000000"},
      "0x2222222222222222222222222222222222222222": {"storage": {"0": "7"}},
      "0x3333333333333333333333333333333333333333": {"code": "0x00"}
    },
    "environment": {"number": 100, "timestamp": 1000, "chain_id": 1},
    "transactions": [{"calldata": "0x", "gas_limit": 200000, "value": "1"}]
  }
]
```

Account fields are `balance`, `nonce`, `code`, and `storage`; omitted values are
zero or empty. The target and caller must be distinct, explicitly supplied accounts.
Target fixture code must be empty because the two hex inputs supply it. A precompile
cannot be the substituted target. The caller is funded only by the fixture.
Unspecified accounts are absent; no chain state is fetched. Numeric/address aliases
that duplicate keys are rejected. Total fixture balance must fit in a 256-bit word.

Optional environment fields are `number`, `timestamp`, `gas_limit`, `beneficiary`,
`prevrandao`, `chain_id`, `blob_excess_gas`, and `block_hashes`. Block fields stay
fixed throughout a sequence. Missing fields use revm defaults, with Cancun blob
pricing. `block_hashes` maps previous block numbers to 32-byte hex hashes; omitted
hashes in the previous 256 blocks are explicitly zero. Other hashes are rejected.
Gas price and base fee remain zero. Access lists, blob transactions, fee-bearing
transactions, constructor execution as the top-level input, and other forks are
not exposed by this fixture format.

Each transaction must match output, success/revert, ordered logs, and all committed
account balances, nonces, storage, existence, and code hashes. Only the substituted
target's code hash is excluded; newly created and other contracts' code is compared.
Candidate receipt gas must not increase. Invalid transactions and exceptional halts
reject the run. Ordinary reverts may pass and the sequence continues.

A failed run preserves `original.hex`, `proposed.hex`, `scenarios.json`, and
`failure.log`. Only a fully passing run writes `candidate.hex` and `result.json`.
The report's `cases` array follows scenario order, then transaction order. Passing
means agreement on those concrete fixtures, not general EVM equivalence or a Lean
certificate. Reports remain local and are not expression leaderboard entries.

## What is verified

Lean checks that each pair of **exact local byte fragments** produces the same
successful stack result, over arbitrary tails with the required stack prefix.
Two failing executions cannot satisfy the certificate. The base model excludes gas
and stack limits; compact-mode Rust analysis separately checks stack heights.
Layout mode adds operational local underflow/overflow proofs with the 1,024-word
bound, alongside equal local stack requirements and peak growth. These are local proofs,
not a Lean proof of the CFG, relocation implementation, or full EVM execution.

For every supplied transaction, revm compares success/revert status, return or
revert data, logs, balances, nonces, and all committed nonzero storage. Sequence
steps are compared individually, including intermediate state. Exceptional halts,
including out-of-gas, and invalid transactions fail validation. Reported gas is transaction receipt gas:
it includes intrinsic gas and applies refunds and the refund cap. Candidate gas
must not increase in any supplied case. Cases are concrete tests and do not
establish equivalence for all inputs or states. No global gas saving is inferred from byte-size savings.

Code identity changes. Deployment behavior, EXTCODEHASH observations by other
contracts, transaction fee effects, and equivalence at every gas limit are not
preserved claims. Removing gas consumption can change out-of-gas behavior and
SSTORE's gas-left check even without a GAS instruction. Do not treat the output
as universally equivalent deployed code.
