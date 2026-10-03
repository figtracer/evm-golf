# Runtime bytecode

The runtime optimizer works directly on deployed Cancun bytecode. It can shrink
complete contracts within a conservative subset: resolved jumps and internal
returns, storage, memory, logs, returns, and reverts. `--preserve-layout` also
supports dynamic jumps, PC, and CODESIZE by keeping every byte offset unchanged.
Both modes admit restricted ECRECOVER precompile calls described below. With
explicit account fixtures, fixed-layout mode also admits guarded CALL/STATICCALL,
EXTCODESIZE, and certified constant CODECOPY reads. Creation, delegation,
selfdestruct, dynamic code-content introspection
and standalone gas introspection remain unsupported in the optimized runtime.
The separate `check-runtime` command can
execute these operations against supplied account fixtures; it does not optimize
or formally prove the proposed candidate.

For a separate conditional proof of a supported internal compiler prefix, see
[internal-region certificates](regions.md). This opt-in command uses pinned
upstream semantics and does not replace the runtime optimizer’s existing gates.

## Select rewrite sites

List the fixed-layout opportunities for an exact runtime:

```sh
cargo run --locked -- runtime-opportunities --bytecode runs/runtime.hex > runs/opportunities.json
```

The JSON contains `original_keccak256` and trusted `rewrites` with original PCs,
before/after bytes and required stack heights. Listing sites does not verify a
candidate or run transactions. It uses the account-fixture opcode policy; actual
optimization still requires the supplied scenarios and all existing proof gates.

Copy the returned hash into a plan and select PCs from that catalog:

```json
{
  "original_keccak256": "0x<64 hex digits from the catalog>",
  "selected_pcs": [2, 8]
}
```

The PCs above are illustrative; use sites from your own catalog. Then run:

```sh
cargo run --locked -- optimize-runtime --bytecode runs/runtime.hex \
  --preserve-layout --scenarios runs/scenarios.json --plan runs/plan.json \
  --out runs/selected-1
```

Plans require `--preserve-layout` and `--scenarios`. The tool checks the baseline
hash, rejects duplicate/unknown PCs and regenerates replacements itself. A plan
cannot supply candidate bytes or Lean source. Empty selection preserves the
baseline; selection order does not matter. Omitting `--plan` keeps the existing
all-sites behavior. Each run uses a fresh output directory and saves `plan.json`
before proof checking and replay. Accepted outputs require the same local artifact
proofs and fixture checks as other fixed-layout runs; no whole-contract or all-input
equivalence is established. This supports external proposal search, but does not
launch agents, schedule a campaign or resume interrupted runs.

## Run

Save runtime bytecode as hexadecimal in `runs/runtime.hex` (an optional `0x`
prefix and surrounding whitespace are accepted). Use the deployed runtime,
not constructor bytecode or a whole compiler artifact. Constructor-set immutables
must already be patched: unpatched compiler templates are not concrete runtime
images. For contracts without immutables, solc's
`--evm-version cancun --bin-runtime` output contains the appropriate hex section.

For the conservative default opcode subset, analyze it first. General external
calls require the fixture-aware optimization path below:

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

Choose exactly one input format. Fixed-layout fixtures use the same local Lean
artifact proofs and add the [external-call guard](#guarded-external-calls).
Compact mode, isolated cases and sequences retain the restricted ECRECOVER
policy. Scenario runs save `scenarios.json` and order report cases by scenario,
then transaction.

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
bytes, including metadata, in their original order. Undefined opcode bytes are
retained as exceptional-halt boundaries; fallthrough stops there while independently
reachable jump destinations are still analyzed. Reachable known but unsupported
or fork-disabled instructions remain rejected. Halted replay cases still fail
validation. Reachable truncated PUSHs are rejected. Input size is bounded by
EIP-170's 24,576-byte deployed-code limit; EOF input is unsupported.

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
Other callees, call types, and gas-forwarding patterns are rejected by this
policy. Fixed-layout account fixtures use the broader guard below.

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

## Guarded external calls

`--preserve-layout --scenarios` admits CALL, STATICCALL and EXTCODESIZE. GAS is
allowed only immediately before CALL or STATICCALL. Calls are never rewritten.
Every observed callee must have an explicit fixture account, including empty-code
accounts; native ECRECOVER at address 1 is the only exception. Other precompiles,
delegation, creation and selfdestruct are rejected. This currently excludes proxy
assets that use DELEGATECALL.

The guard runs in every executed frame, including callbacks into the optimized
target. Constant target CODECOPY is admitted only after three complete literal
PUSH instructions (length, source, destination), with an in-bounds source range.
Lean checks the unchanged prefix and equal copied bytes in both complete images;
rewrites touching copied bytes are skipped. Replay checks the actual image, site,
and stack arguments, including callbacks. Dynamic reads and out-of-bounds ranges
(including zero-length reads with an out-of-bounds source) remain unsupported.
This is byte-preservation evidence, not a formal EVM memory or gas theorem.

The guard rejects standalone GAS and EXTCODECOPY/EXTCODEHASH of
the target. Other accounts retain their original code. Exceptional failures,
including failed child calls whose results are discarded, reject optimization;
matching explicit REVERT is allowed. ECRECOVER must execute successfully as a
native precompile.

Replay compares exact ordered call contexts, calldata, output regions, outcomes
and returndata, plus SSTORE/TSTORE attempts and emitted logs, including effects
later rolled back. Independent databases retain the existing receipt, output,
committed-state and non-increasing gas checks. Forwarded gas may differ: the
trace comparison is concrete evidence for the supplied executions, not an
all-gas or whole-contract proof. Untested paths and observations remain unproved.
The existing Lean layout proposition does not interpret calls. Constant own-code
reads add a separate certificate for their literal prefixes, bounds, and bytes.

Baseline traces are streamed to `scenario-N-calls/transaction-M.trace` and
candidates compare them byte for byte. Each transaction is limited to 1 MiB of
serialized observations per side, checked before payload traversal. This bounds
repeated reads of reused memory independently of EVM gas; exceeding the budget
rejects the run without an accepted candidate. No trace is silently truncated.
`check-runtime` retains its general transaction-replay policy.

## Preserve byte offsets

Use `--preserve-layout` with `analyze-runtime` or `optimize-runtime`. This mode
follows fallthrough and conservatively considers every decoded JUMPDEST reachable
from any jump. It does not resolve jump values or prove global stack heights.
It preserves instruction boundaries, all JUMPDEST positions, and total length,
so PC, CODESIZE, and computed jump offsets remain stable.

The rules replace multiplication by zero or one with AND zero or ADD zero, and
multiplication by any other 256-bit power of two with SHL by its exponent. They
retain the original PUSH width, including padded constants, and save two opcode
gas before refunds. The exact `PUSH1 0; DUP1` pair becomes `PUSH1 0; PUSH0`,
saving one opcode gas with the same two-slot stack peak. Two-literal AND/SHL folds
keep both PUSH widths and replace
the operation with POP, storing the result in the first literal when it fits.
These save one opcode gas while preserving the temporary two-word stack peak.
These rewrites preserve input requirements and final height. Lean validates the
exact site list with a [proved checker](../lean/Certificates.lean),
reusing symbolic fragment proofs. The full certificate contains independently
embedded original and candidate byte arrays. The certificate checks
that sorted, nonoverlapping replacements reconstruct the candidate, that every
other byte is unchanged, and that instruction boundaries, JUMPDEST positions,
length, and local stack profiles agree. Replacements inside PUSH data are rejected.
The artifact model is [lean/Layout.lean](../lean/Layout.lean). Each site's
certificate also executes its exact fragments under
[lean/Stack.lean](../lean/Stack.lean), which enforces the 1,024-word bound at every
instruction boundary. Multiplication rewrites prove equal successful results at
incoming heights 1–1,023, underflow on an empty stack, and overflow at height 1,024.
Literal folds use a separate proposition: success at heights 0–1,022 and overflow
from 1,023 upward. The emitted required-stack metadata selects the corresponding
proof; matching stack profiles alone cannot certify a rewrite. These local properties do not establish the heights reached by the surrounding program.
[lean/Composition.lean](../lean/Composition.lean) additionally proves that each
replacement preserves the result under any completely decoded prefix and suffix
in the bounded model, including preservation of successful execution. The proof
runs the actual concatenated byte lists and relates sufficient instruction fuel
to the byte-length budgets. Complete boundaries matter: a suffix must not supply
missing PUSH data. This is contextual substitution inside the small model,
not interpretation of all surrounding contract instructions.

This structural certificate requires Lean even when no rewrite applies. Its closed
checks use `decide +kernel`, and runtime certificates permit only Lean's standard
foundational axioms. The final artifact's axiom report covers the shared checker
and its local proofs transitively. Expression-specific native proof dependencies
are rejected.
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
