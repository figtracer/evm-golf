# Runtime support

EVM Golf optimizes deployed legacy Cancun runtime bytecode in place: total length
and every JUMPDEST offset stay the same, so computed jumps, PC, CODESIZE and code
copies keep working. EOF and creation bytecode are not accepted.

## Supported contracts

Analysis follows fallthrough from offset 0 and treats every JUMPDEST as a possible
target. It does not resolve jump values or global stack heights. The runtime may
use storage, transient storage, memory, logs, returns, reverts and these calls:

- CALL and STATICCALL to accounts listed in the scenarios, with GAS only
  immediately before the call. Calls are never rewritten.
- ECRECOVER at address 1, which must succeed in every replayed call.
- EXTCODESIZE, and CODECOPY of the runtime itself when length, source and
  destination are literal PUSHes with an in-bounds source.

Rejected: DELEGATECALL, CALLCODE, CREATE, CREATE2, SELFDESTRUCT, other
precompiles, standalone GAS, and EXTCODECOPY or EXTCODEHASH of the target. Undefined
opcode bytes are kept as halting points. Truncated PUSHes on reachable paths are
rejected.

## Rewrites

Built-in rules (applied by `optimize`):

- MUL by 0, 1 or a power of two becomes AND 0, ADD 0 or SHL.
- Zero DUP chains reuse PUSH0; two-literal AND and SHL fold into one literal.
- Repeated address masks and 224-bit mask construction are simplified.

Discovered proposals (`inspect`, and inside `optimize`):

- Windows of up to six POP, DUP1-DUP8 and SWAP1-SWAP7 instructions before a PUSH
  are replaced by any cheaper equivalent of up to four instructions.
- One or two PUSHes inside such a window are treated as unknown values and every
  cheaper placement is tried.
- Fixed patterns: redundant zero additions, repeated masks, swaps around pushed
  constants.

Removed instructions are absorbed by widening a PUSH immediate. Discovery ranks
sites by static gas saving and selects at most 32 disjoint sites per batch. It is
a bounded search, not an optimality proof.

Your own proposals may use PUSH, DUP, SWAP, POP, ADD, AND, SUB and SHL, up to 64
bytes and 16 instructions per window, at most eight input words and two extra
stack slots. Both windows need the same stack requirement, growth and peak, and
the candidate must cost less static gas.

## Replay

Each scenario runs on two independent revm databases, one with the original
runtime and one with the candidate at `target`. For every transaction both must
match on success or revert, output, ordered logs, and committed balances, nonces,
storage, existence and code hashes (except the target's). Candidate receipt gas,
including intrinsic gas and refunds, must not increase. Exceptional halts,
including out of gas, and invalid transactions reject the run; matching reverts
are fine.

During replay a guard runs in every frame, including callbacks into the target.
It records ordered call contexts, calldata, outcomes, returndata, storage and
transient writes and logs, including effects later rolled back, and requires the
candidate to reproduce them byte for byte. Traces are limited to 1 MiB per
transaction and side.

Saving gas can still change behavior at other gas limits (for example SSTORE's
gas-left check or a call crossing a threshold). Supplied transactions cannot rule
that out.

## Limits

Input files are limited to 1 MiB. Scenarios allow at most 256 transactions,
30,000,000 gas each and 300,000,000 in total. Each Lean certificate must check
within 60 seconds of wall-clock time; a timeout is a rejection, so heavily loaded
machines can reject valid work.
