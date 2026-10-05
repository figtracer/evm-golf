# Internal-region certificates

`certify-runtime-region` checks a selected compiler prefix against the canonical
interpreter in pinned [EVMYulLean](https://github.com/NethermindEth/EVMYulLean/tree/047f63070309f436b66c61e276ab3b6d1169265a).
It proves conditional reductions to related internal states. It does not prove
that a transaction reaches the region or that the remaining execution is equivalent.
Terminal mode checks paired success or revert with equal canonical output under explicit conditions.

## Setup and use

Install the separate Lean 4.22.0 environment with Git, Python 3, curl, tar and zstd:

```sh
bash scripts/setup-upstream.sh
bash scripts/setup-upstream.sh --check
bash scripts/check-upstream.sh
cargo run --locked -- certify-runtime-region \
  --original runs/original.hex --candidate runs/candidate.hex \
  --entry-pc 1399 --out runs/region-1
```

Choose the actual entry byte offset in your runtime; the example offset is not a
contract identifier. Inputs are complete deployed hex images, subject to the same
EIP-170 limit as other runtime commands. Use a new output directory for every run.
No rewrite metadata or user-supplied Lean program is accepted.

The default installation is `.tools/upstream/{lean,semantics}`. Set
`EVM_GOLF_UPSTREAM` to another installation root when needed. Setup fetches the
exact upstream commit and its locked Git dependencies, obtains the Mathlib cache,
and builds the semantics' explicit olean target. It avoids upstream native crypto
and Ethereum test targets. `--check` checks toolchain/source pins and tracked
changes; it does not rebuild or establish cache integrity.

The checker validates the installed source revisions and Lean version, replaces
ambient Lean import paths, and freshly compiles all embedded support modules and
generated certificates. Each module has a 45-second wall-clock limit. Failure or
timeout leaves diagnostics without an accepted `result.json`. Installed Lean and
upstream/dependency compiled artifacts remain trusted, like the toolchain itself;
source revision checks do not authenticate those compiled artifacts. The existing
The Lean 4.34 runtime rewrite gates are unchanged.

## Through JUMP

Use `--through-jump` to include the power region's trailing static JUMP:

```sh
bash scripts/setup-upstream.sh --checked-scanner
cargo run --locked -- certify-runtime-region \
  --original runs/original.hex --candidate runs/candidate.hex \
  --entry-pc 1399 --through-jump --out runs/jump-region-1
```

This mode independently proves destination validity in both complete images. It
executes nine instructions per side, requires at least 33 source gas, and spends
33/31 gas. Both reach the pushed destination with stack
`0 :: 0 :: 0 :: c :: (32*a+b modulo 2^256) :: tail`; the destination instruction
has not executed. The existing stack and state premises still apply. The entry
must be an instruction boundary in each image. Without `--exit-pc`, this selects
the exact power region below. Supply `--exit-pc` for a supported span ending in
a literal push, as described under spans.

It uses a separately built, hash-identified scanner overlay on the pinned upstream
sources. The overlay makes jump scanning available to proofs; it does not prove
equivalence with upstream's original opaque scanner. The checker records the
base revision, overlay identity and import paths in `environment.json`. The
default region mode continues using the unchanged upstream semantics.

## Supported regions

Without `--exit-pc`, the command selects one of two exact byte patterns. The power region is:

```text
original:  PUSH1 32; MUL; ADD; SWAP1; PUSH0; DUP1; DUP1; PUSH2 destination; JUMP
candidate: PUSH1  5; SHL; ADD; SWAP1; PUSH0; DUP1; DUP1; PUSH2 destination; JUMP
```

The eight instructions before `JUMP` are checked. The exit is `entry_pc + 11`;
the jump destination is decoded, but the jump is not executed. The two complete
images must have equal lengths. Bytes outside this selected region may differ:
the certificate binds them independently, without certifying those other changes.

The theorem requires:

- Source stack `a :: b :: c :: tail`, top first, with arbitrary 256-bit words and
  at most 1,018 tail items. The peak stack height is at most 1,024.
- At least 25 source gas. The candidate may start with any natural gas surplus.
- Related current and original account maps with the designated owner's two
  deployed code images; unchanged account presence and other account fields.
- Each frame's execution code linked to its deployed code, and equality of the
  other frame fields, including entry PC and stack.

At the exit, both stacks are
`destination :: 0 :: 0 :: 0 :: c :: (32*a+b modulo 2^256) :: tail`.
Source cost is 25 and candidate cost is 23, increasing the gas surplus by two.
Both deployed-code relations and the other frame fields are preserved. For every
natural `fuel`, each `X(fuel+9)` interpreter call reduces to its own `X(fuel+1)`
call at that related boundary. This is not an assertion that the two residual
calls have equal outcomes.

The proof excludes entry reachability, jump execution, suffix behavior,
whole-contract equivalence, and formal correspondence with revm. Concrete replay
with `check-runtime` is separate evidence. Region certificates do not alter
`optimize` or `verify` acceptance.

The mask region is the following exact 18-byte pair:

```text
original:  6001600160e01b03166001600160e01b0319
candidate: 6001600160e01b03166400ffffffff60e01b
```

It checks 12 source instructions and nine candidate instructions, ending at
`entry_pc + 18` before the next instruction. Its input is `a :: tail`, with
arbitrary words and at most 1,020 tail items. At least 36 source gas is required;
the candidate costs 27, increasing its gas surplus by nine. Both output stacks
are `high :: (low AND a) :: tail`, where `low = 2^224 - 1` and `high = NOT low`.
The deployed-code relation permits an incoming execution-count offset; the source
executes three more instructions, increasing that offset by three. All other
frame fields are preserved subject to the same deployed-code and entry premises.
For every natural `fuel`, source `X(fuel+13)` and candidate `X(fuel+10)` reduce to
their respective `X(fuel+1)` calls. Their residual outcomes are not equated.
This is a source-gas-conditioned statement, not equivalence for every gas limit.

## Select a span

Supply an exclusive end byte offset to check multiple supported rewrites together:

```sh
cargo run --locked -- certify-runtime-region \
  --original runs/original.hex --candidate runs/candidate.hex \
  --entry-pc 0 --exit-pc 21 --out runs/span-1
```

Choose instruction boundaries in both images. A span may combine the mask pair
above with same-width `PUSHn 2^k; MUL` → `PUSHn k; SHL` rewrites (`k < 256`).
Unchanged `PUSH1`–`PUSH32`, `PUSH0`, `MUL`, `SHL`, `SHR`, `ADD`, `SUB`, `LT`, `EQ`, `ISZERO`, `AND`, `OR`, `NOT`, `SWAP1`–`SWAP16`, and `DUP1`
instructions may appear between them. The instruction at the end offset is not executed.

Spans may also contain unchanged, aligned `MSTORE` instructions, with supported
rewrites before or after each store. Memory reports expose `source_base_gas` and
`candidate_base_gas`, excluding expansion. The generated `sourceCost(initial state)`
function gives the full source gas requirement, including canonical expansion at
each store; base gas alone is insufficient. Memory equality is relative to the
pinned semantics, whose byte serialization includes opaque foreign-function helpers.
Other instructions are rejected.

The result records the required input stack size, maximum input stack size,
source gas requirement, and separate instruction counts. The proof permits
arbitrary input words and incoming gas/count offsets. It proves related boundary
states and separate residual interpreter calls, subject to those requirements;
it does not establish whole-contract or all-gas equivalence. Unchanged supported
spans are accepted with zero savings. Bytes outside the span remain independently
bound, without certification of their behavior.

Add `--through-jump` to execute the JUMP at `--exit-pc`. The span must
end in an unchanged literal `PUSH0`–`PUSH32`; the checker proves that its destination
is valid in both full images. This requires the checked-scanner setup above.
The result distinguishes `jump_pc` from the landing `exit_pc`, includes the JUMP’s
gas and instruction count, and stops before executing the destination JUMPDEST.
For memory paths, the gas requirement includes expansion plus the JUMP’s 8 gas.

Add `--through-halt` to execute an explicit `STOP`, `RETURN` or `REVERT` at `--exit-pc`
using the original upstream profile. It cannot be combined with `--through-jump`.
The proof gives paired success for STOP/RETURN or paired revert for REVERT, with
equal canonical output and related remaining gas. RETURN and REVERT require
`address :: size :: tail` at the body endpoint, a physical stack of at most 1,024
words, and `size < 2^64`; its gas requirement includes expansion after the body.
The result distinguishes `terminal_pc` from the resulting `exit_pc`. Entry
reachability, all-gas equivalence and memory-reader FFI correctness remain unproved.

Add `--from-call-entry` with `--through-halt` and `--entry-pc 0` to check
canonical call initialization and execution of a supported terminating
program. The program must accept an empty initial stack; RETURN/REVERT operands and
size bounds are checked by Lean. The theorem retains deployed-account linkage,
related account maps and sufficient source gas as premises. It proves paired
canonical `Ξ` success or revert and equal output, not transaction or all-gas
equivalence. REVERT results do not contain a returned machine state; `exit_pc`
describes the internal terminal step. Caller and transaction rollback are not proved.

Rust callers can use `region::certify_selected_span_through_jump` for jump spans,
`region::certify_span_through_jump` for pure spans,
`region::certify_selected_span_through_halt` for terminal spans,
`region::certify_selected_span_from_call_entry` for supported call-entry programs,
`region::certify_selected_span` for pure or memory spans,
`region::certify_span` for pure spans,
`region::certify_selected` for automatic pattern selection, or `region::certify`
for the power compiler region.

## Evidence

The output contains both full hex inputs, generated Lean sources, fresh compiled
modules, per-module logs, `environment.json`, and (only on success) `result.json`.
The result binds input bytes with Keccak-256 and records the precise region,
stack/gas conditions and unproved obligations. The mandatory axiom audit accepts
only `propext`, `Classical.choice`, and `Quot.sound`. Keep all generated evidence
local; it is not source repository content.

## Whole programs

`certify-runtime-whole` proves refinement for a complete runtime pair, not just
a region:

```sh
bash scripts/setup-upstream.sh --checked-scanner
cargo run --locked -- certify-runtime-whole \
  --original runs/original.hex --candidate runs/candidate.hex --out runs/whole-1
```

Theorem `xi_certificate`: run the code-execution function Ξ from a fresh call
frame whose current and original account maps differ only in the owner's
deployed code. If the original returns success or revert, the candidate returns
the same kind of result with the same output. On success the account maps stay
related, created accounts and substate are equal and the candidate keeps at
least as much gas; on revert it keeps at least as much gas. `whole_certificate`
states the same for the interpreter `X` from any related states at pc 0. There
is no trace, path or gas premise. Jump tables come from the checked-scanner
profile, computed by a byte-list scanner proved equal to it.

The generator lists every instruction reachable from pc 0 or a JUMPDEST and
emits one obligation per instruction, split across modules that each stay
within the per-module budget ([WholeProgram.lean](../../lean/upstream/WholeProgram.lean)).
Images up to the EIP-170 limit are accepted. They may differ only at same-width
`PUSHn 2^k; MUL` → `PUSHn k; SHL` sites and at one-hop threading sites
`PUSHn X; JUMPI` → `PUSHn Y; JUMPI` where `X` holds the unchanged trampoline
`JUMPDEST; PUSHm Y; JUMP`, and must have the same jump table.
Reachable instructions must be in the supported profile: stack, arithmetic,
comparison and bitwise opcodes; memory, `KECCAK256`, calldata, call-context and
block reads; `SLOAD`, `SSTORE`, `TLOAD`, `LOG0`–`LOG4`; `JUMP`, `JUMPI`,
`JUMPDEST`, `STOP`, `RETURN`, `REVERT` and undefined opcodes. Calls, creation,
`GAS`, code reads, `TSTORE` and `SELFDESTRUCT` are rejected.

Not proved: message-call (Θ) and transaction (Υ) equivalence, exceptional
original runs, stack-window rewrites and formal correspondence with revm.
