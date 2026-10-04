# Internal-region certificates

`certify-runtime-region` checks a selected compiler prefix against the canonical
interpreter in pinned [EVMYulLean](https://github.com/NethermindEth/EVMYulLean/tree/047f63070309f436b66c61e276ab3b6d1169265a).
It proves conditional reductions to related internal states. It does not prove
that a transaction reaches the region or that the remaining execution is equivalent.

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
Lean 4.34 expression and runtime rewrite gates are unchanged.

## Supported regions

The command selects one of two exact byte patterns. The power region is:

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
with `check-runtime` is separate evidence. Region certificates are not expression
leaderboard entries and do not alter `optimize-runtime` acceptance.

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

The public Rust `region::certify` function and its power-region JSON remain
unchanged. `region::certify_selected`, used by the CLI, also accepts the mask pair.
Its mask JSON records separate instruction counts, execution-count offset,
candidate gas cost and the same proof limitations; it has no `pushed_destination`.
Only mask checks compile the additional mask support modules. Surrounding bytes
are independently bound and may differ, as for the power region.

## Evidence

The output contains both full hex inputs, generated Lean sources, fresh compiled
modules, per-module logs, `environment.json`, and—only on success—`result.json`.
The result binds input bytes with Keccak-256 and records the precise region,
stack/gas conditions and unproved obligations. The mandatory axiom audit accepts
only `propext`, `Classical.choice`, and `Quot.sound`. Keep all generated evidence
local; it is not source repository content.
