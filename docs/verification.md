# Verification and scoring

The current ruleset is `evm-golf-cancun`. It fixes the puzzle semantics,
compiler, score definition, and proof policy used to verify leaderboard entries.
The tool is unreleased: entries are reverified against the current checker,
without release-version migrations.

## Execution model

Inputs are unsigned 256-bit words. Arithmetic wraps modulo 2²⁵⁶. The supported
expression grammar is documented in the [command reference](cli.md#expressions).

The compiler emits the right operand first, then the left operand, then the
binary opcode. Identical sibling expressions are evaluated once and duplicated
with `DUP1` when that improves gas or, at equal gas, byte size. Constants use
minimal PUSH instructions. A shared wrapper stores and returns one word.
Reuse is local to siblings; there is no general stack scheduling.

## Lean proofs

Each accepted candidate has three universally quantified theorems:

1. Original and candidate expressions agree for all input words `x` and `y`.
2. Baseline bytecode computes the original expression.
3. Candidate bytecode computes the original expression.

The bytecode theorems interpret the actual emitted body bytes in
[lean/Model.lean](../lean/Model.lean), starting with an empty stack. The model
supports the compiler's small opcode subset and fails on unsupported instructions,
truncated immediates, and stack underflow. The common memory/RETURN wrapper is
outside the model. Generated PUSH immediates are complete; the model rejects
truncated PUSH data, whereas legacy EVM execution zero-pads it.

Expression equality first tries simplification and `grind` for at most 15 seconds,
then a bounded algebra/`bv_decide` fallback within the same 60-second total budget.
A width-general shift lemma exposes doubling to arithmetic normalization.
Each attempt keeps its source and log; `Proof.lean` contains the successful proof.
The baseline body reduces directly to the reference expression. The candidate body reduces
to its own expression, then uses the symmetric equality theorem under the
returned stack value. This also supports equivalent expansions such as
`x → (x * 1) + 0`; the expression theorem is not rediscovered for each body.

Axiom reports are required for all expected theorems. The checker permits Lean's
standard foundational axioms and narrowly recognized theorem-local `bv_decide`
native dependencies, rejecting `sorry`, missing reports and unexpected axioms.
Dependencies appear in `Proof.log`; this is not an axiom-free or kernel-only
verification claim for expression proofs. Runtime certificates use a stricter
foundational-only policy. The rule suite comes from the optimizer's rule table, and
each extracted candidate is checked independently.

## revm checks

For expression commands, revm executes the complete runtime under Cancun on
128 input pairs: an 8×8 boundary grid and 64 deterministic full-width samples. Output words and gas
must match the reference evaluation and the static cost calculation.

The hand-written Lean model has not been formally connected to the Ethereum
specification or revm. These concrete executions supplement the model proofs;
they are not exhaustive EVM verification. Gas accounting is checked by revm and
is outside the Lean proof.

## Scoring

The leaderboard ranks expression-body gas, with runtime byte size as the
tie-breaker. E-graph extraction accounts for identical-sibling reuse, then compares
the emitted candidate with the original expression using the actual compiler.
It retains the original if extraction worsens that score. Body gas includes calldata
loads. It excludes transaction intrinsic gas and the fixed 13-gas return wrapper, including memory expansion.
Both excluded costs are identical for candidates given the same input.

Runtime byte counts include the wrapper. Deployment costs are not scored.
References are compiled with this project's compiler; improvements over
these synthetic baselines are not improvements over optimized Solidity output.

Generate a [leaderboard](cli.md#leaderboards) to view scores alongside their
bytecode and proof evidence. Results are kept outside the source repository.

## Resource limits

| Resource | Limit |
| --- | ---: |
| Input expression | 4,096 bytes / 128 nodes |
| E-graph search | 10,000 nodes / 30 iterations / 2 seconds |
| Lean proof attempts | 60 seconds per proof file, after toolchain version lookup |
| Campaign input | 64 proposals / 1 MiB |
| Runtime input file / compact fixture JSON | 1 MiB |
| Runtime replay batch | 256 transactions / 30 million gas per transaction / 300 million total gas per program |

These bounds keep local experiments manageable. Search limits can stop further
optimization; they do not waive candidate verification. A proof failure or timeout
never produces an accepted result. Search does not guarantee a global optimum.

## Supported scope

The expression model excludes storage, branches, calls, deployment behavior,
exceptions, and general contract equivalence. The separate
[runtime optimizer](runtime.md) preserves surrounding instructions while checking
local fragments and supplied execution cases. Fixed-layout mode additionally proves
exact reconstruction of the complete emitted artifact, its layout, and each site's
stack profile and bounded local stack behavior in complete instruction contexts,
with proofs tied to the exact replaced bytes. Compact-mode
relocation remains Rust-checked. Neither certificate proves full runtime execution.
Solidity checked arithmetic may revert where these expressions wrap. A valid expression rewrite alone does not justify changing an
arbitrary Solidity contract.

The CLI is a local developer tool, not a sandbox for public code execution.
Submissions contain expression strings, not arbitrary Lean programs or bytecode.
Maintainers should use the trusted checker described in
[Contributing](../CONTRIBUTING.md#puzzle-solutions).
