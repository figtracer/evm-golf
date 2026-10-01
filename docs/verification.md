# Verification and scoring

The current ruleset is `evm-golf-v1-cancun`. It fixes the puzzle semantics,
compiler, score definition, and proof policy used by the checked-in entries.

## Execution model

Inputs are unsigned 256-bit words. Arithmetic wraps modulo 2²⁵⁶. The supported
expression grammar is documented in the [command reference](cli.md#expressions).

The compiler emits the right operand first, then the left operand, then the
binary opcode. It reloads repeated variables from calldata and uses minimal PUSH
instructions for constants. A shared wrapper stores and returns one word.
There is no subexpression sharing through `DUP` or stack scheduling with `SWAP`.

## Lean proofs

Each accepted candidate has three universally quantified theorems:

1. Original and candidate expressions agree for all input words `x` and `y`.
2. Baseline bytecode computes the original expression.
3. Candidate bytecode computes the original expression.

The bytecode theorems interpret the actual emitted body bytes in
[lean/Model.lean](../lean/Model.lean), starting with an empty stack. The model
supports the compiler's small opcode subset and fails on unsupported instructions,
truncated immediates, and stack underflow. The common memory/RETURN wrapper is
outside the model.

The checker uses standard Lean lemmas and `bv_decide`. Native proof checking can
introduce native-evaluation axiom dependencies; these are printed in `Proof.log`.
This is not an axiom-free or kernel-only verification claim. Proofs using `sorry`
are rejected. The rule suite is generated from the same rule table used by the
optimizer, and each extracted candidate is checked independently.

## revm checks

The complete runtime is executed by revm under Cancun rules on 128 input pairs:
an 8×8 boundary grid and 64 deterministic full-width samples. Output words and gas
must match the reference evaluation and the static cost calculation.

The hand-written Lean model has not been formally connected to the Ethereum
specification or revm. These concrete executions supplement the model proofs;
they are not exhaustive EVM verification. Gas accounting is checked by revm and
is outside the Lean proof.

## Scoring

The extractor and leaderboard minimize expression-body gas, with byte size as
the tie-breaker. Body gas includes calldata loads. It excludes transaction
intrinsic gas and the fixed 13-gas return wrapper, including memory expansion.
Both excluded costs are identical for candidates given the same input.

Runtime byte counts include the wrapper. Deployment costs are not scored.
References are compiled with this project's tree compiler; improvements over
these synthetic baselines are not improvements over optimized Solidity output.

| Example | Replacement | Body gas | Runtime bytes |
| --- | --- | ---: | ---: |
| `x * 2` | `x << 1` | 13 → 11 | 11 → 11 |
| `(x xor y) xor y` | `x` | 23 → 5 | 16 → 8 |
| `(x & y) \| (x & ~y)` | `x` | 34 → 5 | 20 → 8 |
| `~x \| ~y` | `~(x & y)` | 20 → 17 | 14 → 13 |
| `(x * 2) + (y - y)` | `x << 1` | 31 → 11 | 19 → 11 |

[Reproducible entries](../leaderboard/README.md) include the bytecode and proofs.

## Resource limits

| Resource | Limit |
| --- | ---: |
| Input expression | 4,096 bytes / 128 nodes |
| E-graph search | 10,000 nodes / 30 iterations / 2 seconds |
| Lean verification | 60 seconds per proof file |
| Campaign input | 64 proposals / 1 MiB |

These bounds keep local experiments manageable. Search limits can stop further
optimization; they do not waive candidate verification. A proof failure or timeout
never produces an accepted result. Search does not guarantee a global optimum.

## Supported scope

Storage, branches, calls, deployment behavior, exceptions, and general contract
equivalence are unsupported. Solidity checked arithmetic may revert where these
expressions wrap. A valid expression rewrite alone does not justify changing an
arbitrary Solidity contract.

The CLI is a local developer tool, not a sandbox for public code execution.
Submissions contain expression strings, not arbitrary Lean programs or bytecode.
Maintainers should use the trusted checker described in
[Contributing](../CONTRIBUTING.md#puzzle-solutions).
