# evm-golf

A local experiment for the Frontiers idea: **search for cheaper EVM expressions,
prove them with Lean, and score the emitted bytecode with revm.**

Rust's `egg` applies 22 rewrite rules to small expressions. The extractor chooses
the lowest modeled gas cost, breaking ties by byte size. Lean checks every
selected result independently, including the emitted expression-body bytecode.
Only then does revm cross-check execution and gas and the CLI save an accepted
`result.json`.

This is a working foundation for agent experiments. Search is currently a
deterministic e-graph, not an LLM swarm. Agents can already propose expressions
through the `check` command. A GitHub-readable leaderboard is generated from
verified submissions. There is no hosted submission service.

**[Leaderboard](leaderboard/README.md) · [Puzzles](challenges.json) · [Agent guide](AGENTS.md) · [Contributing](CONTRIBUTING.md)**

## Play

After the setup below, list puzzles, submit a candidate, and recreate the board:

```sh
cargo run --locked -- challenges
cargo run --locked -- submit double '(shl1 x)' --author your-name --out runs/your-entry
cargo run --locked -- leaderboard --submissions submissions --out runs/your-board
```

To join the checked-in board, contribute the generated `submission.json` under
`submissions/<unique-id>/`. The checker selects the reference by challenge ID,
proves correctness, and independently measures gas. It ignores saved score files.
Leaderboard generation rechecks every entry and writes Markdown, JSON, bytecode
and proofs. Any invalid entry prevents the final board from being written.

Seven fixed puzzles are included, with three clearly labeled reference entries.
Ranking is per puzzle: lower body gas first, then runtime bytes. Exact ties share
rank. The `evm-golf-v1-cancun` ruleset fixes the current puzzle and checker policy.
The checked-in board is a snapshot; regeneration requires a fresh output directory.
See CONTRIBUTING.md for submission review and the separate proof-research track.

## Try it

Requires Rust/Cargo and Lean **4.34.0**. The local setup script downloads the
official Lean binary into `.tools/lean`; it needs `curl`, `tar`, and `zstd`.
Alternatively, set `LEAN` to an existing 4.34.0 binary. Dependencies are locked in
`Cargo.lock`; this checkout was tested with Rust 1.98.0.

```sh
bash scripts/setup-lean.sh
cargo run --locked -- demo --out runs/my-demo
cargo run --locked -- optimize '(+ (* x 2) (- y y))' --out runs/my-puzzle
cargo run --locked -- rules --out runs/rules
```

Every output directory must be new. Reusing one fails instead of overwriting
proofs or mixing old and new results.

Try proposing your own replacement:

```sh
cargo run --locked -- check '(xor (xor x y) y)' 'x' --out runs/my-candidate

# Deliberately false: fails in Lean and produces no result.json.
cargo run --locked -- check '(+ x 1)' 'x' --out runs/wrong-candidate
```

Each accepted run contains `Proof.lean`, `Proof.log` (including the theorem axiom
dependencies), and `result.json` with expressions, bytecode, gas and byte counts.
The demo also writes `scores.json`. Recheck a proof directly with:

```sh
.tools/lean/bin/lean runs/my-puzzle/Proof.lean
```

## What is being optimized?

Inputs are prefix expressions using unsigned wrapping 256-bit words:

| Syntax | Meaning |
| --- | --- |
| `x`, `y` | Two input words from calldata offsets 0 and 32 |
| `0`, `256`, … | Unsigned constants below 2²⁵⁶ |
| `(+ a b)`, `(- a b)`, `(* a b)` | Arithmetic modulo 2²⁵⁶ |
| `(and a b)`, `(or a b)`, `(xor a b)`, `(not a)` | Bitwise operations |
| `(shl1 a)` | Shift left by one, discarding overflow |

The compiler emits the right operand first for binary operations, then the left
operand, then the opcode. It reloads repeated variables from calldata; it does
not yet share subexpressions with `DUP`. Constants use minimal PUSH instructions.
A shared wrapper stores and returns the single result word.

Measured examples from the included demo:

| Puzzle | Replacement | Body gas before → after | Runtime bytes before → after |
| --- | --- | ---: | ---: |
| `x * 2` | `x << 1` | 13 → 11 | 11 → 11 |
| `(x xor y) xor y` | `x` | 23 → 5 | 16 → 8 |
| `(x & y) \| (x & ~y)` | `x` | 34 → 5 | 20 → 8 |
| `~x \| ~y` | `~(x & y)` | 20 → 17 | 14 → 13 |
| `(x * 2) + (y - y)` | `x << 1` | 31 → 11 | 19 → 11 |

These are synthetic examples against this project's deliberately simple code
generator, **not improvements over optimized Solidity output**. Body gas includes
input loads and excludes the fixed 13-gas return wrapper and transaction intrinsic
gas. Both excluded costs are identical between candidates for the same input.
Runtime byte counts include the wrapper. Deployment costs are not scored.

## What the proof does—and its boundary

Every accepted candidate gets three universally quantified Lean theorems:

1. The original and candidate expressions agree for all `x` and `y`.
2. The baseline bytecode body computes the original expression.
3. The candidate bytecode body computes the original expression.

The last two interpret the **actual emitted bytes** in
[`lean/Model.lean`](lean/Model.lean), starting with an empty stack. The model
handles this small opcode subset and fails on unsupported instructions or stack
underflow. `rules` generates and checks a theorem for each rule from the same Rust
rule table used by the search.

Lean uses standard lemmas and `bv_decide`. Its native proof-checking machinery
introduces native-evaluation axiom dependencies, visible in the saved log; this
is not an axiom-free or kernel-only verification claim. No `sorry` is accepted.

The hand-written Lean model has not been formally connected to the Ethereum
specification or revm. The common memory/RETURN wrapper and gas accounting are
outside the Lean proof. revm, pinned to **Cancun**, independently checks the full
runtime on 128 input pairs: an 8×8 boundary grid and 64 deterministic full-width
samples. This supplements the model proof; it is not exhaustive EVM verification.

No storage, branches, calls, deployment behavior, exceptions or general contract
equivalence are supported. Expressions have mathematical wrapping behavior;
Solidity checked arithmetic can instead revert. Don't apply these rewrites to
arbitrary Solidity contracts on the strength of this experiment.

Search is capped at 10,000 e-graph nodes, 30 iterations and two seconds. Input is
capped at 4,096 bytes / 128 nodes. Lean gets 60 seconds per proof file. These keep
local puzzles bounded; timeouts and unproved results fail closed. Search does not
promise a global optimum. This CLI is a trusted local developer tool, not a
sandbox for running public submissions.

## Development

```sh
cargo fmt --check
cargo clippy --locked --all-targets -- -D warnings
cargo test --locked
cargo test --locked -- --ignored
```

The second test command actually runs Lean. It covers acceptance of a valid
optimization, rejection of a false equivalence, rejection of wrong bytecode even
when the expressions match, refusal to overwrite evidence, and all 22 rules.
The normal suite cross-checks every supported operation and PUSH boundaries
against revm, including wrapping arithmetic and SUB operand order.

`src/expr.rs` owns the grammar, rules and cost-guided search; `src/evm.rs` owns
code generation and revm execution; `src/proof.rs` generates and checks proofs.

## Next experiments

Let agents propose replacements against the same fixed puzzles using `submit`.
The first five puzzles are warmups; carry-add and masked-select require identities
outside the built-in e-graph rules. The reference entries are examples, not claims
of novel optimizations. Future work includes stack reuse (`DUP`/`SWAP`), real
compiler fragments, agent-written proof lemmas, and a measured Lean/Z3/cvc5 study.

Inspired by [zkGolf](https://zk.golf/) and its
[public challenge repo](https://github.com/zksecurity/zk-golf-challenges).
This independent prototype uses a smaller expression language and its own stated
proof policy. It does not inherit zkGolf's verifier or axiom acceptance rules.

Built with [egg](https://github.com/egraphs-good/egg),
[Lean](https://github.com/leanprover/lean4), and
[revm](https://github.com/bluealloy/revm).
