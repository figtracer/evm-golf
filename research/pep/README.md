# Agent-written proofs versus SMT

This experiment tests the group-chat suggestion that agents writing Lean proofs
could establish rewrite rules that Z3 or cvc5 struggle with. It compares identical
256-bit expression equalities, then checks whether the guided proofs also verify
the bytecode emitted by EVM Golf.

The selected corpus tests standard modular algebra. It is not a collection of
hard production rules from an existing compiler.

## Findings

See the [recorded comparison](results/README.md) for individual timings and
[raw results](results/results.json) for every trial. These are local exploratory
measurements, not a general solver ranking.

- Z3 proved all six valid identities, including all four multiplication cases.
- Agent-written Lean proofs established the four multiplication identities using
  standard library lemmas. The automatic Lean tactic could not complete those
  cases within the comparison budget.
- cvc5 proved distributivity and multiplication cancellation, but reached the
  wall limit on difference of squares and the square expansion identity.
- The deliberately false square identity was never accepted. Reported
  counterexamples were replayed with the canonical Rust evaluator and revm.

This supports improving the Lean proof strategy for these cases. It does not
support the stronger claim that Lean plus an agent beats Z3. Much of the useful
work here is selecting existing algebraic lemmas instead of expanding symbolic
multiplications into bits.

## Proofs that transfer to bytecode

For example, for all wrapping 256-bit words:

```text
x * (y + 1) - x * y = x
```

The guided proof expands multiplication over addition and cancels the shared
term. The generated baseline bytecode theorem reduces directly by `rfl`; the
candidate bytecode theorem reuses the expression equality. This avoids asking
the bit-vector prover to rediscover the same identity for each theorem.

| Expression | Equivalent candidate | Body gas |
| --- | --- | ---: |
| `x*y + x*x` | `x*(y+x)` | 34 → 24 |
| `x*(y+1) - x*y` | `x` | 41 → 5 |
| `x*x - y*y` | `(x-y)*(x+y)` | 35 → 33 |
| `(x+y)*(x+y) - (x*x+y*y)` | `2*(x*y)` | 71 → 24 |

The [bytecode results](results/bytecode-results.json) record separate checks of
expression equivalence, baseline execution, and candidate execution against the
existing Lean model. Each valid pair also passes 128 concrete revm cases. Gas is
measured by the existing compiler/revm path and is not a Lean theorem. The common
return wrapper and full contract behavior remain outside this model.

These are research artifacts. They do not change the optimizer's rewrite table,
contest verifier, accepted submission format, ruleset, or leaderboard. In
particular, the current `check` command still uses its existing automatic proof
policy. Moving the guided strategy into that path requires a separately
versioned verifier change.

## Reproduce

Requires Rust, Python 3, Lean 4.34.0 from `scripts/setup-lean.sh`, and Z3/cvc5
executables. The recorded run used Z3 4.16.0 and cvc5 1.4.1. Obtain cvc5 from its
[official releases](https://github.com/cvc5/cvc5/releases); the tested macOS arm64
archive URL and checksum are in [cvc5-provenance.json](cvc5-provenance.json).
The runner does not install tools or use model APIs.

From the repository root, with `z3` and `cvc5` on PATH:

```sh
python3 -B research/pep/run.py --out runs/pep-1 --timeout 15 --repetitions 2
```

Use `--z3 /path/to/z3`, `--cvc5 /path/to/cvc5`, or `--lean /path/to/lean` to select
executables. `--case mul-cancel` restricts measured cases. Output directories must
be new. This runner uses POSIX process groups and supports macOS/Linux.

Generate the matched inputs without benchmarking:

```sh
cargo run --locked --example proof_cases -- research/pep/cases.json runs/pep-inputs 15
.tools/lean/bin/lean -j1 runs/pep-inputs/mul-cancel.guided.lean
.tools/lean/bin/lean -j1 runs/pep-inputs/mul-cancel.bytecode.lean
```

The final positional argument is the internal SAT timeout in seconds. The runner
rounds its wall budget up to a whole second for this value, so Lean's default
10-second SAT timeout cannot end a longer comparison early.

Replay a counterexample with Rust U256 arithmetic and the emitted EVM programs:

```sh
cargo run --locked --example proof_cases -- --replay research/pep/cases.json false-square-cross 1 1
```

Run the research regression checks:

```sh
cargo test --locked --example proof_cases
python3 -B -m unittest discover -s research/pep -p test_run.py -v
```

## Method

[cases.json](cases.json) is the shared corpus. The Rust example parses it through
EVM Golf's existing grammar and emits both Lean and SMT from the same expression
nodes. SMT asserts the negated equality in `QF_BV`; `unsat` establishes equality.
There are no preconditions, signed operations, or unbounded integer arithmetic.

The four methods are:

1. Z3, default solving configuration.
2. cvc5, default solving configuration with SMT-LIB input.
3. Lean automatic: the current verifier's `simp [BitVec.mul_comm]` followed by
   `bv_decide`, with the experiment's resource settings.
4. Lean guided: replay of the agent-authored proof. Add-zero uses `simp`; the
   carry-add and false controls use `bv_decide` in this column too.

Every trial runs sequentially in a fresh process. Timings include startup,
imports, proof elaboration/search, and checking. Each tool receives an untimed
warmup; method order rotates deterministically across cases and repetitions.
The recorded comparison uses two repetitions with a 15-second wall limit per
process group. Descendants are killed on timeout. Lean uses one worker and no
heartbeat limit; the external wall limit still applies. Other engine defaults
are retained. There is no memory cap, peak-memory measurement, or CPU pinning.
Timeout durations include process termination overhead and are censored results.

Guided replay timing **excludes proof authoring**. A Codex agent developed the
four algebraic proofs in two batch attempts over about 115 seconds, recorded in
[discovery.json](discovery.json). The bytecode transfer was a subsequent agent
experiment, recorded separately in [bytecode-discovery.json](bytecode-discovery.json).
These are single authoring observations, not repeated discovery benchmarks.

Solver versions, platform, source hashes, commands, exit codes, raw logs, and
axiom dependencies accompany the results. SAT model requests and concrete
counterexample replay run separately from the measured query. A missing model
or failed proof is never promoted to a checked result.

Raw SMT `unsat` answers have not been certificate-checked. Lean checks the guided
polynomial proofs using standard `propext`/`Quot.sound` dependencies. The automatic
lane and `bv_decide` controls can additionally depend on native evaluation; those
names are retained in the axiom reports. `sorry`, unrecognized axioms, and missing
requested theorem reports are rejected. Proof strings in this developer-owned
corpus are trusted reviewed source, not a sandboxed public proof-submission API.

The cases were chosen to exercise algebraic proof structure. There is no blind
holdout, solver tuning study, or agent-versus-human comparison. The useful next
research corpus would contain actual rules that timed out in a production
optimizer, with their precise semantics and preconditions preserved.
