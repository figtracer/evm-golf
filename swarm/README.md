# Three-agent campaign

Run date: 2026-10-01. Checker baseline: `aba4a7a06ffe976141bca699a36ef92ecf1ed72c`.
Ruleset: `evm-golf-v1-cancun`. The scoring code, puzzle specifications, rewrite
rules and Lean proof policy were unchanged for this run.

Three actual Codex collaboration subagents participated concurrently, inheriting
the session model with no model override. They used different strategy prompts:

| Participant | Strategy |
| --- | --- |
| swarm-algebra | Algebraic simplification and composition |
| swarm-bitwise | Boolean identities, complementary masks and carry arithmetic |
| swarm-cost | Gas costs and short candidate expressions |

Each agent received the same seven puzzles, the repository documentation, and
permission for at most ten local checker attempts. Each was asked to return one
best candidate per puzzle in the existing Submission JSON format. They could
read the existing solutions and were forbidden from changing the checker or
puzzles. No external model API, wallet or paid compute was used by the repo.

All agents reported seven checker attempts and seven accepted proposals. This
archive contains the 21 returned candidates, independently rechecked by the
campaign command. Agent deliberation is not archived or treated as proof.

**Outcome:** all three tied the three populated reference records. They supplied
entries for four previously empty puzzles. No agent improved an existing record.
The agents beat the current e-graph on carry-add and masked-select by using
identities absent from its 22-rule table. That is a limitation of this particular
rule set, not evidence that agents generally outperform e-graphs or SMT solvers.

[Verified report and e-graph comparison](results/README.md) · [Exact inputs](proposals.json)

This is an informed smoke test, not a blind evaluation, multi-model benchmark,
novel-optimization claim, or proof that any candidate is globally optimal.

## Replay verification

```sh
cargo run --locked -- campaign --proposals swarm/proposals.json --out runs/replay-1
```

Replay does not contact a language model. It verifies the saved expressions,
records failed attempts without aborting the batch, ranks accepted entries, and
runs the built-in e-graph against all seven puzzles. Model-generated proposals
and deterministic replay are distinct steps.

## Run another live swarm

Use your agent host to launch three independent workers with the strategy roles
above and the contestant prompt below. Give each a separate output directory and
a fixed local test budget. Collect their JSON arrays into one array, then pass it
to `campaign`. This repository does not bundle provider credentials, an LLM SDK,
or an unattended agent daemon.

> Read AGENTS.md, README.md and challenges.json. For each puzzle, propose the
> cheapest equivalent expression you can find using the supported grammar.
> Use your assigned strategy. Test at most ten candidates with the existing
> `evm-golf submit` command in unique temporary directories. Do not change the
> compiler, puzzle, rule table or proof checker. Return seven Submission objects
> in a JSON array and state any failures or timeouts. Existing reference entries
> are visible; do not claim blind discovery or novelty. Never call a paid API or
> publish changes. The coordinator will independently reverify your output.
