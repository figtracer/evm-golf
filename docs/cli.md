# Command reference

Run commands from the checkout root with `cargo run --locked -- <command>`.
The compiled binary is also available at `target/debug/evm-golf`.
Every `--out` directory must be new; existing output is never overwritten.

| Command | Purpose |
| --- | --- |
| `optimize <expression> --out <dir>` | Search for a cheaper expression, then verify it |
| `check <original> <candidate> --out <dir>` | Verify an independently proposed replacement |
| `challenges` | Print the fixed puzzle specifications as JSON |
| `submit <challenge> <candidate> --author <name> --out <dir>` | Verify a puzzle solution and save a submission |
| `leaderboard --submissions <dir> --out <dir>` | Reverify submissions and generate Markdown and JSON rankings |
| `campaign --proposals <file> --out <dir>` | Verify a batch and compare it with e-graph search |
| `rules --out <dir>` | Prove the built-in rewrite rules at 256-bit width |
| `demo --out <dir>` | Run five example optimizations and save their scores |

`leaderboard` defaults to `--submissions submissions`. `demo` defaults to
`--out runs/demo`. Use `<command> --help` for argument details.

## Expressions

Expressions use prefix notation and unsigned wrapping 256-bit words.

| Syntax | Meaning |
| --- | --- |
| `x`, `y` | Input words at calldata offsets 0 and 32 |
| `0`, `256`, … | Unsigned constants below 2²⁵⁶ |
| `(+ a b)`, `(- a b)`, `(* a b)` | Arithmetic modulo 2²⁵⁶ |
| `(and a b)`, `(or a b)`, `(xor a b)`, `(not a)` | Bitwise operations |
| `(shl1 a)` | Left shift by one, discarding overflow |

For example:

```sh
cargo run --locked -- check '(xor (xor x y) y)' 'x' --out runs/check-1
```

A false replacement fails verification and produces no accepted result:

```sh
cargo run --locked -- check '(+ x 1)' 'x' --out runs/rejected-1
```

## Submissions

The checker chooses the reference from [challenges.json](../challenges.json).
A candidate cannot supply its own reference or claim its own score.

```sh
cargo run --locked -- submit double '(shl1 x)' --author alice --out runs/alice-double
```

The generated `submission.json` uses this format:

```json
{
  "ruleset": "evm-golf-cancun",
  "challenge": "double",
  "author": "alice",
  "candidate": "(shl1 x)"
}
```

Author names and submission directory names use 1–64 ASCII letters, digits,
hyphens or underscores. Names are self-reported attribution. Unknown JSON fields
and rulesets are rejected. Keep entries local; see [Leaderboards](#leaderboards)
to collect and rank them.

## Leaderboards

Collect verified entries in an ignored local directory, then generate a board:

```sh
cargo run --locked -- submit double '(shl1 x)' --author alice --out submissions/alice-double
cargo run --locked -- leaderboard --submissions submissions --out runs/board-1
```

Entries and generated scores, proofs, and logs belong to the leaderboard output,
not source-control contributions. `submissions/`, `leaderboard/`, and `runs/` are
ignored. The CLI generates local files; it does not host or publish a leaderboard.

The command reads immediate child directories containing `submission.json`. It
rechecks every input and ignores saved score files. One invalid entry prevents
the final board from being written; intermediate evidence remains for diagnosis.

The output includes `README.md`, `leaderboard.json`, and per-entry proofs and
results. Rank is per puzzle: body gas first, then runtime byte size. Exact ties
share rank. Every submission appears, including ties and candidates worse than
the baseline. [Scoring details](verification.md#scoring).

## Campaigns

A proposal file is a JSON array of submission objects using the same schema.
For example, save a local proposal and verify it:

```sh
mkdir -p runs
cat > runs/proposals.json <<'JSON'
[{"ruleset":"evm-golf-cancun","challenge":"double","author":"example","candidate":"(shl1 x)"}]
JSON
cargo run --locked -- campaign --proposals runs/proposals.json --out runs/campaign-1
```

Campaigns continue past individual unverified proposals and record each outcome
in `campaign.json` after each attempt. An interrupted run retains the latest complete
snapshot; replay into a fresh output directory. Verified entries are rechecked through the leaderboard path;
the command also attempts an independently verified e-graph result for every puzzle.
An unavailable comparison is labeled `unverified` and links to its error log.
`README.md` contains the comparison and links to evidence.

A completed batch may contain unverified entries. These can reflect invalid
inputs, failed proofs, timeouts, or operational errors; they do not automatically
establish inequivalence. Malformed batch JSON, output-write failures, or failure
to reverify accepted entries abort the run. An optimizer comparison failure does
not discard the campaign report. See the report and exit status.

Replay makes no model API calls. Proposal generation takes place in the agent
host. Keep proposal batches and run artifacts local.

## Rule verification

```sh
cargo run --locked -- rules --out runs/rules-1
```

This generates a Lean theorem for every rule in the Rust rule table. The saved
log includes each theorem's axiom dependencies. Read the
[proof policy](verification.md#lean-proofs) before interpreting the result.
