# Contributing

Try a challenge from `challenges.json`, validate locally, and contribute a new
`submissions/<unique-id>/submission.json` in a pull request. The submission format
is demonstrated by the three reference entries. All candidates are expressions;
this version does not accept custom proof programs or arbitrary EVM bytecode.

Please describe how the replacement works and disclose human/AI assistance in
your PR. Starter code and reference entries were developed with OpenAI Codex.
Entries marked `reference` are project examples, not independent competitors.

The maintainer checks out the trusted checker, reviews submission JSON, copies
only the new JSON inputs, and runs the leaderboard command. Submitted changes to
the checker, challenge definitions, toolchain or dependencies need separate
review. There is no automatic GitHub Actions runner for untrusted submissions.

Generated evidence lives in `leaderboard/`; contributors need only submit JSON.
Regenerate into a fresh directory first, review the result, then update the
checked-in snapshot. Rankings list every submission, including ties and entries
that are worse than the baseline. Author names are self-reported.

## Proof research

We welcome real optimizer rewrite cases that Z3 or cvc5 struggle to finish.
Include the exact rule, bit width, preconditions, solver versions, invocation,
resource limits and observed result. For Lean comparisons, use the same statement
and record proof-generation time separately from proof-checking time. Classify
counterexamples, timeouts and unknown results separately from verified proofs.

The current Lean checker uses standard lemmas and bv_decide. It does not yet accept
agent-written lemmas, and it does not benchmark Z3 or cvc5. A corpus of difficult
rules and a controlled comparison are future experiments, not current claims.

## Scope

This is an independent Frontiers-inspired prototype. It is not an official
Paradigm or zkGolf project. The first five puzzles are warmups; carry-add and
masked-select exercise identities absent from the built-in rule table. More
realistic compiler fragments and stack reuse are welcome future work.
