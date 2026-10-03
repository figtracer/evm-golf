# Documentation

EVM Golf provides a CLI and Rust library for optimizing and verifying small
EVM expressions and supported contract runtimes. Start with the setup guide, then
choose a workflow.

| Guide | Contents |
| --- | --- |
| [Getting started](getting-started.md) | Build, toolchains, first optimization |
| [Runtime bytecode](runtime.md) | Compact/fixed-layout optimization, selected rewrite plans, artifact proofs, account-fixture replay |
| [Internal-region certificates](regions.md) | Separate upstream semantics proofs, setup and explicit conditions |
| [Commands](cli.md) | Expressions, submissions, leaderboards, campaigns |
| [Verification and scoring](verification.md) | Semantics, proof boundary, gas accounting, limits |
| [Development](dev/README.md) | Repository layout, checks, compatibility |
| [Contributing](../CONTRIBUTING.md) | Code changes, puzzle solutions, proof research |
| [Agent guide](../AGENTS.md) | Contestant instructions and batch proposals |

## Challenges and leaderboards

[Challenge definitions](../challenges.json) are checked in. Use the
[leaderboard command](cli.md#leaderboards) to generate rankings and verification
evidence from local submissions. Entries, results, proofs, and logs stay out of
the source repository.
