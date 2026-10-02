# Documentation

EVM Golf provides a CLI and Rust library for optimizing and verifying small
EVM expressions. Start with the setup guide, then choose a workflow.

| Guide | Contents |
| --- | --- |
| [Getting started](getting-started.md) | Build, toolchains, first optimization |
| [Runtime bytecode](runtime.md) | Contract input, static jumps, local proofs, execution cases |
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
