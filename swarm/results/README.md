# Campaign results

Ruleset: `evm-golf-v1-cancun`. 21 proposals: 21 verified, 0 unverified.

[Rankings and proofs](leaderboard/README.md) · [Machine-readable results](campaign.json) · [Replay inputs](proposals.json)

Unverified includes invalid inputs, failed proofs, timeouts and operational failures.
It does not by itself establish inequivalence. Only verified candidates are ranked.

## Best verified score per puzzle

Body gas; ties are broken by runtime byte size. The baseline is the fixed
reference expression compiled by this prototype, not optimized Solidity.

| Puzzle | Reference gas | E-graph gas | Best proposal gas | Proposal bytes |
| --- | ---: | ---: | ---: | ---: |
| [double](egraph/double/result.json) | 13 | 11 | 11 | 11 |
| [xor-cancel](egraph/xor-cancel/result.json) | 23 | 5 | 5 | 8 |
| [mask-partition](egraph/mask-partition/result.json) | 34 | 5 | 5 | 8 |
| [demorgan](egraph/demorgan/result.json) | 20 | 17 | 17 | 13 |
| [combined](egraph/combined/result.json) | 31 | 11 | 11 | 11 |
| [carry-add](egraph/carry-add/result.json) | 37 | 37 | 14 | 12 |
| [masked-select](egraph/masked-select/result.json) | 31 | 31 | 26 | 18 |

## Attempts

| ID | Author | Puzzle | Outcome |
| --- | --- | --- | --- |
| attempt-001 | swarm-algebra | double | verified |
| attempt-002 | swarm-algebra | xor-cancel | verified |
| attempt-003 | swarm-algebra | mask-partition | verified |
| attempt-004 | swarm-algebra | demorgan | verified |
| attempt-005 | swarm-algebra | combined | verified |
| attempt-006 | swarm-algebra | carry-add | verified |
| attempt-007 | swarm-algebra | masked-select | verified |
| attempt-008 | swarm-bitwise | double | verified |
| attempt-009 | swarm-bitwise | xor-cancel | verified |
| attempt-010 | swarm-bitwise | mask-partition | verified |
| attempt-011 | swarm-bitwise | demorgan | verified |
| attempt-012 | swarm-bitwise | combined | verified |
| attempt-013 | swarm-bitwise | carry-add | verified |
| attempt-014 | swarm-bitwise | masked-select | verified |
| attempt-015 | swarm-cost | double | verified |
| attempt-016 | swarm-cost | xor-cancel | verified |
| attempt-017 | swarm-cost | mask-partition | verified |
| attempt-018 | swarm-cost | demorgan | verified |
| attempt-019 | swarm-cost | combined | verified |
| attempt-020 | swarm-cost | carry-add | verified |
| attempt-021 | swarm-cost | masked-select | verified |
