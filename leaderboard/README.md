# EVM Golf leaderboard

Ruleset: `evm-golf-v2-cancun`. Lower body gas wins; runtime bytes break ties.
Every row was freshly verified with Lean and cross-checked with revm.
These are synthetic expression puzzles, not comparisons against solc.

## Double a word

`double` — baseline: 13 gas, 11 runtime bytes.

| Rank | Author | Gas | Bytes | Saved gas | Candidate | Evidence |
| ---: | --- | ---: | ---: | ---: | --- | --- |
| 1 | reference | 11 | 11 | 2 | `(shl1 x)` | [proof](double-reference/Proof.lean) · [result](double-reference/result.json) |

## Cancel repeated XOR

`xor-cancel` — baseline: 23 gas, 16 runtime bytes.

No submissions yet.

## Recombine complementary masks

`mask-partition` — baseline: 34 gas, 20 runtime bytes.

No submissions yet.

## Share a complement

`demorgan` — baseline: 20 gas, 14 runtime bytes.

No submissions yet.

## Combine arithmetic identities

`combined` — baseline: 31 gas, 19 runtime bytes.

No submissions yet.

## Recognize carry arithmetic

`carry-add` — baseline: 37 gas, 22 runtime bytes.

| Rank | Author | Gas | Bytes | Saved gas | Candidate | Evidence |
| ---: | --- | ---: | ---: | ---: | --- | --- |
| 1 | reference | 14 | 12 | 23 | `(+ x y)` | [proof](carry-reference/Proof.lean) · [result](carry-reference/result.json) |

## Select with a constant mask

`masked-select` — baseline: 31 gas, 19 runtime bytes.

| Rank | Author | Gas | Bytes | Saved gas | Candidate | Evidence |
| ---: | --- | ---: | ---: | ---: | --- | --- |
| 1 | reference | 26 | 18 | 5 | `(xor 255 (and x (xor 255 y)))` | [proof](select-reference/Proof.lean) · [result](select-reference/result.json) |
