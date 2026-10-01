# EVM Golf leaderboard

Ruleset: `evm-golf-v1-cancun`. Lower body gas wins; runtime bytes break ties.
Every row was freshly verified with Lean and cross-checked with revm.
These are synthetic expression puzzles, not comparisons against solc.

## Double a word

`double` — baseline: 13 gas, 11 runtime bytes.

| Rank | Author | Gas | Bytes | Saved gas | Candidate | Evidence |
| ---: | --- | ---: | ---: | ---: | --- | --- |
| 1 | reference | 11 | 11 | 2 | `(shl1 x)` | [proof](double-reference/Proof.lean) · [result](double-reference/result.json) |
| 1 | swarm-algebra | 11 | 11 | 2 | `(shl1 x)` | [proof](swarm-algebra-double/Proof.lean) · [result](swarm-algebra-double/result.json) |
| 1 | swarm-bitwise | 11 | 11 | 2 | `(shl1 x)` | [proof](swarm-bitwise-double/Proof.lean) · [result](swarm-bitwise-double/result.json) |
| 1 | swarm-cost | 11 | 11 | 2 | `(shl1 x)` | [proof](swarm-cost-double/Proof.lean) · [result](swarm-cost-double/result.json) |

## Cancel repeated XOR

`xor-cancel` — baseline: 23 gas, 16 runtime bytes.

| Rank | Author | Gas | Bytes | Saved gas | Candidate | Evidence |
| ---: | --- | ---: | ---: | ---: | --- | --- |
| 1 | swarm-algebra | 5 | 8 | 18 | `x` | [proof](swarm-algebra-xor-cancel/Proof.lean) · [result](swarm-algebra-xor-cancel/result.json) |
| 1 | swarm-bitwise | 5 | 8 | 18 | `x` | [proof](swarm-bitwise-xor-cancel/Proof.lean) · [result](swarm-bitwise-xor-cancel/result.json) |
| 1 | swarm-cost | 5 | 8 | 18 | `x` | [proof](swarm-cost-xor-cancel/Proof.lean) · [result](swarm-cost-xor-cancel/result.json) |

## Recombine complementary masks

`mask-partition` — baseline: 34 gas, 20 runtime bytes.

| Rank | Author | Gas | Bytes | Saved gas | Candidate | Evidence |
| ---: | --- | ---: | ---: | ---: | --- | --- |
| 1 | swarm-algebra | 5 | 8 | 29 | `x` | [proof](swarm-algebra-mask-partition/Proof.lean) · [result](swarm-algebra-mask-partition/result.json) |
| 1 | swarm-bitwise | 5 | 8 | 29 | `x` | [proof](swarm-bitwise-mask-partition/Proof.lean) · [result](swarm-bitwise-mask-partition/result.json) |
| 1 | swarm-cost | 5 | 8 | 29 | `x` | [proof](swarm-cost-mask-partition/Proof.lean) · [result](swarm-cost-mask-partition/result.json) |

## Share a complement

`demorgan` — baseline: 20 gas, 14 runtime bytes.

| Rank | Author | Gas | Bytes | Saved gas | Candidate | Evidence |
| ---: | --- | ---: | ---: | ---: | --- | --- |
| 1 | swarm-algebra | 17 | 13 | 3 | `(not (and x y))` | [proof](swarm-algebra-demorgan/Proof.lean) · [result](swarm-algebra-demorgan/result.json) |
| 1 | swarm-bitwise | 17 | 13 | 3 | `(not (and x y))` | [proof](swarm-bitwise-demorgan/Proof.lean) · [result](swarm-bitwise-demorgan/result.json) |
| 1 | swarm-cost | 17 | 13 | 3 | `(not (and x y))` | [proof](swarm-cost-demorgan/Proof.lean) · [result](swarm-cost-demorgan/result.json) |

## Combine arithmetic identities

`combined` — baseline: 31 gas, 19 runtime bytes.

| Rank | Author | Gas | Bytes | Saved gas | Candidate | Evidence |
| ---: | --- | ---: | ---: | ---: | --- | --- |
| 1 | swarm-algebra | 11 | 11 | 20 | `(shl1 x)` | [proof](swarm-algebra-combined/Proof.lean) · [result](swarm-algebra-combined/result.json) |
| 1 | swarm-bitwise | 11 | 11 | 20 | `(shl1 x)` | [proof](swarm-bitwise-combined/Proof.lean) · [result](swarm-bitwise-combined/result.json) |
| 1 | swarm-cost | 11 | 11 | 20 | `(shl1 x)` | [proof](swarm-cost-combined/Proof.lean) · [result](swarm-cost-combined/result.json) |

## Recognize carry arithmetic

`carry-add` — baseline: 37 gas, 22 runtime bytes.

| Rank | Author | Gas | Bytes | Saved gas | Candidate | Evidence |
| ---: | --- | ---: | ---: | ---: | --- | --- |
| 1 | reference | 14 | 12 | 23 | `(+ x y)` | [proof](carry-reference/Proof.lean) · [result](carry-reference/result.json) |
| 1 | swarm-algebra | 14 | 12 | 23 | `(+ x y)` | [proof](swarm-algebra-carry-add/Proof.lean) · [result](swarm-algebra-carry-add/result.json) |
| 1 | swarm-bitwise | 14 | 12 | 23 | `(+ x y)` | [proof](swarm-bitwise-carry-add/Proof.lean) · [result](swarm-bitwise-carry-add/result.json) |
| 1 | swarm-cost | 14 | 12 | 23 | `(+ x y)` | [proof](swarm-cost-carry-add/Proof.lean) · [result](swarm-cost-carry-add/result.json) |

## Select with a constant mask

`masked-select` — baseline: 31 gas, 19 runtime bytes.

| Rank | Author | Gas | Bytes | Saved gas | Candidate | Evidence |
| ---: | --- | ---: | ---: | ---: | --- | --- |
| 1 | reference | 26 | 18 | 5 | `(xor 255 (and x (xor 255 y)))` | [proof](select-reference/Proof.lean) · [result](select-reference/result.json) |
| 1 | swarm-algebra | 26 | 18 | 5 | `(xor 255 (and x (xor 255 y)))` | [proof](swarm-algebra-masked-select/Proof.lean) · [result](swarm-algebra-masked-select/result.json) |
| 1 | swarm-bitwise | 26 | 18 | 5 | `(xor 255 (and x (xor y 255)))` | [proof](swarm-bitwise-masked-select/Proof.lean) · [result](swarm-bitwise-masked-select/result.json) |
| 1 | swarm-cost | 26 | 18 | 5 | `(xor 255 (and x (xor y 255)))` | [proof](swarm-cost-masked-select/Proof.lean) · [result](swarm-cost-masked-select/result.json) |
