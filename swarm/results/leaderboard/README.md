# EVM Golf leaderboard

Ruleset: `evm-golf-v1-cancun`. Lower body gas wins; runtime bytes break ties.
Every row was freshly verified with Lean and cross-checked with revm.
These are synthetic expression puzzles, not comparisons against solc.

## Double a word

`double` — baseline: 13 gas, 11 runtime bytes.

| Rank | Author | Gas | Bytes | Saved gas | Candidate | Evidence |
| ---: | --- | ---: | ---: | ---: | --- | --- |
| 1 | swarm-algebra | 11 | 11 | 2 | `(shl1 x)` | [proof](attempt-001/Proof.lean) · [result](attempt-001/result.json) |
| 1 | swarm-bitwise | 11 | 11 | 2 | `(shl1 x)` | [proof](attempt-008/Proof.lean) · [result](attempt-008/result.json) |
| 1 | swarm-cost | 11 | 11 | 2 | `(shl1 x)` | [proof](attempt-015/Proof.lean) · [result](attempt-015/result.json) |

## Cancel repeated XOR

`xor-cancel` — baseline: 23 gas, 16 runtime bytes.

| Rank | Author | Gas | Bytes | Saved gas | Candidate | Evidence |
| ---: | --- | ---: | ---: | ---: | --- | --- |
| 1 | swarm-algebra | 5 | 8 | 18 | `x` | [proof](attempt-002/Proof.lean) · [result](attempt-002/result.json) |
| 1 | swarm-bitwise | 5 | 8 | 18 | `x` | [proof](attempt-009/Proof.lean) · [result](attempt-009/result.json) |
| 1 | swarm-cost | 5 | 8 | 18 | `x` | [proof](attempt-016/Proof.lean) · [result](attempt-016/result.json) |

## Recombine complementary masks

`mask-partition` — baseline: 34 gas, 20 runtime bytes.

| Rank | Author | Gas | Bytes | Saved gas | Candidate | Evidence |
| ---: | --- | ---: | ---: | ---: | --- | --- |
| 1 | swarm-algebra | 5 | 8 | 29 | `x` | [proof](attempt-003/Proof.lean) · [result](attempt-003/result.json) |
| 1 | swarm-bitwise | 5 | 8 | 29 | `x` | [proof](attempt-010/Proof.lean) · [result](attempt-010/result.json) |
| 1 | swarm-cost | 5 | 8 | 29 | `x` | [proof](attempt-017/Proof.lean) · [result](attempt-017/result.json) |

## Share a complement

`demorgan` — baseline: 20 gas, 14 runtime bytes.

| Rank | Author | Gas | Bytes | Saved gas | Candidate | Evidence |
| ---: | --- | ---: | ---: | ---: | --- | --- |
| 1 | swarm-algebra | 17 | 13 | 3 | `(not (and x y))` | [proof](attempt-004/Proof.lean) · [result](attempt-004/result.json) |
| 1 | swarm-bitwise | 17 | 13 | 3 | `(not (and x y))` | [proof](attempt-011/Proof.lean) · [result](attempt-011/result.json) |
| 1 | swarm-cost | 17 | 13 | 3 | `(not (and x y))` | [proof](attempt-018/Proof.lean) · [result](attempt-018/result.json) |

## Combine arithmetic identities

`combined` — baseline: 31 gas, 19 runtime bytes.

| Rank | Author | Gas | Bytes | Saved gas | Candidate | Evidence |
| ---: | --- | ---: | ---: | ---: | --- | --- |
| 1 | swarm-algebra | 11 | 11 | 20 | `(shl1 x)` | [proof](attempt-005/Proof.lean) · [result](attempt-005/result.json) |
| 1 | swarm-bitwise | 11 | 11 | 20 | `(shl1 x)` | [proof](attempt-012/Proof.lean) · [result](attempt-012/result.json) |
| 1 | swarm-cost | 11 | 11 | 20 | `(shl1 x)` | [proof](attempt-019/Proof.lean) · [result](attempt-019/result.json) |

## Recognize carry arithmetic

`carry-add` — baseline: 37 gas, 22 runtime bytes.

| Rank | Author | Gas | Bytes | Saved gas | Candidate | Evidence |
| ---: | --- | ---: | ---: | ---: | --- | --- |
| 1 | swarm-algebra | 14 | 12 | 23 | `(+ x y)` | [proof](attempt-006/Proof.lean) · [result](attempt-006/result.json) |
| 1 | swarm-bitwise | 14 | 12 | 23 | `(+ x y)` | [proof](attempt-013/Proof.lean) · [result](attempt-013/result.json) |
| 1 | swarm-cost | 14 | 12 | 23 | `(+ x y)` | [proof](attempt-020/Proof.lean) · [result](attempt-020/result.json) |

## Select with a constant mask

`masked-select` — baseline: 31 gas, 19 runtime bytes.

| Rank | Author | Gas | Bytes | Saved gas | Candidate | Evidence |
| ---: | --- | ---: | ---: | ---: | --- | --- |
| 1 | swarm-algebra | 26 | 18 | 5 | `(xor 255 (and x (xor 255 y)))` | [proof](attempt-007/Proof.lean) · [result](attempt-007/result.json) |
| 1 | swarm-bitwise | 26 | 18 | 5 | `(xor 255 (and x (xor y 255)))` | [proof](attempt-014/Proof.lean) · [result](attempt-014/result.json) |
| 1 | swarm-cost | 26 | 18 | 5 | `(xor 255 (and x (xor y 255)))` | [proof](attempt-021/Proof.lean) · [result](attempt-021/result.json) |
