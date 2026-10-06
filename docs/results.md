# Results

We ran `optimize` with default settings on 36 builds of real token contracts:
ERC20 and ERC4626 vaults from OpenZeppelin, Solady and Solmate, compiled with
legacy and via-IR, optimizer off, 200 and 10,000 runs. Every change was proved
and replayed.

## Gas saved each time a function is called

| Function | Usual saving | Best saving | Builds tested |
| --- | ---: | ---: | ---: |
| `transfer` | 14 gas | 33 gas | 18 |
| `transferFrom` | 15.5 gas | 44 gas | 18 |
| `approve` | 9 gas | 23 gas | 18 |
| `balanceOf` | 3 gas | 15 gas | 36 |
| `deposit` | 6 gas | 128 gas | 18 |
| `mint` | 10 gas | 116 gas | 18 |
| `withdraw` | 10.5 gas | 182 gas | 18 |
| `redeem` | 10.5 gas | 118 gas | 18 |

How to read a row: on a usual build, each `transfer` call costs 14 gas less
after optimization. On the best build, it costs 33 gas less. "Usual" is the
median over the builds whose test transactions call that function.

Builds compiled without the optimizer save the most, mostly from jump
threading. Code that was already optimized (Balancer vault, Uniswap V3 pool)
still saves 6 to 10 gas per transaction. These numbers are execution gas only.
The fixed transaction cost and storage writes stay the same.

## Examples of accepted rewrites

| Before | After | Gas saved each time it runs |
| --- | --- | ---: |
| `PUSH1 0x20 DUP2 SWAP1` | `DUP1 PUSH2 0x0020` | 3 |
| `PUSH1 a PUSH1 0x20 SWAP1` | `PUSH1 0x20 PUSH2 a` | 3 |
| `POP PUSH2 c SWAP3 POP POP POP` | `POP POP POP POP PUSH3 c` | 3 |
| `PUSH2 X JUMPI`, X: `JUMPDEST PUSH2 Y JUMP` | `PUSH2 Y JUMPI` | 12, if the jump is taken |

The wider PUSH keeps every byte offset unchanged.
