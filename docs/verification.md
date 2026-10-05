# Verification

A candidate is accepted only after both checks below pass. Neither alone is
enough, and together they are still not a whole-contract equivalence proof.

## Lean certificate

The checker generates the Lean source itself; no user-supplied Lean or proof
metadata is accepted. One certificate covers the whole runtime and proves:

- **Exact bytes.** The original and candidate byte arrays are embedded
  independently. Sorted, disjoint sites reconstruct the candidate, every other
  byte is unchanged, and lengths, instruction boundaries outside the sites,
  JUMPDEST positions and protected code-copy bytes agree.
- **Local equivalence.** For each site, the before and after instructions produce
  the same stack for arbitrary input words in a bounded 256-bit word model
  ([lean/Model.lean](../lean/Model.lean), [lean/Stack.lean](../lean/Stack.lean)).
  Underflow and overflow happen at the same incoming stack heights (0 to 1,024),
  and substitution holds under any completely decoded prefix and suffix
  ([lean/Composition.lean](../lean/Composition.lean)).

- **Jump threading.** In a control-flow model of PUSH, JUMPDEST, JUMP and JUMPI
  over the full images ([lean/Threading.lean](../lean/Threading.lean)), the
  candidate reaches in two steps the same program counter and stack that the
  original reaches after also running the trampoline, including the same stack
  faults, for every input stack. Jump destinations are computed from the bytes
  and proved equal in both images, and each trampoline is unchanged.

Only Lean's foundational axioms (`propext`, `Classical.choice`, `Quot.sound`)
may appear in the axiom report, and every expected theorem must be reported.

A separate developer command proves whole-program refinement of Ξ against
pinned EVMYulLean for call-free runtimes with the power rewrite
([regions](dev/regions.md#whole-programs)). It does not affect `optimize` or
`verify`.
The pinned toolchain is Lean 4.34.0. Each certificate must check within 60
seconds; any failure or timeout rejects the candidate.

The models erase gas and do not interpret calls, storage or memory. It does not
prove which stack heights the surrounding program reaches, or that the model
matches revm for every instruction.

## Replay

revm replays every supplied transaction on the original and the candidate with
the guards described in [runtime support](runtime.md#replay): identical outcomes,
outputs, logs, state and ordered call and storage effects, no exceptional halts,
and no increase in receipt gas.

## Not covered

- Inputs, states, callers and gas limits outside the supplied scenarios.
- Behavior that depends on remaining gas (for example SSTORE's 2,300-gas check
  or a call crossing a threshold after the candidate saves gas).
- Code identity: the candidate has a different code hash, and deployment is not
  checked.
- Several optimized contracts calling each other: each contract is checked
  against fixtures that contain the other contracts unchanged.

The separate region checker for developers ([dev/regions.md](dev/regions.md))
proves conditional equivalence of selected regions against pinned upstream EVM
semantics. It is not part of `optimize` or `verify`.
