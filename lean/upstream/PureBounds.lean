import CountOffset
import SwapOperations

/-! Abstract-state bounds and canonical-cost steps for supported pure operations. -/
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream
namespace GolfPureBounds

theorem bounds_push (s : EVM.State) (p : Operation.POp) (nonzero : p ≠ .PUSH0)
    (gas : 3 ≤ s.gasAvailable.toNat) (inputs : 0 ≤ s.stack.length)
    (outputs : s.stack.length - 0 + 1 ≤ 1024) : FullXBounds s (.Push p) := by
  refine ⟨?_, inputs, outputs⟩
  simpa only [cost_push s p nonzero] using gas

theorem bounds_push0 (s : EVM.State)
    (gas : 2 ≤ s.gasAvailable.toNat) (inputs : 0 ≤ s.stack.length)
    (outputs : s.stack.length - 0 + 1 ≤ 1024) : FullXBounds s .PUSH0 :=
  ⟨gas, inputs, outputs⟩

theorem bounds_mul (s : EVM.State)
    (gas : 5 ≤ s.gasAvailable.toNat) (inputs : 2 ≤ s.stack.length)
    (outputs : s.stack.length - 2 + 1 ≤ 1024) : FullXBounds s .MUL :=
  ⟨gas, inputs, outputs⟩

theorem bounds_shl (s : EVM.State)
    (gas : 3 ≤ s.gasAvailable.toNat) (inputs : 2 ≤ s.stack.length)
    (outputs : s.stack.length - 2 + 1 ≤ 1024) : FullXBounds s .SHL :=
  ⟨gas, inputs, outputs⟩

theorem bounds_add (s : EVM.State)
    (gas : 3 ≤ s.gasAvailable.toNat) (inputs : 2 ≤ s.stack.length)
    (outputs : s.stack.length - 2 + 1 ≤ 1024) : FullXBounds s .ADD :=
  ⟨gas, inputs, outputs⟩

theorem bounds_swap1 (s : EVM.State)
    (gas : 3 ≤ s.gasAvailable.toNat) (inputs : 2 ≤ s.stack.length)
    (outputs : s.stack.length - 2 + 2 ≤ 1024) : FullXBounds s .SWAP1 :=
  ⟨gas, inputs, outputs⟩

theorem bounds_dup1 (s : EVM.State)
    (gas : 3 ≤ s.gasAvailable.toNat) (inputs : 1 ≤ s.stack.length)
    (outputs : s.stack.length - 1 + 2 ≤ 1024) : FullXBounds s .DUP1 :=
  ⟨gas, inputs, outputs⟩

theorem canonical_step_push (s : EVM.State) (p : Operation.POp) (v : UInt256)
    (width fuel : Nat) (nonzero : p ≠ .PUSH0) :
    EVM.step (fuel + 1) (C' s (.Push p)) (some (.Push p, some (v, width))) s =
      .ok (pushedWidth s v width) := by
  rw [cost_push s p nonzero]
  exact step_push s p v width fuel 3 nonzero

theorem canonical_step_push0 (s : EVM.State) (fuel : Nat)
    (arg : Option (UInt256 × Nat)) :
    EVM.step (fuel + 1) (C' s .PUSH0) (some (.PUSH0, arg)) s =
      .ok (binaryPost s (UInt256.ofNat 0) s.stack 2) := by
  rw [cost_push0]
  exact step_push0 s fuel 2 arg

theorem canonical_step_mul (s : EVM.State) (fuel : Nat)
    (arg : Option (UInt256 × Nat))
    (a b : UInt256) (tail : List UInt256) (stack : s.stack = b :: a :: tail) :
    EVM.step (fuel + 1) (C' s .MUL) (some (.MUL, arg)) s =
      .ok (binaryPost s (UInt256.mul b a) tail 5) := by
  rw [cost_mul]
  exact step_mul s fuel 5 arg a b tail stack

theorem canonical_step_shl (s : EVM.State) (fuel : Nat)
    (arg : Option (UInt256 × Nat))
    (a b : UInt256) (tail : List UInt256) (stack : s.stack = b :: a :: tail) :
    EVM.step (fuel + 1) (C' s .SHL) (some (.SHL, arg)) s =
      .ok (binaryPost s (UInt256.shiftLeft a b) tail 3) := by
  rw [cost_shl]
  exact step_shl s fuel 3 arg a b tail stack

theorem canonical_step_add (s : EVM.State) (fuel : Nat)
    (arg : Option (UInt256 × Nat))
    (a b : UInt256) (tail : List UInt256) (stack : s.stack = b :: a :: tail) :
    EVM.step (fuel + 1) (C' s .ADD) (some (.ADD, arg)) s =
      .ok (binaryPost s (UInt256.add b a) tail 3) := by
  rw [cost_add]
  exact step_add s fuel 3 arg a b tail stack

theorem canonical_step_swap1 (s : EVM.State) (fuel : Nat)
    (arg : Option (UInt256 × Nat))
    (a b : UInt256) (tail : List UInt256) (stack : s.stack = b :: a :: tail) :
    EVM.step (fuel + 1) (C' s .SWAP1) (some (.SWAP1, arg)) s =
      .ok (binaryPost s a (b :: tail) 3) := by
  rw [cost_swap1]
  exact step_swap1 s fuel 3 arg a b tail stack

theorem canonical_step_dup1 (s : EVM.State) (fuel : Nat)
    (arg : Option (UInt256 × Nat))
    (a : UInt256) (tail : List UInt256) (stack : s.stack = a :: tail) :
    EVM.step (fuel + 1) (C' s .DUP1) (some (.DUP1, arg)) s =
      .ok (binaryPost s a (a :: tail) 3) := by
  rw [cost_dup1]
  exact step_dup1 s fuel 3 arg a tail stack

theorem remaining_enough (initial available spent cost total : Nat)
    (within : spent + cost ≤ total) (funded : total ≤ initial)
    (balance : available = initial - spent) : cost ≤ available := by
  omega

theorem remaining_sub (initial current : UInt256) (spent cost total : Nat)
    (small : cost < UInt256.size) (within : spent + cost ≤ total)
    (funded : total ≤ initial.toNat)
    (balance : current.toNat = initial.toNat - spent) :
    (current - UInt256.ofNat cost).toNat = initial.toNat - (spent + cost) := by
  rw [word_sub_toNat current cost small
    (remaining_enough initial.toNat current.toNat spent cost total within funded balance), balance]
  omega

theorem bounds_sub (s : EVM.State)
    (gas : 3 ≤ s.gasAvailable.toNat) (inputs : 2 ≤ s.stack.length)
    (outputs : s.stack.length - 2 + 1 ≤ 1024) : FullXBounds s .SUB :=
  ⟨gas, inputs, outputs⟩

theorem canonical_step_sub (s : EVM.State) (fuel : Nat)
    (arg : Option (UInt256 × Nat))
    (a b : UInt256) (tail : List UInt256) (stack : s.stack = b :: a :: tail) :
    EVM.step (fuel + 1) (C' s .SUB) (some (.SUB, arg)) s =
      .ok (binaryPost s (UInt256.sub b a) tail 3) := by
  exact GolfCountOffset.step_sub s fuel 3 arg a b tail stack

theorem bounds_and (s : EVM.State)
    (gas : 3 ≤ s.gasAvailable.toNat) (inputs : 2 ≤ s.stack.length)
    (outputs : s.stack.length - 2 + 1 ≤ 1024) : FullXBounds s .AND :=
  ⟨gas, inputs, outputs⟩

theorem canonical_step_and (s : EVM.State) (fuel : Nat)
    (arg : Option (UInt256 × Nat))
    (a b : UInt256) (tail : List UInt256) (stack : s.stack = b :: a :: tail) :
    EVM.step (fuel + 1) (C' s .AND) (some (.AND, arg)) s =
      .ok (binaryPost s (b &&& a) tail 3) := by
  exact GolfCountOffset.step_and s fuel 3 arg a b tail stack

theorem bounds_not (s : EVM.State)
    (gas : 3 ≤ s.gasAvailable.toNat) (inputs : 1 ≤ s.stack.length)
    (outputs : s.stack.length - 1 + 1 ≤ 1024) : FullXBounds s .NOT :=
  ⟨gas, inputs, outputs⟩

theorem canonical_step_not (s : EVM.State) (fuel : Nat)
    (arg : Option (UInt256 × Nat))
    (a : UInt256) (tail : List UInt256) (stack : s.stack = a :: tail) :
    EVM.step (fuel + 1) (C' s .NOT) (some (.NOT, arg)) s =
      .ok (binaryPost s (UInt256.lnot a) tail 3) := by
  exact GolfCountOffset.step_not s fuel 3 arg a tail stack

theorem bounds_lt (s : EVM.State)
    (gas : 3 ≤ s.gasAvailable.toNat) (inputs : 2 ≤ s.stack.length)
    (outputs : s.stack.length - 2 + 1 ≤ 1024) : FullXBounds s .LT :=
  ⟨gas, inputs, outputs⟩

theorem canonical_step_lt (s : EVM.State) (fuel : Nat)
    (arg : Option (UInt256 × Nat))
    (a b : UInt256) (tail : List UInt256) (stack : s.stack = b :: a :: tail) :
    EVM.step (fuel + 1) (C' s .LT) (some (.LT, arg)) s =
      .ok (binaryPost s (UInt256.lt b a) tail 3) := by
  exact GolfCountOffset.step_lt s fuel 3 arg a b tail stack

theorem bounds_eq (s : EVM.State)
    (gas : 3 ≤ s.gasAvailable.toNat) (inputs : 2 ≤ s.stack.length)
    (outputs : s.stack.length - 2 + 1 ≤ 1024) : FullXBounds s .EQ :=
  ⟨gas, inputs, outputs⟩

theorem canonical_step_eq (s : EVM.State) (fuel : Nat)
    (arg : Option (UInt256 × Nat))
    (a b : UInt256) (tail : List UInt256) (stack : s.stack = b :: a :: tail) :
    EVM.step (fuel + 1) (C' s .EQ) (some (.EQ, arg)) s =
      .ok (binaryPost s (UInt256.eq b a) tail 3) := by
  exact GolfCountOffset.step_eq s fuel 3 arg a b tail stack

theorem bounds_shr (s : EVM.State)
    (gas : 3 ≤ s.gasAvailable.toNat) (inputs : 2 ≤ s.stack.length)
    (outputs : s.stack.length - 2 + 1 ≤ 1024) : FullXBounds s .SHR :=
  ⟨gas, inputs, outputs⟩

theorem canonical_step_shr (s : EVM.State) (fuel : Nat)
    (arg : Option (UInt256 × Nat))
    (a b : UInt256) (tail : List UInt256) (stack : s.stack = b :: a :: tail) :
    EVM.step (fuel + 1) (C' s .SHR) (some (.SHR, arg)) s =
      .ok (binaryPost s (UInt256.shiftRight a b) tail 3) := by
  exact GolfCountOffset.step_shr s fuel 3 arg a b tail stack

theorem bounds_iszero (s : EVM.State)
    (gas : 3 ≤ s.gasAvailable.toNat) (inputs : 1 ≤ s.stack.length)
    (outputs : s.stack.length - 1 + 1 ≤ 1024) : FullXBounds s .ISZERO :=
  ⟨gas, inputs, outputs⟩

theorem canonical_step_iszero (s : EVM.State) (fuel : Nat)
    (arg : Option (UInt256 × Nat))
    (a : UInt256) (tail : List UInt256) (stack : s.stack = a :: tail) :
    EVM.step (fuel + 1) (C' s .ISZERO) (some (.ISZERO, arg)) s =
      .ok (binaryPost s (UInt256.isZero a) tail 3) := by
  exact GolfCountOffset.step_iszero s fuel 3 arg a tail stack

theorem bounds_or (s : EVM.State)
    (gas : 3 ≤ s.gasAvailable.toNat) (inputs : 2 ≤ s.stack.length)
    (outputs : s.stack.length - 2 + 1 ≤ 1024) : FullXBounds s .OR :=
  ⟨gas, inputs, outputs⟩

theorem canonical_step_or (s : EVM.State) (fuel : Nat)
    (arg : Option (UInt256 × Nat)) (a b : UInt256) (tail : List UInt256)
    (stack : s.stack = b :: a :: tail) :
    EVM.step (fuel+1) (C' s .OR) (some (.OR,arg)) s =
      .ok (binaryPost s (b ||| a) tail 3) := by
  exact GolfCountOffset.step_or s fuel 3 arg a b tail stack

theorem canonical_step_exchange (s : EVM.State) (e : Operation.ExOp) (fuel : Nat)
    (arg : Option (UInt256 × Nat)) (a z : UInt256) (middle tail : List UInt256)
    (index : middle.length+1 = GolfSwapFamily.depth e)
    (stack : s.stack = a :: (middle ++ z :: tail)) :
    EVM.step (fuel+1) (C' s (.Exchange e)) (some (.Exchange e,arg)) s =
      .ok (binaryPost s z (middle ++ a :: tail) 3) := by
  rw [GolfSwapFamily.cost]
  exact GolfSwapFamily.step_prefix s e fuel 3 arg a z middle tail index stack

end GolfPureBounds

#print axioms GolfPureBounds.bounds_push
#print axioms GolfPureBounds.bounds_push0
#print axioms GolfPureBounds.bounds_mul
#print axioms GolfPureBounds.bounds_shl
#print axioms GolfPureBounds.bounds_add
#print axioms GolfPureBounds.bounds_swap1
#print axioms GolfPureBounds.bounds_dup1
#print axioms GolfPureBounds.canonical_step_push
#print axioms GolfPureBounds.canonical_step_push0
#print axioms GolfPureBounds.canonical_step_mul
#print axioms GolfPureBounds.canonical_step_shl
#print axioms GolfPureBounds.canonical_step_add
#print axioms GolfPureBounds.canonical_step_swap1
#print axioms GolfPureBounds.canonical_step_dup1

#print axioms GolfPureBounds.remaining_enough
#print axioms GolfPureBounds.remaining_sub

#print axioms GolfPureBounds.bounds_sub
#print axioms GolfPureBounds.bounds_and
#print axioms GolfPureBounds.bounds_not
#print axioms GolfPureBounds.canonical_step_sub
#print axioms GolfPureBounds.canonical_step_and
#print axioms GolfPureBounds.canonical_step_not

#print axioms GolfPureBounds.bounds_or
#print axioms GolfPureBounds.canonical_step_or
#print axioms GolfPureBounds.canonical_step_exchange

#print axioms GolfPureBounds.bounds_shr
#print axioms GolfPureBounds.canonical_step_shr
#print axioms GolfPureBounds.bounds_eq
#print axioms GolfPureBounds.canonical_step_eq
#print axioms GolfPureBounds.bounds_lt
#print axioms GolfPureBounds.canonical_step_lt
#print axioms GolfPureBounds.bounds_iszero
#print axioms GolfPureBounds.canonical_step_iszero
