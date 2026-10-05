import CountOffset
import SwapOperations
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset
namespace CanonicalMaskWindow

-- These snapshots describe proof endpoints; execution remains upstream EVM.step/X.
def spend (gas : UInt256) : Nat → UInt256
 | 0 => gas
 | n+1 => spend gas n - UInt256.ofNat 3

def snapshot (s : EVM.State) (stack : List UInt256) (bytes steps : Nat) : EVM.State :=
 { s with
   stack := stack
   pc := s.pc + UInt256.ofNat bytes
   gasAvailable := spend s.gasAvailable steps
   execLength := s.execLength + steps }

theorem word_add_nat (a : UInt256) (m n : Nat) :
 a + UInt256.ofNat m + UInt256.ofNat n = a + UInt256.ofNat (m+n) := by
 change UInt256.mk ((a.val + Fin.ofNat _ m) + Fin.ofNat _ n) =
   UInt256.mk (a.val + Fin.ofNat _ (m+n))
 congr 1
 apply Fin.ext
 simp [Fin.add_def, Fin.ofNat, Nat.add_assoc]

theorem snapshot_zero (s : EVM.State) : snapshot s s.stack 0 0 = s := by
 have zero : s.pc + UInt256.ofNat 0 = s.pc := by
   change UInt256.mk (s.pc.val + 0) = s.pc
   simp
 simp only [snapshot,spend,zero,Nat.add_zero]

theorem snapshot_push (s : EVM.State) (stack : List UInt256) (bytes steps width : Nat)
 (value : UInt256) :
 pushedWidth (snapshot s stack bytes steps) value width =
 snapshot s (value::stack) (bytes+(width+1)) (steps+1) := by
 simp only [pushedWidth,snapshot,spend,word_add_nat,Nat.add_assoc]

theorem snapshot_binary (s : EVM.State) (stack tail : List UInt256) (bytes steps : Nat)
 (value : UInt256) :
 binaryPost (snapshot s stack bytes steps) value tail 3 =
 snapshot s (value::tail) (bytes+1) (steps+1) := by
 simp only [binaryPost,snapshot,spend,word_add_nat,Nat.add_assoc]

theorem spend_nat (gas : UInt256) (steps : Nat) (enough : 3*steps ≤ gas.toNat) :
 (spend gas steps).toNat = gas.toNat - 3*steps := by
 induction steps with
 | zero => simp [spend]
 | succ n ih =>
   have hn : 3*n ≤ gas.toNat := by omega
   have hg : 3 ≤ (spend gas n).toNat := by rw [ih hn]; omega
   rw [spend,word_sub_toNat _ 3 (by decide) hg,ih hn]
   omega

@[simp] theorem mem_or (s : EVM.State) : memoryExpansionCost s .OR = 0 := by
 simp [memoryExpansionCost,memoryExpansionCost.μᵢ']
@[simp] theorem cost_or (s : EVM.State) : C' s .OR = 3 := rfl

theorem X_next_or (s next : EVM.State) (fuel : Nat) (jumps : Array UInt256)
 (arg : Option (UInt256 × Nat))
 (decoded : decode s.executionEnv.code s.pc = some (.OR,arg))
 (bounds : FullXBounds s .OR)
 (canonical : EVM.step (fuel+1) (C' s .OR) (some (.OR,arg)) s = .ok next) :
 X (fuel+2) jumps s = X (fuel+1) jumps next := by
 have gas := bounds.gas
 have inputs := bounds.inputs
 have outputs := bounds.outputs
 conv_lhs => unfold X
 simp only [decoded]
 simp [mem_or,cost_or,Operation.isCreate,δ,α,
  show ¬s.gasAvailable.toNat < 3 by exact Nat.not_lt.mpr gas,
  show ¬s.stack.length < 2 by exact Nat.not_lt.mpr inputs,
  show ¬1024 < s.stack.length - 2 + 1 by exact Nat.not_lt.mpr outputs]
 change (do
   let n ← EVM.step (fuel+1) 3 (some (.OR,arg)) s
   X (fuel+1) jumps n) = _
 rw [cost_or] at canonical
 rw [canonical]
 rfl

inductive ExtraOp : Operation .EVM → Prop where
 | sub : ExtraOp .SUB
 | and : ExtraOp .AND
 | not : ExtraOp .NOT
 | bor : ExtraOp .OR
 | exchange (e : Operation.ExOp) : ExtraOp (.Exchange e)

theorem X_next_extra (s next : EVM.State) (fuel : Nat) (jumps : Array UInt256)
 (op : Operation .EVM) (arg : Option (UInt256 × Nat)) (allowed : ExtraOp op)
 (decoded : decode s.executionEnv.code s.pc = some (op,arg))
 (bounds : FullXBounds s op)
 (canonical : EVM.step (fuel+1) (C' s op) (some (op,arg)) s = .ok next) :
 X (fuel+2) jumps s = X (fuel+1) jumps next := by
 have gas := bounds.gas
 have inputs := bounds.inputs
 have outputs := bounds.outputs
 cases allowed with
 | sub =>
   have mem : memoryExpansionCost s .SUB = 0 := by
     simp [memoryExpansionCost,memoryExpansionCost.μᵢ']
   have cost : C' s .SUB = 3 := rfl
   conv_lhs => unfold X
   simp only [decoded]
   simp [mem,cost,Operation.isCreate,δ,α,
     show ¬s.gasAvailable.toNat < 3 by exact Nat.not_lt.mpr gas,
     show ¬s.stack.length < 2 by exact Nat.not_lt.mpr inputs,
     show ¬1024 < s.stack.length - 2 + 1 by exact Nat.not_lt.mpr outputs]
   change (do
     let n ← EVM.step (fuel+1) 3 (some (.SUB,arg)) s
     X (fuel+1) jumps n) = _
   rw [cost] at canonical
   rw [canonical]
   rfl
 | and =>
   have mem : memoryExpansionCost s .AND = 0 := by
     simp [memoryExpansionCost,memoryExpansionCost.μᵢ']
   have cost : C' s .AND = 3 := rfl
   conv_lhs => unfold X
   simp only [decoded]
   simp [mem,cost,Operation.isCreate,δ,α,
     show ¬s.gasAvailable.toNat < 3 by exact Nat.not_lt.mpr gas,
     show ¬s.stack.length < 2 by exact Nat.not_lt.mpr inputs,
     show ¬1024 < s.stack.length - 2 + 1 by exact Nat.not_lt.mpr outputs]
   change (do
     let n ← EVM.step (fuel+1) 3 (some (.AND,arg)) s
     X (fuel+1) jumps n) = _
   rw [cost] at canonical
   rw [canonical]
   rfl
 | not =>
   have mem : memoryExpansionCost s .NOT = 0 := by
     simp [memoryExpansionCost,memoryExpansionCost.μᵢ']
   have cost : C' s .NOT = 3 := rfl
   conv_lhs => unfold X
   simp only [decoded]
   simp [mem,cost,Operation.isCreate,δ,α,
     show ¬s.gasAvailable.toNat < 3 by exact Nat.not_lt.mpr gas,
     show ¬s.stack.length < 1 by exact Nat.not_lt.mpr inputs,
     show ¬1024 < s.stack.length - 1 + 1 by exact Nat.not_lt.mpr outputs]
   change (do
     let n ← EVM.step (fuel+1) 3 (some (.NOT,arg)) s
     X (fuel+1) jumps n) = _
   rw [cost] at canonical
   rw [canonical]
   rfl

 | bor => exact X_next_or s next fuel jumps arg decoded bounds canonical
 | exchange e => exact GolfSwapFamily.X_next s next e fuel jumps arg decoded bounds canonical

#print axioms mem_or
#print axioms cost_or
#print axioms X_next_or
#print axioms word_add_nat
#print axioms snapshot_push
#print axioms snapshot_binary
#print axioms spend_nat
#print axioms X_next_extra
end CanonicalMaskWindow
