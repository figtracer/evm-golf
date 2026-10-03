import Driver

/-! Canonical EVM region proof support against the pinned upstream semantics. -/
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM
namespace GolfUpstream

theorem mul_power_of_two_shift (a : UInt256) (k : Nat) (range : k < 256) :
    UInt256.mul (UInt256.ofNat (2^k)) a = UInt256.shiftLeft a (UInt256.ofNat k) := by
  have small : k < UInt256.size := by unfold UInt256.size; omega
  have powSmall : 2^k < UInt256.size := by
    change 2^k < 2^256
    exact Nat.pow_lt_pow_right (by decide) range
  have notLarge : ¬(UInt256.ofNat k).val ≥ (256 : Fin UInt256.size) := by
    change ¬256 % UInt256.size ≤ k % UInt256.size
    rw [Nat.mod_eq_of_lt small]
    change ¬256 ≤ k
    omega
  unfold UInt256.shiftLeft
  rw [if_neg notLarge]
  apply congrArg UInt256.mk
  apply Fin.ext
  change ((2^k % UInt256.size) * a.val.val) % UInt256.size =
    (a.val.val <<< (k % UInt256.size)) % UInt256.size
  rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt powSmall]
  simp [Nat.shiftLeft_eq, Nat.mul_comm]

def MulPowerAt (code : ByteArray) (pc : UInt256) (p : Operation.POp) (width k : Nat) : Prop :=
  decode code pc = some (.Push p, some (UInt256.ofNat (2^k), width)) ∧
  decode code (pc + UInt256.ofNat (width + 1)) = some (.MUL, none)

def ShiftPowerAt (code : ByteArray) (pc : UInt256) (p : Operation.POp) (width k : Nat) : Prop :=
  decode code pc = some (.Push p, some (UInt256.ofNat k, width)) ∧
  decode code (pc + UInt256.ofNat (width + 1)) = some (.SHL, none)

def mulPowerPost (s : EVM.State) (code : ByteArray) (width k : Nat)
    (a : UInt256) (tail : List UInt256) : EVM.State :=
  binaryPost (pushedWidth (withCode s code) (UInt256.ofNat (2^k)) width)
    (UInt256.mul (UInt256.ofNat (2^k)) a) tail 5

def shiftPowerPost (s : EVM.State) (code : ByteArray) (width k : Nat)
    (a : UInt256) (tail : List UInt256) : EVM.State :=
  binaryPost (pushedWidth (withCode s code) (UInt256.ofNat k) width)
    (UInt256.shiftLeft a (UInt256.ofNat k)) tail 3

theorem fullX_power_refinement (s : EVM.State) (oldCode newCode : ByteArray)
    (p : Operation.POp) (width k : Nat) (a : UInt256) (tail : List UInt256)
    (fuel : Nat) (jumps : Array UInt256) (nonzero : p ≠ .PUSH0) (range : k < 256)
    (oldFragment : MulPowerAt oldCode s.pc p width k)
    (newFragment : ShiftPowerAt newCode s.pc p width k)
    (stack : s.stack = a :: tail) (gas : 8 ≤ s.gasAvailable.toNat)
    (height : s.stack.length < 1024) :
    X (fuel + 3) jumps (withCode s oldCode) =
      X (fuel + 1) jumps (mulPowerPost s oldCode width k a tail) ∧
    X (fuel + 3) jumps (withCode s newCode) =
      X (fuel + 1) jumps (shiftPowerPost s newCode width k a tail) ∧
    eraseCodeGas (mulPowerPost s oldCode width k a tail) =
      eraseCodeGas (shiftPowerPost s newCode width k a tail) ∧
    (shiftPowerPost s newCode width k a tail).gasAvailable.toNat =
      (mulPowerPost s oldCode width k a tail).gasAvailable.toNat + 2 := by
  have enough : 3 ≤ s.gasAvailable.toNat := by omega
  have afterPush := word_sub_toNat s.gasAvailable 3 (by decide) enough
  have tailHeight : tail.length < 1024 := by simp [stack] at height; omega
  have oldRun : X (fuel + 3) jumps (withCode s oldCode) =
      X (fuel + 1) jumps (mulPowerPost s oldCode width k a tail) := by
    have first := X_push_width (withCode s oldCode) p (UInt256.ofNat (2^k)) width
      (fuel + 1) jumps nonzero oldFragment.1 enough height
    have second := X_mul (pushedWidth (withCode s oldCode) (UInt256.ofNat (2^k)) width)
      a (UInt256.ofNat (2^k)) tail fuel jumps oldFragment.2
      (by simp [pushedWidth, withCode, stack]) (by change 5 ≤ (s.gasAvailable - UInt256.ofNat 3).toNat; omega) tailHeight
    exact first.trans second
  have newRun : X (fuel + 3) jumps (withCode s newCode) =
      X (fuel + 1) jumps (shiftPowerPost s newCode width k a tail) := by
    have first := X_push_width (withCode s newCode) p (UInt256.ofNat k) width
      (fuel + 1) jumps nonzero newFragment.1 enough height
    have second := X_shl (pushedWidth (withCode s newCode) (UInt256.ofNat k) width)
      a (UInt256.ofNat k) tail fuel jumps newFragment.2
      (by simp [pushedWidth, withCode, stack]) (by change 3 ≤ (s.gasAvailable - UInt256.ofNat 3).toNat; omega) tailHeight
    exact first.trans second
  have frame : eraseCodeGas (mulPowerPost s oldCode width k a tail) =
      eraseCodeGas (shiftPowerPost s newCode width k a tail) := by
    simp only [mulPowerPost, shiftPowerPost, pushedWidth, binaryPost, withCode,
      eraseCodeGas, mul_power_of_two_shift a k range]
  have mulRemaining := word_sub_toNat (s.gasAvailable - UInt256.ofNat 3) 5
    (by decide) (by omega)
  have shiftRemaining := word_sub_toNat (s.gasAvailable - UInt256.ofNat 3) 3
    (by decide) (by omega)
  refine ⟨oldRun, newRun, frame, ?_⟩
  change ((s.gasAvailable - UInt256.ofNat 3) - UInt256.ofNat 3).toNat =
    ((s.gasAvailable - UInt256.ofNat 3) - UInt256.ofNat 5).toNat + 2
  rw [mulRemaining, shiftRemaining]
  omega


#print axioms fullX_power_refinement
end GolfUpstream
