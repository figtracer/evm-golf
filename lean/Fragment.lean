/-!
Reusable successful PUSH/MUL to PUSH/SHL execution in the small Golf model.
Exact immediate values and complete positive PUSH widths remain proof premises.
Gas, stack bounds and surrounding code are handled separately.
-/

namespace GolfProof

theorem mul_power_fragment
    (before after : List Nat) (exponent : Nat)
    (beforeWidth : 0 < before.length ∧ before.length ≤ 32)
    (afterWidth : 0 < after.length ∧ after.length ≤ 32)
    (beforeValue : Golf.immediate before = 2 ^ exponent)
    (afterValue : Golf.immediate after = exponent)
    (exponentBound : exponent < 256)
    (a x y : Golf.Word) (tail : List Golf.Word) :
    ∃ output,
      Golf.run (before.length + 3)
        ((95 + before.length) :: (before ++ [2])) (a :: tail) x y = some output ∧
      Golf.run (after.length + 3)
        ((95 + after.length) :: (after ++ [27])) (a :: tail) x y = some output := by
  have beforePush : 96 ≤ 95 + before.length ∧ 95 + before.length ≤ 127 := by omega
  have afterPush : 96 ≤ 95 + after.length ∧ 95 + after.length ≤ 127 := by omega
  have beforeNotPush0 : 95 + before.length ≠ 95 := by omega
  have afterNotPush0 : 95 + after.length ≠ 95 := by omega
  have beforeSize : 95 + before.length - 95 = before.length := by omega
  have afterSize : 95 + after.length - 95 = after.length := by omega
  have exponentFits : exponent < 2 ^ 256 :=
    Nat.lt_trans exponentBound (by decide +kernel)
  refine ⟨(BitVec.ofNat 256 (2 ^ exponent) * a) :: tail, ?_, ?_⟩
  · rw [Golf.run]
    simp only [beforeNotPush0, beforePush, beforeSize, ite_false]
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.le_add_right,
      ite_true, List.take_left, List.drop_left, beforeValue]
    simp [Golf.run]
  · rw [Golf.run]
    simp only [afterNotPush0, afterPush, afterSize, ite_false]
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.le_add_right,
      ite_true, List.take_left, List.drop_left, afterValue]
    simp [Golf.run, BitVec.toNat_ofNat, Nat.mod_eq_of_lt exponentFits,
      GolfProof.shift_power, BitVec.mul_comm]

end GolfProof
