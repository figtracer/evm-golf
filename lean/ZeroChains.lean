/- Generic zero-producing stack chains in the existing Golf model.
Execution and stack-profile lemmas; no gas or full-EVM correspondence. -/
namespace GolfZeroChain

-- Only existing Golf DUP1 semantics; arbitrary-depth DUP is intentionally excluded.
def replace (ops : List Nat) : List Nat := ops.map (fun _ => 95)

theorem tail_equal (ops : List Nat) (allowed : ∀ op ∈ ops, op = 95 ∨ op = 128)
    (stack : List Golf.Word) (x y : Golf.Word) :
    GolfBounded.run (ops.length + 1) ops (0 :: stack) x y =
      GolfBounded.run (ops.length + 1) (replace ops) (0 :: stack) x y := by
  induction ops generalizing stack with
  | nil => rfl
  | cons op ops ih =>
    have rest : ∀ q ∈ ops, q = 95 ∨ q = 128 := by
      intro q h; exact allowed q (List.mem_cons_of_mem op h)
    have current := allowed op (by simp)
    rcases current with rfl | rfl
    all_goals
      change (if (0 :: stack).length > 1024 then none else
        GolfBounded.run (ops.length + 1) ops (0 :: 0 :: stack) x y) =
        (if (0 :: stack).length > 1024 then none else
        GolfBounded.run (ops.length + 1) (replace ops) (0 :: 0 :: stack) x y)
      split
      · rfl
      · exact ih rest (0 :: stack)

def code (bytes ops : List Nat) : List Nat := (95 + bytes.length) :: (bytes ++ ops)

theorem chain_equal (bytes ops : List Nat) (width : bytes.length ≤ 32)
    (zero : GolfLiterals.word bytes = 0)
    (allowed : ∀ op ∈ ops, op = 95 ∨ op = 128)
    (stack : List Golf.Word) (x y : Golf.Word) :
    GolfBounded.run (ops.length + 2) (code bytes ops) stack x y =
      GolfBounded.run (ops.length + 2) (code bytes (replace ops)) stack x y := by
  unfold code
  rw [GolfLiterals.bounded_push bytes ops width,
    GolfLiterals.bounded_push bytes (replace ops) width, zero]
  split
  · rfl
  · exact tail_equal ops allowed stack x y

-- Required initial height 0, delta and peak ops.length+1 on both sides.
-- The bounded root above covers ALL incoming heights, not only success.
-- Gas and canonical EVM correspondence are separate obligations.
theorem complete_tail (ops : List Nat) (allowed : ∀ op ∈ ops, op = 95 ∨ op = 128) :
    GolfComposition.Complete ops ops.length := by
  induction ops with
  | nil => exact .nil
  | cons op ops ih =>
    have current := allowed op (by simp)
    apply GolfComposition.Complete.step (immediate := [])
    · rcases current with rfl | rfl <;> decide +kernel
    · apply ih; intro q h; exact allowed q (List.mem_cons_of_mem op h)

theorem complete_code (bytes ops : List Nat) (width : bytes.length ≤ 32)
    (allowed : ∀ op ∈ ops, op = 95 ∨ op = 128) :
    GolfComposition.Complete (code bytes ops) (ops.length + 1) := by
  apply GolfComposition.Complete.step (immediate := bytes)
  · split <;> omega
  · exact complete_tail ops allowed

theorem replaced_allowed (ops : List Nat) : ∀ op ∈ replace ops, op = 95 ∨ op = 128 := by
  simp [replace]

theorem byte_equal (bytes ops : List Nat) (width : bytes.length ≤ 32)
    (zero : GolfLiterals.word bytes = 0)
    (allowed : ∀ op ∈ ops, op = 95 ∨ op = 128)
    (stack : List Golf.Word) (x y : Golf.Word) :
    GolfBounded.run ((code bytes ops).length + 1) (code bytes ops) stack x y =
      GolfBounded.run ((code bytes (replace ops)).length + 1) (code bytes (replace ops)) stack x y := by
  rw [GolfComposition.byte_fuel (complete_code bytes ops width allowed),
    GolfComposition.byte_fuel (complete_code bytes (replace ops) width (replaced_allowed ops))]
  simpa [replace] using chain_equal bytes ops width zero allowed stack x y

theorem contextual (bytes ops : List Nat) (width : bytes.length ≤ 32)
    (zero : GolfLiterals.word bytes = 0)
    (allowed : ∀ op ∈ ops, op = 95 ∨ op = 128) :
    GolfComposition.ContextEquivalent (code bytes ops) (code bytes (replace ops)) :=
  GolfComposition.context_of_equal (complete_code bytes ops width allowed)
    (complete_code bytes (replace ops) width (replaced_allowed ops))
    (byte_equal bytes ops width zero allowed)



theorem replicate_end (n : Nat) (stack : List Golf.Word) :
    List.replicate n (0 : Golf.Word) ++ (0 :: stack) =
      List.replicate (n + 1) 0 ++ stack := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons 0) ih

theorem tail_output (ops : List Nat) (allowed : ∀ op ∈ ops, op = 95 ∨ op = 128)
    (stack : List Golf.Word) (x y : Golf.Word) :
    GolfBounded.run (ops.length + 1) ops (0 :: stack) x y =
      if stack.length + ops.length + 1 ≤ 1024 then
        some (List.replicate (ops.length + 1) 0 ++ stack) else none := by
  induction ops generalizing stack with
  | nil =>
    by_cases h : 1024 < stack.length + 1
    · have hn : ¬stack.length + 1 ≤ 1024 := by omega
      simp [GolfBounded.run,h,hn]
    · have hn : stack.length + 1 ≤ 1024 := by omega
      simp [GolfBounded.run,h,hn]
  | cons op ops ih =>
    have rest : ∀ q ∈ ops, q = 95 ∨ q = 128 := by
      intro q h; exact allowed q (List.mem_cons_of_mem op h)
    have current := allowed op (by simp)
    rcases current with rfl | rfl
    all_goals
      change (if (0 :: stack).length > 1024 then none else
        GolfBounded.run (ops.length + 1) ops (0 :: 0 :: stack) x y) = _
      rw [ih rest]
      simp only [List.length_cons, replicate_end]
      by_cases fit : stack.length + ops.length + 2 ≤ 1024
      · have initial : ¬stack.length + 1 > 1024 := by omega
        have next : stack.length + 1 + ops.length + 1 ≤ 1024 := by omega
        simp_all [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · have next : ¬stack.length + 1 + ops.length + 1 ≤ 1024 := by omega
        simp_all [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem output (bytes ops : List Nat) (width : bytes.length ≤ 32)
    (zero : GolfLiterals.word bytes = 0)
    (allowed : ∀ op ∈ ops, op = 95 ∨ op = 128)
    (stack : List Golf.Word) (x y : Golf.Word) :
    GolfBounded.run ((code bytes ops).length + 1) (code bytes ops) stack x y =
      if stack.length + ops.length + 1 ≤ 1024 then
        some (List.replicate (ops.length + 1) 0 ++ stack) else none := by
  rw [GolfComposition.byte_fuel (complete_code bytes ops width allowed)]
  unfold code
  rw [GolfLiterals.bounded_push bytes ops width, zero, tail_output ops allowed]
  by_cases fit : stack.length + ops.length + 1 ≤ 1024
  · have h : ¬stack.length > 1024 := by omega
    simp [fit,h]
  · simp [fit]

theorem failure_iff (bytes ops : List Nat) (width : bytes.length ≤ 32)
    (zero : GolfLiterals.word bytes = 0)
    (allowed : ∀ op ∈ ops, op = 95 ∨ op = 128)
    (stack : List Golf.Word) (x y : Golf.Word) :
    GolfBounded.run ((code bytes ops).length + 1) (code bytes ops) stack x y = none ↔
      1024 < stack.length + ops.length + 1 := by
  rw [output bytes ops width zero allowed]
  split <;> simp_all <;> omega

theorem useful_success (bytes ops : List Nat) (width : bytes.length ≤ 32)
    (zero : GolfLiterals.word bytes = 0)
    (allowed : ∀ op ∈ ops, op = 95 ∨ op = 128)
    (useful : ops.length ≤ 1023) (x y : Golf.Word) :
    GolfBounded.run ((code bytes ops).length + 1) (code bytes ops) [] x y =
      some (List.replicate (ops.length + 1) 0) := by
  rw [output bytes ops width zero allowed]
  simp [show ops.length + 1 ≤ 1024 by omega]


theorem tail_profile (ops : List Nat) (allowed : ∀ op ∈ ops, op = 95 ∨ op = 128)
    (height extra : Nat) :
    GolfLayout.profileAux (ops.length + extra + 1) ops (height + 1) 0 (height + 1) =
      some (0, ((height + ops.length + 1 : Nat) : Int), height + ops.length + 1) := by
  induction ops generalizing height with
  | nil => simp [GolfLayout.profileAux]
  | cons op ops ih =>
    have rest : ∀ q ∈ ops, q = 95 ∨ q = 128 := by
      intro q h; exact allowed q (List.mem_cons_of_mem op h)
    have current := allowed op (by simp)
    have nonpos : (1 - ((height : Int) + 1)).toNat = 0 := Int.toNat_of_nonpos (by omega)
    have nextInt : (height : Int) + 1 + 1 = ((height + 1 : Nat) : Int) + 1 := by omega
    have nextNat : (((height : Int) + 1 + 1).toNat) = height + 1 + 1 := by omega
    have peak : max (height + 1) (height + 1 + 1) = height + 1 + 1 := by omega
    rcases current with rfl | rfl
    all_goals
      rw [show (List.length (_ :: ops) + extra + 1) = (ops.length + extra + 1) + 1 by simp; omega]
      rw [GolfLayout.profileAux]
      simp only [show (95 ≤ (95:Nat) ∧ 95 ≤ 127) by decide, show ¬(95 ≤ (128:Nat) ∧ 128 ≤ 127) by decide,
        show ¬((128:Nat) = 1 ∨ 128 = 2 ∨ 128 = 22 ∨ 128 = 27) by decide,
        Nat.sub_self, Nat.zero_le, ite_true, ite_false, List.drop_zero,
        nonpos, Nat.max_self, nextNat, peak]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih rest (height + 1)


theorem unbounded_tail (ops : List Nat) (allowed : ∀ op ∈ ops, op = 95 ∨ op = 128)
    (extra : Nat) (stack : List Golf.Word) (x y : Golf.Word) :
    Golf.run (ops.length + extra + 1) ops (0 :: stack) x y =
      some (List.replicate (ops.length + 1) 0 ++ stack) := by
  induction ops generalizing stack with
  | nil => simp [Golf.run]
  | cons op ops ih =>
    have rest : ∀ q ∈ ops, q = 95 ∨ q = 128 := by
      intro q h; exact allowed q (List.mem_cons_of_mem op h)
    have current := allowed op (by simp)
    have fuel : (op :: ops).length + extra + 1 = (ops.length + extra + 1) + 1 := by simp; omega
    rw [fuel]
    rcases current with rfl | rfl
    all_goals
      change Golf.run (ops.length + extra + 1) ops (0 :: 0 :: stack) x y = _
      rw [ih rest, replicate_end]
      rfl

theorem unbounded_output (bytes ops : List Nat) (width : bytes.length ≤ 32)
    (zero : GolfLiterals.word bytes = 0)
    (allowed : ∀ op ∈ ops, op = 95 ∨ op = 128)
    (stack : List Golf.Word) (x y : Golf.Word) :
    Golf.run ((code bytes ops).length + 1) (code bytes ops) stack x y =
      some (List.replicate (ops.length + 1) 0 ++ stack) := by
  unfold code
  have fuel : ((95 + bytes.length) :: (bytes ++ ops)).length + 1 =
      (ops.length + bytes.length + 1) + 1 := by simp; omega
  rw [fuel, GolfLiterals.run_push bytes ops width, zero]
  exact unbounded_tail ops allowed bytes.length stack x y


theorem profile (bytes ops : List Nat) (width : bytes.length ≤ 32)
    (allowed : ∀ op ∈ ops, op = 95 ∨ op = 128) :
    GolfLayout.profile (code bytes ops) = some (0, ((ops.length + 1 : Nat) : Int), ops.length + 1) := by
  have push : 95 ≤ 95 + bytes.length ∧ 95 + bytes.length ≤ 127 := by omega
  have size : 95 + bytes.length - 95 = bytes.length := by omega
  unfold GolfLayout.profile code
  rw [show ((95 + bytes.length) :: (bytes ++ ops)).length + 1 =
    (ops.length + bytes.length + 1) + 1 by simp; omega]
  rw [GolfLayout.profileAux]
  simp only [push, ite_true, size, List.length_append, Nat.le_add_right,
    List.drop_left]
  simpa using tail_profile ops allowed 0 bytes.length

structure Certificate (before after : List Nat) (growth : Nat) : Prop where
  unbounded : GolfLayout.LiteralEquivalent before after
  bounded : GolfLayout.GrowthLiteralEquivalent before after growth
  contextual : GolfComposition.ContextEquivalent before after

theorem certify (bytes ops : List Nat) (width : bytes.length ≤ 32)
    (zero : GolfLiterals.word bytes = 0)
    (allowed : ∀ op ∈ ops, op = 95 ∨ op = 128) (useful : ops.length ≤ 1023) :
    Certificate (code bytes ops) (code bytes (replace ops)) (ops.length + 1) := by
  refine ⟨?_, ?_, contextual bytes ops width zero allowed⟩
  · intro stack x y
    refine ⟨List.replicate (ops.length + 1) 0 ++ stack,
      unbounded_output bytes ops width zero allowed stack x y, ?_⟩
    simpa [replace] using unbounded_output bytes (replace ops) width zero
      (replaced_allowed ops) stack x y
  · refine ⟨by omega, by omega, profile bytes ops width allowed, ?_,
      byte_equal bytes ops width zero allowed, ?_, ?_⟩
    · simpa [replace] using profile bytes (replace ops) width (replaced_allowed ops)
    · intro stack x y height
      refine ⟨List.replicate (ops.length + 1) 0 ++ stack, ?_, ?_⟩
      · rw [output bytes ops width zero allowed]; simp [show stack.length + ops.length + 1 ≤ 1024 by omega]
      · rw [output bytes (replace ops) width zero (replaced_allowed ops)]
        simp only [replace, List.length_map]
        simp [show stack.length + ops.length + 1 ≤ 1024 by omega]
    · intro stack x y height
      constructor
      · exact (failure_iff bytes ops width zero allowed stack x y).mpr (by omega)
      · apply (failure_iff bytes (replace ops) width zero (replaced_allowed ops) stack x y).mpr
        simpa [replace, Nat.add_assoc] using height
end GolfZeroChain
