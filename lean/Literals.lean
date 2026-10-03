/-!
Exact two-literal folds in the small Golf model. Both programs retain two PUSH
instructions, including the temporary peak of two additional stack words.
The equality premise binds the folded literal to the original word operation.
The exact zero-duplication rule also preserves two additional stack words.
-/
namespace GolfLiterals

def word (bytes : List Nat) : Golf.Word := BitVec.ofNat 256 (Golf.immediate bytes)

def code (first second : List Nat) (op : Nat) : List Nat :=
  (95 + first.length) :: (first ++ (95 + second.length) :: (second ++ [op]))

theorem run_push (bytes rest : List Nat) (width : bytes.length ≤ 32)
    (fuel : Nat) (stack : List Golf.Word) (x y : Golf.Word) :
    Golf.run (fuel + 1) ((95 + bytes.length) :: (bytes ++ rest)) stack x y =
      Golf.run fuel rest (word bytes :: stack) x y := by
  by_cases empty : bytes = []
  · subst bytes; simp [Golf.run, word, Golf.immediate]
  · have positive : 0 < bytes.length := by cases bytes <;> simp_all
    have push : 96 ≤ 95 + bytes.length ∧ 95 + bytes.length ≤ 127 := by omega
    simp [Golf.run, push, empty, word]

theorem bounded_push (bytes rest : List Nat) (width : bytes.length ≤ 32)
    (fuel : Nat) (stack : List Golf.Word) (x y : Golf.Word) :
    GolfBounded.run (fuel + 1) ((95 + bytes.length) :: (bytes ++ rest)) stack x y =
      if stack.length > 1024 then none else
        GolfBounded.run fuel rest (word bytes :: stack) x y := by
  have size : (if 96 ≤ 95 + bytes.length ∧ 95 + bytes.length ≤ 127
    then 95 + bytes.length - 95 else 0) = bytes.length := by split <;> omega
  simp only [GolfBounded.run, size, List.take_left, List.drop_left]
  rw [show (95 + bytes.length) :: bytes = (95 + bytes.length) :: (bytes ++ []) by simp,
    run_push bytes [] width]
  simp [Golf.run]

theorem complete (first second : List Nat) (op : Nat)
    (firstWidth : first.length ≤ 32) (secondWidth : second.length ≤ 32)
    (operation : op = 22 ∨ op = 27 ∨ op = 80) : GolfComposition.Complete (code first second op) 3 := by
  apply GolfComposition.Complete.step (immediate := first)
  · split <;> omega
  · apply GolfComposition.Complete.step (immediate := second)
    · split <;> omega
    · apply GolfComposition.Complete.step (immediate := [])
      · rcases operation with rfl | rfl | rfl <;> decide +kernel
      · exact GolfComposition.Complete.nil

theorem run_code (first second : List Nat) (op : Nat)
    (firstWidth : first.length ≤ 32) (secondWidth : second.length ≤ 32)
    (operation : op = 22 ∨ op = 27 ∨ op = 80)
    (stack : List Golf.Word) (x y : Golf.Word) :
    Golf.run ((code first second op).length + 1) (code first second op) stack x y =
      some ((if op = 22 then word second &&& word first
        else if op = 27 then word first <<< (word second).toNat else word first) :: stack) := by
  simp only [code, List.length_cons, List.length_append, List.length_nil]
  rw [run_push first _ firstWidth]
  have fuel : first.length + (second.length + 1 + 1) = (first.length + second.length + 1) + 1 := by omega
  rw [fuel, run_push second _ secondWidth]
  rcases operation with rfl | rfl | rfl <;> simp [Golf.run]

theorem bounded_code (first second : List Nat) (op : Nat)
    (firstWidth : first.length ≤ 32) (secondWidth : second.length ≤ 32)
    (operation : op = 22 ∨ op = 27 ∨ op = 80)
    (stack : List Golf.Word) (x y : Golf.Word) :
    GolfBounded.run ((code first second op).length + 1) (code first second op) stack x y =
      if stack.length ≤ 1022 then
        some ((if op = 22 then word second &&& word first
          else if op = 27 then word first <<< (word second).toNat else word first) :: stack)
      else none := by
  rw [GolfComposition.byte_fuel (complete first second op firstWidth secondWidth operation)]
  simp only [code]
  rw [bounded_push first _ firstWidth, bounded_push second _ secondWidth]
  rcases operation with rfl | rfl | rfl <;>
    simp [GolfBounded.run, Golf.run] <;> (repeat' split) <;> simp_all <;> omega

structure LocalCertificate (before after : List Nat) : Prop where
  unbounded : GolfLayout.LiteralEquivalent before after
  bounded : GolfBounded.LiteralEquivalent before after
  contextual : GolfComposition.ContextEquivalent before after

theorem certify (first second folded discard : List Nat) (op : Nat)
    (firstWidth : first.length ≤ 32) (secondWidth : second.length ≤ 32)
    (foldedWidth : folded.length ≤ 32) (discardWidth : discard.length ≤ 32)
    (binary : op = 22 ∨ op = 27)
    (value : word folded = if op = 22 then word second &&& word first
      else word first <<< (word second).toNat) :
    LocalCertificate (code first second op) (code folded discard 80) := by
  have operation : op = 22 ∨ op = 27 ∨ op = 80 := by
    rcases binary with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have beforeRun := run_code first second op firstWidth secondWidth operation
  have afterRun := run_code folded discard 80 foldedWidth discardWidth (Or.inr (Or.inr rfl))
  have beforeBounded := bounded_code first second op firstWidth secondWidth operation
  have afterBounded := bounded_code folded discard 80 foldedWidth discardWidth (Or.inr (Or.inr rfl))
  have expression : (if op = 22 then word second &&& word first
      else if op = 27 then word first <<< (word second).toNat else word first) = word folded := by
    rw [value]
    rcases binary with rfl | rfl <;> rfl
  have bounded : GolfBounded.LiteralEquivalent (code first second op) (code folded discard 80) := by
    refine ⟨?_, ?_, ?_⟩
    · intro stack x y
      rw [beforeBounded, afterBounded, expression]
      rfl
    · intro stack x y height
      refine ⟨word folded :: stack, ?_, ?_⟩
      · rw [beforeBounded, expression]; simp [height]
      · rw [afterBounded]; simp [height]
    · intro stack x y height
      rw [beforeBounded, afterBounded]
      simp [show ¬stack.length ≤ 1022 by omega]
  refine ⟨?_, bounded, GolfComposition.context_of_equal
    (complete first second op firstWidth secondWidth operation)
    (complete folded discard 80 foldedWidth discardWidth (Or.inr (Or.inr rfl))) bounded.equal⟩
  intro stack x y
  refine ⟨word folded :: stack, ?_, ?_⟩
  · rw [beforeRun, expression]
  · rw [afterRun]; rfl

-- Zero duplication retains the complete PUSH immediate and two free stack slots.

def zero_pair (bytes : List Nat) (op : Nat) : List Nat :=
  (95 + bytes.length) :: (bytes ++ [op])

theorem run_zero_pair (bytes : List Nat) (op : Nat) (width : bytes.length ≤ 32)
    (zero : GolfLiterals.word bytes = 0) (kind : op = 128 ∨ op = 95)
    (stack : List Golf.Word) (x y : Golf.Word) :
    Golf.run ((zero_pair bytes op).length + 1) (zero_pair bytes op) stack x y =
      some (0 :: 0 :: stack) := by
  simp only [zero_pair, List.length_cons, List.length_append, List.length_nil]
  rw [GolfLiterals.run_push bytes [op] width, zero]
  rcases kind with rfl | rfl <;> simp [Golf.run]

theorem bounded_zero_pair (bytes : List Nat) (op : Nat) (width : bytes.length ≤ 32)
    (zero : GolfLiterals.word bytes = 0) (kind : op = 128 ∨ op = 95)
    (stack : List Golf.Word) (x y : Golf.Word) :
    GolfBounded.run ((zero_pair bytes op).length + 1) (zero_pair bytes op) stack x y =
      if stack.length ≤ 1022 then some (0 :: 0 :: stack) else none := by
  simp only [zero_pair, List.length_cons, List.length_append, List.length_nil]
  rw [GolfLiterals.bounded_push bytes [op] width, zero]
  rcases kind with rfl | rfl
  all_goals
    by_cases good : stack.length ≤ 1022
    · have h0 : ¬1024 < stack.length := by omega
      have h1 : ¬1024 < stack.length + 1 := by omega
      have h2 : ¬1024 < stack.length + 1 + 1 := by omega
      simp [GolfBounded.run, Golf.run, good, h0, h1, h2]
    · by_cases h0 : 1024 < stack.length
      · simp [GolfBounded.run, Golf.run, good, h0]
      · by_cases h1 : 1024 < stack.length + 1
        · simp [GolfBounded.run, Golf.run, good, h0, h1]
        · have h2 : 1024 < stack.length + 1 + 1 := by omega
          simp [GolfBounded.run, Golf.run, good, h0, h1, h2]

theorem complete_zero_pair (bytes : List Nat) (op : Nat) (width : bytes.length ≤ 32)
    (kind : op = 128 ∨ op = 95) : GolfComposition.Complete (zero_pair bytes op) 2 := by
  apply GolfComposition.Complete.step (op := 95 + bytes.length) (immediate := bytes)
  · split <;> omega
  · apply GolfComposition.Complete.step (op := op) (immediate := [])
    · rcases kind with rfl | rfl <;> decide +kernel
    · exact GolfComposition.Complete.nil

theorem certify_zero_pair (bytes : List Nat) (width : bytes.length ≤ 32)
    (zero : GolfLiterals.word bytes = 0) :
    GolfLiterals.LocalCertificate (zero_pair bytes 128) (zero_pair bytes 95) := by
  have left := bounded_zero_pair bytes 128 width zero (Or.inl rfl)
  have right := bounded_zero_pair bytes 95 width zero (Or.inr rfl)
  have bounded : GolfBounded.LiteralEquivalent (zero_pair bytes 128) (zero_pair bytes 95) := by
    refine ⟨?_, ?_, ?_⟩
    · intro stack x y
      exact (left stack x y).trans (right stack x y).symm
    · intro stack x y height
      refine ⟨0 :: 0 :: stack, ?_, ?_⟩
      · rw [left]; simp [height]
      · rw [right]; simp [height]
    · intro stack x y height
      rw [left, right]
      simp [show ¬stack.length ≤ 1022 by omega]
  refine ⟨?_, bounded, GolfComposition.context_of_equal
    (complete_zero_pair bytes 128 width (Or.inl rfl))
    (complete_zero_pair bytes 95 width (Or.inr rfl)) bounded.equal⟩
  intro stack x y
  exact ⟨0 :: 0 :: stack,
    run_zero_pair bytes 128 width zero (Or.inl rfl) stack x y,
    run_zero_pair bytes 95 width zero (Or.inr rfl) stack x y⟩

-- The empty immediate is PUSH0; retains opcode boundaries and two stack slots.
theorem certify_push0_dup : GolfLiterals.LocalCertificate [95, 128] [95, 95] := by
  exact certify_zero_pair [] (by decide +kernel) rfl

-- Preserve the original PUSH1-specific lemmas as instances of the general rule.
theorem zero_dup_before (stack : List Golf.Word) (x y : Golf.Word) :
    GolfBounded.run 4 [96, 0, 128] stack x y =
      if stack.length ≤ 1022 then some (0 :: 0 :: stack) else none := by
  exact bounded_zero_pair [0] 128 (by decide +kernel) rfl (Or.inl rfl) stack x y

theorem zero_dup_after (stack : List Golf.Word) (x y : Golf.Word) :
    GolfBounded.run 4 [96, 0, 95] stack x y =
      if stack.length ≤ 1022 then some (0 :: 0 :: stack) else none := by
  exact bounded_zero_pair [0] 95 (by decide +kernel) rfl (Or.inr rfl) stack x y

theorem zero_dup_complete_before : GolfComposition.Complete [96, 0, 128] 2 :=
  complete_zero_pair [0] 128 (by decide +kernel) (Or.inl rfl)

theorem zero_dup_complete_after : GolfComposition.Complete [96, 0, 95] 2 :=
  complete_zero_pair [0] 95 (by decide +kernel) (Or.inr rfl)

theorem certify_zero_dup : LocalCertificate [96, 0, 128] [96, 0, 95] :=
  certify_zero_pair [0] (by decide +kernel) rfl

end GolfLiterals
