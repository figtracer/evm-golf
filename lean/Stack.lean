/-!
Operational stack bounds for the small Golf model. Each decoded instruction
uses Golf.run for its word semantics; the 1,024-word limit is checked at every
instruction boundary, including after PUSH and before the following opcode.
This does not model gas or establish correspondence with the full EVM.
-/

namespace GolfBounded

-- The empty-code boundary is checked too, so successful outputs fit the limit.
def run : Nat → List Nat → List Golf.Word → Golf.Word → Golf.Word → Option (List Golf.Word)
  | 0, _, _, _, _ => none
  | fuel + 1, code, stack, x, y =>
    if stack.length > 1024 then none
    else match code with
    | [] => some stack
    | op :: rest =>
      let size := if 96 ≤ op ∧ op ≤ 127 then op - 95 else 0
      match Golf.run 2 (op :: rest.take size) stack x y with
      | none => none
      | some next => run fuel (rest.drop size) next x y

-- A complete PUSH of any width, followed by one binary instruction.
def fragment (bytes : List Nat) (op : Nat) : List Nat :=
  (95 + bytes.length) :: (bytes ++ [op])

theorem fragment_bridge (bytes : List Nat) (op : Nat) (stack : List Golf.Word)
    (x y : Golf.Word) (width : bytes.length ≤ 32)
    (binary : op = 1 ∨ op = 2 ∨ op = 22 ∨ op = 27) :
    run ((fragment bytes op).length + 1) (fragment bytes op) stack x y =
      if stack.length < 1024 then
        Golf.run ((fragment bytes op).length + 1) (fragment bytes op) stack x y
      else none := by
  cases bytes with
  | nil =>
    simp only [fragment, List.length_nil, Nat.add_zero, List.nil_append,
      List.length_cons, Nat.reduceAdd]
    rcases binary with rfl | rfl | rfl | rfl <;>
      cases stack with
      | nil => simp [run, Golf.run]
      | cons a tail => simp [run, Golf.run] <;> (repeat' split) <;> simp_all <;> omega
  | cons byte bytes =>
    have push : 96 ≤ 95 + (byte :: bytes).length ∧ 95 + (byte :: bytes).length ≤ 127 := by
      simp only [List.length_cons] at *
      omega
    have size : 95 + (byte :: bytes).length - 95 = (byte :: bytes).length := by omega
    simp only [List.length_cons] at push size width
    rcases binary with rfl | rfl | rfl | rfl <;>
      cases stack with
      | nil => simp [fragment, run, Golf.run, push, size]
      | cons a tail => simp [fragment, run, Golf.run, push, size] <;> (repeat' split) <;> simp_all <;> omega

theorem fragment_underflow (bytes : List Nat) (op : Nat) (x y : Golf.Word)
    (width : bytes.length ≤ 32)
    (binary : op = 1 ∨ op = 2 ∨ op = 22 ∨ op = 27) :
    Golf.run ((fragment bytes op).length + 1) (fragment bytes op) [] x y = none := by
  cases bytes with
  | nil =>
    rcases binary with rfl | rfl | rfl | rfl <;> simp [fragment, Golf.run]
  | cons byte bytes =>
    have push : 96 ≤ 95 + (bytes.length + 1) ∧ 95 + (bytes.length + 1) ≤ 127 := by
      simp only [List.length_cons] at width
      omega
    rcases binary with rfl | rfl | rfl | rfl <;> simp [fragment, Golf.run, push]

structure FragmentEquivalent (before after : List Nat) : Prop where
  equal : ∀ stack x y,
    run (before.length + 1) before stack x y = run (after.length + 1) after stack x y
  success : ∀ a tail x y, (a :: tail).length < 1024 →
    ∃ output, run (before.length + 1) before (a :: tail) x y = some output ∧
      run (after.length + 1) after (a :: tail) x y = some output
  underflow : ∀ x y,
    run (before.length + 1) before [] x y = none ∧
      run (after.length + 1) after [] x y = none
  overflow : ∀ stack x y, 1024 ≤ stack.length →
    run (before.length + 1) before stack x y = none ∧
      run (after.length + 1) after stack x y = none

-- Two literal pushes need two free slots, including on an empty input stack.
structure LiteralEquivalent (before after : List Nat) : Prop where
  equal : ∀ stack x y,
    run (before.length + 1) before stack x y = run (after.length + 1) after stack x y
  success : ∀ stack x y, stack.length ≤ 1022 →
    ∃ output, run (before.length + 1) before stack x y = some output ∧
      run (after.length + 1) after stack x y = some output
  overflow : ∀ stack x y, 1023 ≤ stack.length →
    run (before.length + 1) before stack x y = none ∧
      run (after.length + 1) after stack x y = none

-- A proved bridge, never a profile-based definition of execution.
structure Behavior (code : List Nat) : Prop where
  bridge : ∀ stack x y, run (code.length + 1) code stack x y =
    if stack.length < 1024 then Golf.run (code.length + 1) code stack x y else none
  underflow : ∀ x y, Golf.run (code.length + 1) code [] x y = none

theorem push_binary (bytes : List Nat) (op : Nat) (width : bytes.length ≤ 32)
    (binary : op = 1 ∨ op = 2 ∨ op = 22 ∨ op = 27) : Behavior (fragment bytes op) :=
  ⟨fun stack x y => fragment_bridge bytes op stack x y width binary,
    fun x y => fragment_underflow bytes op x y width binary⟩

theorem of_unbounded {before after : List Nat}
    (beforeBehavior : Behavior before) (afterBehavior : Behavior after)
    (equivalent : ∀ (a x y : Golf.Word) (tail : List Golf.Word),
      ∃ output, Golf.run (before.length + 1) before (a :: tail) x y = some output ∧
        Golf.run (after.length + 1) after (a :: tail) x y = some output) :
    FragmentEquivalent before after := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro stack x y
    rw [beforeBehavior.bridge, afterBehavior.bridge]
    split
    · cases stack with
      | nil => rw [beforeBehavior.underflow, afterBehavior.underflow]
      | cons a tail =>
        obtain ⟨output, lhs, rhs⟩ := equivalent a x y tail
        rw [lhs, rhs]
    · rfl
  · intro a tail x y height
    rw [beforeBehavior.bridge, afterBehavior.bridge]
    simp only [height, ↓reduceIte]
    exact equivalent a x y tail
  · intro x y
    rw [beforeBehavior.bridge, afterBehavior.bridge]
    simp only [List.length_nil, Nat.reduceLT, ↓reduceIte]
    exact ⟨beforeBehavior.underflow x y, afterBehavior.underflow x y⟩
  · intro stack x y height
    rw [beforeBehavior.bridge, afterBehavior.bridge]
    simp only [show ¬stack.length < 1024 by omega, ↓reduceIte, and_self]

end GolfBounded
