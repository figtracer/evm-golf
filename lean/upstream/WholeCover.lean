import WholeProgram
import WholeScan
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition

/-! Point sets as natural-number lists, checked in linear time. -/
namespace GolfWhole

def subsetSorted : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    if x = y then subsetSorted xs ys else if y < x then subsetSorted (x :: xs) ys else false

theorem subsetSorted_sound : ∀ (a b : List Nat), subsetSorted a b = true → ∀ x ∈ a, x ∈ b
  | [], _, _, x, hx => by simp at hx
  | _ :: _, [], h, _, _ => by simp [subsetSorted] at h
  | x :: xs, y :: ys, h, z, hz => by
    unfold subsetSorted at h
    by_cases e : x = y
    · rw [if_pos e] at h
      rcases List.mem_cons.mp hz with rfl | hz
      · rw [e]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (subsetSorted_sound xs ys h z hz)
    · rw [if_neg e] at h
      by_cases l : y < x
      · rw [if_pos l] at h
        exact List.mem_cons_of_mem _ (subsetSorted_sound (x :: xs) ys h z hz)
      · rw [if_neg l] at h; cases h

theorem word_beq_self (x : UInt256) : (x == x) = true := by
  obtain ⟨a⟩ := x
  have e : ((⟨a⟩ : UInt256) == ⟨a⟩) = (a == a) := rfl
  rw [e]; exact beq_self_eq_true a

theorem mem_points {l : List Nat} {x : Nat} (h : x ∈ l) :
    (l.map UInt256.ofNat).contains (UInt256.ofNat x) = true := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    simp only [List.map_cons, List.contains_cons, Bool.or_eq_true]
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl (word_beq_self _)
    · exact Or.inr (ih h)

theorem next_of {l : List Nat} {pc : UInt256} {k target : Nat}
    (sum : pc + UInt256.ofNat k = UInt256.ofNat target) (mem : target ∈ l) :
    (l.map UInt256.ofNat).contains (pc + UInt256.ofNat k) = true := by
  rw [sum]; exact mem_points mem

theorem start_of {l : List Nat} (mem : 0 ∈ l) : (l.map UInt256.ofNat).contains (UInt256.ofNat 0) = true :=
  mem_points mem

theorem jumps_points (jumps points : List Nat) (h : subsetSorted jumps points = true) :
    ∀ x, (jumps.map UInt256.ofNat).toArray.contains x = true →
      (points.map UInt256.ofNat).contains x = true := by
  have hs := subsetSorted_sound _ _ h
  intro x hx
  rw [← Array.contains_toList, List.toList_toArray] at hx
  clear h
  induction jumps with
  | nil => simp at hx
  | cons j js ih =>
    simp only [List.map_cons, List.contains_cons, Bool.or_eq_true] at hx
    rcases hx with e | e
    · rw [word_eq_of_beq e]
      exact mem_points (hs j List.mem_cons_self)
    · exact ih (fun y hy => hs y (List.mem_cons_of_mem _ hy)) e

theorem cover_app {Q : UInt256 → Prop} {l₁ l₂ : List Nat}
    (h₁ : ∀ x, (l₁.map UInt256.ofNat).contains x = true → Q x)
    (h₂ : ∀ x, (l₂.map UInt256.ofNat).contains x = true → Q x) :
    ∀ x, ((l₁ ++ l₂).map UInt256.ofNat).contains x = true → Q x := by
  intro x hx
  simp only [List.map_append, List.contains_append, Bool.or_eq_true] at hx
  rcases hx with h | h
  · exact h₁ x h
  · exact h₂ x h

#print axioms jumps_points
#print axioms next_of
#print axioms cover_app

end GolfWhole
