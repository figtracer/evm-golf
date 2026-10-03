/-!
Reflect exact MUL identities and two-literal AND/SHL folds into the local
unbounded, bounded and contextual certificate propositions. The checker validates
actual byte lists; it does not define a substitute execution semantics.
-/
namespace GolfReflected

structure LocalCertificate (before after : List Nat) : Prop where
  unbounded : GolfLayout.FragmentEquivalent before after
  bounded : GolfBounded.FragmentEquivalent before after
  contextual : GolfComposition.ContextEquivalent before after

-- Reduce the actual PUSH before unfolding the following concrete binary opcode.
theorem run_fragment (bytes : List Nat) (op : Nat)
    (width : bytes.length ≤ 32)
    (binary : op = 1 ∨ op = 2 ∨ op = 22 ∨ op = 27)
    (a x y : Golf.Word) (tail : List Golf.Word) :
    Golf.run ((GolfBounded.fragment bytes op).length + 1)
        (GolfBounded.fragment bytes op) (a :: tail) x y =
      Golf.run 2 [op] (BitVec.ofNat 256 (Golf.immediate bytes) :: a :: tail) x y := by
  by_cases empty : bytes = []
  · subst bytes
    rfl
  · have positive : 0 < bytes.length := by cases bytes <;> simp_all
    have push : 96 ≤ 95 + bytes.length ∧ 95 + bytes.length ≤ 127 := by omega
    have notPush0 : 95 + bytes.length ≠ 95 := by omega
    have size : 95 + bytes.length - 95 = bytes.length := by omega
    simp only [GolfBounded.fragment, List.length_cons, List.length_append,
      List.length_nil, Nat.add_zero]
    rw [Golf.run]
    simp only [notPush0, push, size, ite_false, ite_true]
    simp only [List.length_append, List.length_cons, List.length_nil,
      Nat.le_add_right, ite_true, List.take_left, List.drop_left]
    rcases binary with rfl | rfl | rfl | rfl <;> simp [Golf.run]

theorem mul_zero_fragment (before after : List Nat)
    (beforeWidth : before.length ≤ 32) (afterWidth : after.length ≤ 32)
    (beforeValue : Golf.immediate before = 0) (afterValue : Golf.immediate after = 0) :
    GolfLayout.FragmentEquivalent
      (GolfBounded.fragment before 2) (GolfBounded.fragment after 22) := by
  intro a x y tail
  refine ⟨0 :: tail, ?_, ?_⟩
  · rw [run_fragment before 2 beforeWidth (by decide +kernel)]
    simp [Golf.run, beforeValue]
  · rw [run_fragment after 22 afterWidth (by decide +kernel)]
    simp [Golf.run, afterValue]

theorem mul_one_fragment (before after : List Nat)
    (beforeWidth : before.length ≤ 32) (afterWidth : after.length ≤ 32)
    (beforeValue : Golf.immediate before = 1) (afterValue : Golf.immediate after = 0) :
    GolfLayout.FragmentEquivalent
      (GolfBounded.fragment before 2) (GolfBounded.fragment after 1) := by
  intro a x y tail
  refine ⟨a :: tail, ?_, ?_⟩
  · rw [run_fragment before 2 beforeWidth (by decide +kernel)]
    simp [Golf.run, beforeValue]
  · rw [run_fragment after 1 afterWidth (by decide +kernel)]
    simp [Golf.run, afterValue]

theorem mul_power_fragment (before after : List Nat) (exponent : Nat)
    (beforeWidth : 0 < before.length ∧ before.length ≤ 32)
    (afterWidth : 0 < after.length ∧ after.length ≤ 32)
    (beforeValue : Golf.immediate before = 2 ^ exponent)
    (afterValue : Golf.immediate after = exponent) (exponentBound : exponent < 256) :
    GolfLayout.FragmentEquivalent
      (GolfBounded.fragment before 2) (GolfBounded.fragment after 27) := by
  intro a x y tail
  simpa only [GolfBounded.fragment, List.length_cons, List.length_append,
    List.length_nil, Nat.add_zero, Nat.add_assoc] using
    GolfProof.mul_power_fragment before after exponent beforeWidth afterWidth
      beforeValue afterValue exponentBound a x y tail

theorem complete_push_binary (bytes : List Nat) (op : Nat)
    (width : bytes.length ≤ 32)
    (binary : op = 1 ∨ op = 2 ∨ op = 22 ∨ op = 27) :
    GolfComposition.Complete (GolfBounded.fragment bytes op) 2 := by
  apply GolfComposition.Complete.step (op := 95 + bytes.length) (immediate := bytes)
  · change bytes.length = (if 96 ≤ 95 + bytes.length ∧ 95 + bytes.length ≤ 127
      then 95 + bytes.length - 95 else 0)
    split <;> omega
  · apply GolfComposition.Complete.step (op := op) (immediate := [])
    · rcases binary with rfl | rfl | rfl | rfl <;> decide +kernel
    · exact GolfComposition.Complete.nil

-- Both execution models and arbitrary complete contexts are transported once.
theorem certify_push_binary (before after : List Nat) (afterOp : Nat)
    (beforeWidth : before.length ≤ 32) (afterWidth : after.length ≤ 32)
    (afterBinary : afterOp = 1 ∨ afterOp = 2 ∨ afterOp = 22 ∨ afterOp = 27)
    (equivalent : GolfLayout.FragmentEquivalent
      (GolfBounded.fragment before 2) (GolfBounded.fragment after afterOp)) :
    LocalCertificate (GolfBounded.fragment before 2) (GolfBounded.fragment after afterOp) := by
  have bounded := GolfBounded.of_unbounded
    (GolfBounded.push_binary before 2 beforeWidth (by decide +kernel))
    (GolfBounded.push_binary after afterOp afterWidth afterBinary) equivalent
  exact ⟨equivalent, bounded, GolfComposition.context_of_fragment
    (complete_push_binary before 2 beforeWidth (by decide +kernel))
    (complete_push_binary after afterOp afterWidth afterBinary) bounded⟩

-- Extraction is only a proposed immediate slice. Exact reconstruction below
-- independently checks the actual PUSH opcode, immediate extent and binary op.
def immediatePart (code : List Nat) : List Nat :=
  code.drop 1 |>.take (code.length - 2)

def checkLocal (site : GolfLayout.Site) : Bool :=
  let before := immediatePart site.before
  let after := immediatePart site.after
  let exponent := Golf.immediate after
  decide (before.length ≤ 32) &&
    (decide (after.length ≤ 32) &&
      (decide (site.before = GolfBounded.fragment before 2) &&
        ((decide (site.after = GolfBounded.fragment after 22) &&
            (decide (Golf.immediate before = 0) && decide (Golf.immediate after = 0))) ||
          ((decide (site.after = GolfBounded.fragment after 1) &&
              (decide (Golf.immediate before = 1) && decide (Golf.immediate after = 0))) ||
            (if exponent < 256 then
              decide (0 < before.length) &&
                (decide (0 < after.length) &&
                  (decide (site.after = GolfBounded.fragment after 27) &&
                    decide (Golf.immediate before = 2 ^ exponent)))
             else false)))))

theorem checkLocal_sound (site : GolfLayout.Site) (checked : checkLocal site = true) :
    LocalCertificate site.before site.after := by
  simp only [checkLocal, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at checked
  rcases checked with ⟨beforeWidth, afterWidth, beforeCode, alternatives⟩
  rcases alternatives with zero | one | power
  · rcases zero with ⟨afterCode, beforeValue, afterValue⟩
    rw [beforeCode, afterCode]
    exact certify_push_binary _ _ 22 beforeWidth afterWidth (by decide +kernel)
      (mul_zero_fragment _ _ beforeWidth afterWidth beforeValue afterValue)
  · rcases one with ⟨afterCode, beforeValue, afterValue⟩
    rw [beforeCode, afterCode]
    exact certify_push_binary _ _ 1 beforeWidth afterWidth (by decide +kernel)
      (mul_one_fragment _ _ beforeWidth afterWidth beforeValue afterValue)
  · split at power
    · rename_i exponentBound
      simp only [Bool.and_eq_true, decide_eq_true_eq] at power
      rcases power with ⟨beforePositive, afterPositive, afterCode, beforeValue⟩
      rw [beforeCode, afterCode]
      exact certify_push_binary _ _ 27 beforeWidth afterWidth (by decide +kernel)
        (mul_power_fragment _ _ _ ⟨beforePositive, beforeWidth⟩
          ⟨afterPositive, afterWidth⟩ beforeValue rfl exponentBound)
    · cases power

-- Each immediate is only a proposed slice; exact reconstructed code and widths
-- below reject truncated PUSHs, extra instructions and malformed opcodes.
def firstPart (code : List Nat) : List Nat :=
  code.drop 1 |>.take (code.head! - 95)

def secondPart (code : List Nat) : List Nat :=
  firstPart (code.drop ((firstPart code).length + 1))

def checkLiteral (site : GolfLayout.Site) : Bool :=
  let first := firstPart site.before
  let second := secondPart site.before
  let folded := firstPart site.after
  let discard := secondPart site.after
  let op := site.before.getLast!
  decide (first.length ≤ 32) &&
    (decide (second.length ≤ 32) &&
      (decide (folded.length = first.length) &&
        (decide (discard.length = second.length) &&
          (decide (op = 22 ∨ op = 27) &&
            (decide (site.before = GolfLiterals.code first second op) &&
              (decide (site.after = GolfLiterals.code folded discard 80) &&
                decide (GolfLiterals.word folded =
                  if op = 22 then GolfLiterals.word second &&& GolfLiterals.word first
                  else GolfLiterals.word first <<< (GolfLiterals.word second).toNat)))))))

theorem checkLiteral_sound (site : GolfLayout.Site) (checked : checkLiteral site = true) :
    GolfLiterals.LocalCertificate site.before site.after := by
  simp only [checkLiteral, Bool.and_eq_true, decide_eq_true_eq] at checked
  rcases checked with ⟨firstWidth, secondWidth, foldedWidth, discardWidth,
    operation, beforeCode, afterCode, value⟩
  rw [beforeCode, afterCode]
  exact GolfLiterals.certify _ _ _ _ _ firstWidth secondWidth
    (by omega) (by omega) operation value

-- Only the exact zero/DUP1 pair is admitted, not arbitrary stack rewrites.
def checkZeroDup (site : GolfLayout.Site) : Bool :=
  decide (site.before = [96, 0, 128]) && decide (site.after = [96, 0, 95])

theorem checkZeroDup_sound (site : GolfLayout.Site) (checked : checkZeroDup site = true) :
    GolfLiterals.LocalCertificate site.before site.after := by
  simp only [checkZeroDup, Bool.and_eq_true, decide_eq_true_eq] at checked
  rw [checked.1, checked.2]
  exact GolfLiterals.certify_zero_dup

-- Stack metadata chooses the certificate proposition, not merely a profile.
def checkSite (site : GolfLayout.Site) : Bool :=
  if site.requiredStack = 1 then checkLocal site
  else if site.requiredStack = 0 then checkLiteral site || checkZeroDup site else false

-- Structurally recursive Bool traversal; each occurrence checks its exact bytes.
def checkSites (sites : List GolfLayout.Site) : Bool := sites.all checkSite

theorem checkSites_sound (sites : List GolfLayout.Site) (checked : checkSites sites = true) :
    GolfLayout.CertifiedSites sites := by
  induction sites with
  | nil => exact GolfLayout.CertifiedSites.nil
  | cons site sites ih =>
    simp only [checkSites, List.all_cons, Bool.and_eq_true] at checked
    have localCheck := checked.1
    simp only [checkSite] at localCheck
    split at localCheck
    · rename_i required
      have localProof := checkLocal_sound site localCheck
      exact GolfLayout.CertifiedSites.cons required localProof.unbounded localProof.bounded
        localProof.contextual (ih checked.2)
    · split at localCheck
      · rename_i required
        have localProof : GolfLiterals.LocalCertificate site.before site.after := by
          simp only [Bool.or_eq_true] at localCheck
          rcases localCheck with literal | zeroDup
          · exact checkLiteral_sound site literal
          · exact checkZeroDup_sound site zeroDup
        exact GolfLayout.CertifiedSites.literalCons required localProof.unbounded localProof.bounded
          localProof.contextual (ih checked.2)
      · cases localCheck

end GolfReflected
