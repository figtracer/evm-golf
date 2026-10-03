/-!
Compositional execution of exact byte-list fragments in GolfBounded.run.
Complete witnesses prevent PUSH immediates from crossing segment boundaries;
fuel is normalized to a sufficient instruction count, including termination.
No gas, control-flow graph, or full-EVM correspondence is modeled here.
-/

namespace GolfComposition

-- A proof-only decoded boundary witness. Every PUSH owns all of its immediate
-- bytes inside the segment; no suffix byte can become part of that immediate.
inductive Complete : List Nat → Nat → Prop where
  | nil : Complete [] 0
  | step {op : Nat} {immediate rest : List Nat} {count : Nat} :
      immediate.length = (if 96 ≤ op ∧ op ≤ 127 then op - 95 else 0) →
      Complete rest count → Complete (op :: (immediate ++ rest)) (count + 1)

theorem count_le_length {code : List Nat} {count : Nat} (complete : Complete code count) :
    count ≤ code.length := by
  induction complete with
  | nil => simp
  | step width rest ih => simp only [List.length_cons, List.length_append]; omega

theorem fuel_stable {code : List Nat} {count : Nat} (complete : Complete code count)
    (extra : Nat) (stack : List Golf.Word) (x y : Golf.Word) :
    GolfBounded.run (count + extra + 1) code stack x y =
      GolfBounded.run (count + 1) code stack x y := by
  induction complete generalizing stack with
  | nil => simp [GolfBounded.run]
  | @step op immediate rest count width complete ih =>
    have shift : count + 1 + extra + 1 = (count + extra + 1) + 1 := by omega
    rw [shift]
    simp only [GolfBounded.run, ← width, List.take_left, List.drop_left]
    split
    · rfl
    · split
      · rfl
      · exact ih _

theorem run_append {code : List Nat} {count : Nat} (complete : Complete code count)
    (suffix : List Nat) (fuel : Nat) (stack : List Golf.Word) (x y : Golf.Word) :
    GolfBounded.run (count + fuel + 1) (code ++ suffix) stack x y =
      (GolfBounded.run (count + 1) code stack x y).bind
        (fun middle => GolfBounded.run (fuel + 1) suffix middle x y) := by
  induction complete generalizing stack with
  | nil =>
    by_cases overflow : stack.length > 1024 <;> simp [GolfBounded.run, overflow]
  | @step op immediate rest count width complete ih =>
    have shift : count + 1 + fuel + 1 = (count + fuel + 1) + 1 := by omega
    rw [shift]
    simp only [List.cons_append, List.append_assoc, GolfBounded.run, ← width,
      List.take_left, List.drop_left]
    split
    · rfl
    · split
      · rfl
      · exact ih _

theorem complete_append {left right : List Nat} {leftCount rightCount : Nat}
    (leftComplete : Complete left leftCount) (rightComplete : Complete right rightCount) :
    Complete (left ++ right) (leftCount + rightCount) := by
  induction leftComplete with
  | nil => simpa using rightComplete
  | @step op immediate rest count width complete ih =>
    have shift : count + 1 + rightCount = count + rightCount + 1 := by omega
    rw [shift]
    simpa only [List.cons_append, List.append_assoc] using Complete.step width ih

theorem byte_fuel {code : List Nat} {count : Nat} (complete : Complete code count)
    (stack : List Golf.Word) (x y : Golf.Word) :
    GolfBounded.run (code.length + 1) code stack x y =
      GolfBounded.run (count + 1) code stack x y := by
  have fuel : count + (code.length - count) + 1 = code.length + 1 := by
    have := count_le_length complete
    omega
  simpa only [fuel] using fuel_stable complete (code.length - count) stack x y

theorem replace_context {front before after suffix : List Nat}
    {prefixCount beforeCount afterCount suffixCount : Nat}
    (prefixComplete : Complete front prefixCount)
    (beforeComplete : Complete before beforeCount)
    (afterComplete : Complete after afterCount)
    (suffixComplete : Complete suffix suffixCount)
    (replacement : GolfBounded.FragmentEquivalent before after)
    (stack : List Golf.Word) (x y : Golf.Word) :
    GolfBounded.run ((front ++ (before ++ suffix)).length + 1)
        (front ++ (before ++ suffix)) stack x y =
      GolfBounded.run ((front ++ (after ++ suffix)).length + 1)
        (front ++ (after ++ suffix)) stack x y := by
  rw [byte_fuel (complete_append prefixComplete (complete_append beforeComplete suffixComplete)),
    byte_fuel (complete_append prefixComplete (complete_append afterComplete suffixComplete)),
    run_append prefixComplete, run_append prefixComplete]
  congr 1
  funext middle
  rw [run_append beforeComplete, run_append afterComplete]
  have equal := replacement.equal middle x y
  rw [byte_fuel beforeComplete, byte_fuel afterComplete] at equal
  rw [equal]

-- This is contextual equivalence inside the deliberately small Golf model,
-- not execution equivalence for arbitrary EVM contracts. Unsupported contexts
-- may fail on both sides; context_success requires an actual successful run.
def ContextEquivalent (before after : List Nat) : Prop :=
  ∀ (front suffix : List Nat) (frontCount suffixCount : Nat),
    Complete front frontCount → Complete suffix suffixCount →
    ∀ (stack : List Golf.Word) (x y : Golf.Word),
      GolfBounded.run ((front ++ (before ++ suffix)).length + 1)
          (front ++ (before ++ suffix)) stack x y =
        GolfBounded.run ((front ++ (after ++ suffix)).length + 1)
          (front ++ (after ++ suffix)) stack x y

theorem context_of_fragment {before after : List Nat} {beforeCount afterCount : Nat}
    (beforeComplete : Complete before beforeCount)
    (afterComplete : Complete after afterCount)
    (replacement : GolfBounded.FragmentEquivalent before after) :
    ContextEquivalent before after := by
  intro front suffix frontCount suffixCount frontComplete suffixComplete stack x y
  exact replace_context frontComplete beforeComplete afterComplete suffixComplete replacement stack x y

theorem context_success {front before after suffix : List Nat}
    {frontCount suffixCount : Nat}
    (replacement : ContextEquivalent before after)
    (frontComplete : Complete front frontCount) (suffixComplete : Complete suffix suffixCount)
    (stack : List Golf.Word) (x y : Golf.Word) (output : List Golf.Word)
    (success : GolfBounded.run ((front ++ (before ++ suffix)).length + 1)
      (front ++ (before ++ suffix)) stack x y = some output) :
    GolfBounded.run ((front ++ (after ++ suffix)).length + 1)
      (front ++ (after ++ suffix)) stack x y = some output := by
  rw [← replacement front suffix frontCount suffixCount frontComplete suffixComplete]
  exact success

end GolfComposition
