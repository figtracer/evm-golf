import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega
import LayoutScanner
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace GolfLayout
inductive CompleteScanPrefix : List Nat → Nat → Prop where
 | nil : CompleteScanPrefix [] 0
 | cons (op : Nat) (immediate rest : List Nat) (steps : Nat)
   (width : immediate.length = if 96 ≤ op ∧ op ≤ 127 then op-95 else 0)
   (tail : CompleteScanPrefix rest steps) :
   CompleteScanPrefix (op::(immediate++rest)) (steps+1)

theorem scanAux_suffix {code : List Nat} {steps : Nat}
 (complete : CompleteScanPrefix code steps) (fuel pc : Nat) (suffix : List Nat) :
 scanAux (steps+fuel) pc (code++suffix) =
 scanAux steps pc code ++ scanAux fuel (pc+code.length) suffix := by
 induction complete generalizing pc with
 | nil => simp only [Nat.zero_add,List.nil_append,List.length_nil,Nat.add_zero,scanAux]
 | cons op immediate rest steps width tail ih =>
   simp only [Nat.succ_add, List.cons_append, List.append_assoc]
   simp only [scanAux, ← width, List.drop_left]
   rw [ih]
   simp [List.length_cons, List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

-- Fuel bounds use byte length, hence also cover truncated final PUSH data.
-- Unlike CompleteScanPrefix, no completeness assumption is needed for suffix.
theorem scanAux_sufficient (fuel other pc : Nat) (code : List Nat)
    (enough : code.length ≤ fuel) (otherEnough : code.length ≤ other) :
    scanAux fuel pc code = scanAux other pc code := by
  induction fuel generalizing other pc code with
  | zero =>
    have empty : code = [] := by
      cases code with
      | nil => rfl
      | cons op rest => simp only [List.length_cons] at enough; omega
    subst code
    cases other <;> rfl
  | succ fuel ih =>
    cases code with
    | nil => cases other <;> rfl
    | cons op rest =>
      cases other with
      | zero => simp only [List.length_cons] at otherEnough; omega
      | succ other =>
        simp only [List.length_cons] at enough otherEnough
        simp only [scanAux]
        congr 1
        apply ih
        · simp only [List.length_drop]; omega
        · simp only [List.length_drop]; omega

theorem complete_steps_le_length {code : List Nat} {steps : Nat}
    (complete : CompleteScanPrefix code steps) : steps ≤ code.length := by
  induction complete with
  | nil => simp
  | cons op immediate rest steps width tail ih =>
    simp only [List.length_cons,List.length_append]
    omega

end GolfLayout

namespace GolfLayout
structure CompleteChunk where
  code : List Nat
  steps : Nat
  complete : CompleteScanPrefix code steps

def chunkBytes : List CompleteChunk → List Nat
  | [] => []
  | chunk :: chunks => chunk.code ++ chunkBytes chunks

def chunkSteps : List CompleteChunk → Nat
  | [] => 0
  | chunk :: chunks => chunk.steps + chunkSteps chunks

def chunkRows (pc : Nat) : List CompleteChunk → List (Nat × Nat × Bool)
  | [] => []
  | chunk :: chunks => scanAux chunk.steps pc chunk.code ++ chunkRows (pc + chunk.code.length) chunks

theorem scan_chunks (chunks : List CompleteChunk) (fuel pc : Nat) (tail : List Nat) :
    scanAux (chunkSteps chunks + fuel) pc (chunkBytes chunks ++ tail) =
    chunkRows pc chunks ++ scanAux fuel (pc + (chunkBytes chunks).length) tail := by
  induction chunks generalizing pc with
  | nil => simp only [chunkSteps, chunkBytes, chunkRows, Nat.zero_add, List.nil_append, List.length_nil, Nat.add_zero]
  | cons chunk chunks ih =>
    simp only [chunkSteps, chunkBytes, chunkRows, Nat.add_assoc, List.append_assoc]
    rw [scanAux_suffix chunk.complete, ih]
    simp only [List.length_append, Nat.add_assoc]

theorem chunkSteps_le_length (chunks : List CompleteChunk) :
    chunkSteps chunks ≤ (chunkBytes chunks).length := by
  induction chunks with
  | nil => simp [chunkSteps, chunkBytes]
  | cons chunk chunks ih =>
    have h := complete_steps_le_length chunk.complete
    simp only [chunkSteps, chunkBytes, List.length_append]
    omega

theorem scan_complete_chunks (chunks : List CompleteChunk) (tail : List Nat) :
    scan (chunkBytes chunks ++ tail) = chunkRows 0 chunks ++
      scanAux tail.length (chunkBytes chunks).length tail := by
  have bound := chunkSteps_le_length chunks
  let fuel := (chunkBytes chunks ++ tail).length + 1
  have residual : tail.length ≤ fuel - chunkSteps chunks := by
    dsimp [fuel]
    simp only [List.length_append]
    omega
  have split : fuel = chunkSteps chunks + (fuel - chunkSteps chunks) := by
    dsimp [fuel]
    simp only [List.length_append]
    omega
  change scanAux fuel 0 (chunkBytes chunks ++ tail) = _
  rw [split, scan_chunks]
  rw [scanAux_sufficient (fuel - chunkSteps chunks) tail.length
    (0 + (chunkBytes chunks).length) tail residual (Nat.le_refl _)]
  simp only [Nat.zero_add]
end GolfLayout



#print axioms GolfLayout.scanAux_suffix
#print axioms GolfLayout.scanAux_sufficient
#print axioms GolfLayout.complete_steps_le_length
#print axioms GolfLayout.scan_chunks
#print axioms GolfLayout.chunkSteps_le_length
#print axioms GolfLayout.scan_complete_chunks
