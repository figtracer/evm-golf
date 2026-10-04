/- Kernel-checked scan decomposition across a complete prefix and arbitrary suffix.
   Shared suffix rows retain their exact decoder binding when prefix instruction
   counts differ. This is structural verification, not full-EVM correspondence. -/
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
def completeCount : Nat → List Nat → Option Nat
 | 0, _ => none
 | _+1, [] => some 0
 | fuel+1, op::rest =>
   let width := if 96 ≤ op ∧ op ≤ 127 then op-95 else 0
   if (rest.take width).length = width then
     (completeCount fuel (rest.drop width)).map (fun n => n+1)
   else none

theorem completeCount_sound (fuel : Nat) (code : List Nat) (steps : Nat)
 (checked : completeCount fuel code = some steps) : CompleteScanPrefix code steps := by
 induction fuel generalizing code steps with
 | zero => simp only [completeCount] at checked; contradiction
 | succ fuel ih =>
   cases code with
   | nil =>
     simp only [completeCount,Option.some.injEq] at checked
     subst steps
     exact .nil
   | cons op rest =>
     let w := if 96 ≤ op ∧ op ≤ 127 then op-95 else 0
     change (if (rest.take w).length = w then
       (completeCount fuel (rest.drop w)).map (fun n => n+1) else none) = some steps at checked
     by_cases enough : (rest.take w).length = w
     · rw [if_pos enough] at checked
       cases tailEq : completeCount fuel
         (rest.drop w) with
       | none => simp only [tailEq,Option.map_none] at checked; contradiction
       | some n =>
         simp only [tailEq,Option.map_some,Option.some.injEq] at checked
         subst steps
         have tail := ih _ n tailEq
         have width : (rest.take w).length =
             (if 96 ≤ op ∧ op ≤ 127 then op-95 else 0) := by
           exact enough
         simpa only [List.take_append_drop] using
           CompleteScanPrefix.cons op _ _ n width tail
     · rw [if_neg enough] at checked; contradiction
end GolfLayout

namespace GolfLayout
theorem scanAux_lower (fuel pc : Nat) (code : List Nat)
 (row : Nat × Nat × Bool) (member : row ∈ scanAux fuel pc code) : pc ≤ row.1 := by
 induction fuel generalizing pc code with
 | zero => simp only [scanAux,List.not_mem_nil] at member
 | succ fuel ih =>
   cases code with
   | nil => simp only [scanAux,List.not_mem_nil] at member
   | cons op rest =>
     simp only [scanAux,List.mem_cons] at member
     rcases member with same | later
     · subst row; exact Nat.le_refl _
     · have bound := ih _ _ later
       omega
end GolfLayout

namespace GolfLayout
theorem scanAux_upper (fuel pc : Nat) (code : List Nat)
    (row : Nat × Nat × Bool)
    (member : row ∈ scanAux fuel pc code) :
    row.1 < pc + code.length := by
  induction fuel generalizing pc code with
  | zero => simp only [scanAux, List.not_mem_nil] at member
  | succ fuel ih =>
    cases code with
    | nil => simp only [scanAux, List.not_mem_nil] at member
    | cons op rest =>
      simp only [scanAux, List.mem_cons] at member
      rcases member with same | later
      · subst row
        simp only [List.length_cons]
        omega
      · let width := if 96 ≤ op ∧ op ≤ 127 then op - 95 else 0
        change row ∈ scanAux fuel (pc + width + 1) (rest.drop width) at later
        have bound := ih (pc + width + 1) (rest.drop width) later
        cases tailEq : rest.drop width with
        | nil =>
          rw [tailEq] at later
          cases fuel <;> simp only [scanAux, List.not_mem_nil] at later
        | cons next tail =>
          have lengths : (rest.drop width).length = rest.length - width := by
            simp only [List.length_drop]
          rw [tailEq] at lengths
          simp only [List.length_cons] at lengths
          simp only [List.length_drop] at bound
          simp only [List.length_cons]
          omega
end GolfLayout
namespace GolfSharedSuffix
open GolfLayout GolfGenericWindow

theorem outside_gap (sites : List Site) (rows : List Row) (start finish : Nat)
    (bounds : ∀ row ∈ rows, start ≤ row.1 ∧ row.1 < finish)
    (disjoint : ∀ site ∈ sites, finish ≤ site.pc ∨ site.pc + site.before.length ≤ start) :
    ∀ row ∈ rows, ∀ site ∈ sites, inSite site row.1 = false := by
  intro row member site siteMember
  have range := bounds row member
  rcases disjoint site siteMember with before | after
  · have outside : ¬site.pc ≤ row.1 := by omega
    simp [inSite, outside]
  · have outside : ¬row.1 < site.pc + site.before.length := by omega
    simp [inSite, outside]

theorem exterior_gap (sites : List Site) (rows : List Row) (start finish : Nat)
    (bounds : ∀ row ∈ rows, start ≤ row.1 ∧ row.1 < finish)
    (disjoint : ∀ site ∈ sites, finish ≤ site.pc ∨ site.pc + site.before.length ≤ start) :
    GolfGenericWindowBatch.exterior sites rows = rows := by
  apply List.filter_eq_self.mpr
  intro row member
  have none : sites.any (fun site => inSite site row.1) = false := by
    apply List.any_eq_false.mpr
    intro site siteMember
    simp [outside_gap sites rows start finish bounds disjoint row member site siteMember]
  simp [none]

theorem noInterior_gap (site : Site) (rows : List Row) (start finish : Nat)
    (bounds : ∀ row ∈ rows, start ≤ row.1 ∧ row.1 < finish)
    (disjoint : finish ≤ site.pc ∨ site.pc + site.before.length ≤ start) :
    noInterior site rows = true := by
  apply List.all_eq_true.mpr
  intro row member
  have range := bounds row member
  rcases disjoint with before | after
  · have outside : ¬site.pc < row.1 := by omega
    simp [outside]
  · have outside : ¬row.1 < site.pc + site.before.length := by omega
    simp [outside]
end GolfSharedSuffix
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
    simp only [List.length_append, Nat.add_assoc, List.append_assoc]

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
