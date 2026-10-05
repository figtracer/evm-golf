/- Scan row bounds and shared-gap lemmas for generated batch certificates. -/
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
