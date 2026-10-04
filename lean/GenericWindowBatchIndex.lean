/- Kernel-checked interval indexing for the unchanged batch artifact contract. -/
namespace GolfBatchIntervals
open GolfLayout
inductive Tree where
 | empty
 | node (left : Tree) (site : Site) (right : Tree)

def flatten : Tree → List Site
 | .empty => []
 | .node left site right => flatten left ++ site :: flatten right

def Valid : Tree → Prop
 | .empty => True
 | .node left site right => Valid left ∧ Valid right ∧
     (∀ s ∈ flatten left, s.pc+s.before.length ≤ site.pc) ∧
     (∀ s ∈ flatten right, site.pc+site.before.length ≤ s.pc)

def checkValid : Tree → Bool
 | .empty => true
 | .node left site right => checkValid left && (checkValid right &&
    ((flatten left).all (fun s => decide (s.pc+s.before.length ≤ site.pc)) &&
     (flatten right).all (fun s => decide (site.pc+site.before.length ≤ s.pc))))

theorem checkValid_sound (tree : Tree) (checked : checkValid tree = true) : Valid tree := by
 induction tree with
 | empty => trivial
 | node left site right ihl ihr =>
   simp only [checkValid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at checked
   exact ⟨ihl checked.1,ihr checked.2.1,checked.2.2.1,checked.2.2.2⟩

def lookup : Tree → Nat → Bool
 | .empty, _ => false
 | .node left site right, pc =>
   if pc < site.pc then lookup left pc
   else if site.pc+site.before.length ≤ pc then lookup right pc
   else true

theorem inSite_true (site : Site) (pc : Nat) :
 GolfGenericWindow.inSite site pc = true ↔ site.pc ≤ pc ∧ pc < site.pc+site.before.length := by
 simp [GolfGenericWindow.inSite]

theorem any_false (sites : List Site) (pc : Nat)
 (outside : ∀ site ∈ sites, ¬(site.pc ≤ pc ∧ pc < site.pc+site.before.length)) :
 sites.any (fun site => GolfGenericWindow.inSite site pc) = false := by
 apply List.any_eq_false.mpr
 intro site member inside
 exact outside site member ((inSite_true site pc).mp inside)

theorem lookup_eq_any (tree : Tree) (valid : Valid tree) (pc : Nat) :
 lookup tree pc = (flatten tree).any (fun site => GolfGenericWindow.inSite site pc) := by
 induction tree with
 | empty => rfl
 | node left site right ihl ihr =>
   rcases valid with ⟨vl,vr,lb,rb⟩
   have leftEq := ihl vl
   have rightEq := ihr vr
   by_cases below : pc < site.pc
   · have pivot : GolfGenericWindow.inSite site pc = false := by
       apply Bool.eq_false_iff.mpr
       intro h
       have := (inSite_true site pc).mp h
       omega
     have rightFalse := any_false (flatten right) pc (by
       intro s hs inside
       have := rb s hs
       omega)
     simp [lookup,below,flatten,List.any_append,leftEq,pivot,rightFalse]
   · by_cases above : site.pc+site.before.length ≤ pc
     · have pivot : GolfGenericWindow.inSite site pc = false := by
         apply Bool.eq_false_iff.mpr
         intro h
         have := (inSite_true site pc).mp h
         omega
       have leftFalse := any_false (flatten left) pc (by
         intro s hs inside
         have := lb s hs
         omega)
       simp [lookup,below,above,flatten,List.any_append,rightEq,pivot,leftFalse]
     · have pivot : GolfGenericWindow.inSite site pc = true :=
         (inSite_true site pc).mpr (by omega)
       simp [lookup,below,above,flatten,List.any_append,pivot]

-- All sites are bound, not merely a subset deemed useful by a host decoder.
theorem lookup_bound (tree : Tree) (sites : List Site)
 (checked : checkValid tree = true) (binding : flatten tree = sites) (pc : Nat) :
 lookup tree pc = sites.any (fun site => GolfGenericWindow.inSite site pc) := by
 rw [←binding]
 exact lookup_eq_any tree (checkValid_sound tree checked) pc

def exterior (tree : Tree) (rows : List GolfGenericWindow.Row) :=
 rows.filter (fun row => !lookup tree row.1)

theorem exterior_bound (tree : Tree) (sites : List Site)
 (checked : checkValid tree = true) (binding : flatten tree = sites)
 (rows : List GolfGenericWindow.Row) :
 exterior tree rows = GolfGenericWindowBatch.exterior sites rows := by
 unfold exterior GolfGenericWindowBatch.exterior
 apply congrArg (fun p => rows.filter p)
 funext row
 rw [lookup_bound tree sites checked binding]

end GolfBatchIntervals

namespace GolfGenericWindowBatch
theorem noInterior_row_first (sites : List GolfLayout.Site) (rows : List GolfGenericWindow.Row) :
 sites.all (fun site => GolfGenericWindow.noInterior site rows) =
 rows.all (fun row => !row.2.2 || sites.all (fun site => !(site.pc < row.1 && row.1 < site.pc+site.before.length))) := by
 apply Bool.eq_iff_iff.mpr
 simp only [GolfGenericWindow.noInterior, List.all_eq_true, Bool.or_eq_true]
 constructor
 · intro h row hr
   by_cases hj : (!row.2.2) = true
   · exact Or.inl hj
   · exact Or.inr (fun site hs => (h site hs row hr).resolve_left hj)
 · intro h site hs row hr
   rcases h row hr with hj | all
   · exact Or.inl hj
   · exact Or.inr (all site hs)
end GolfGenericWindowBatch


namespace GolfGenericWindowBatch
open GolfLayout
abbrev FastChecks (tree : GolfBatchIntervals.Tree) (original candidate : List Nat) (sites : List Site)
 (copies : List CodeCopy) : Prop :=
 sites ≠ [] ∧
 original.all (fun b => b<256) = true ∧
 candidate.all (fun b => b<256) = true ∧
 applySites original sites = some candidate ∧
 original.length = candidate.length ∧
 aligned sites ((scan original).map (fun row => row.1) ++ [original.length]) = true ∧
 aligned sites ((scan candidate).map (fun row => row.1) ++ [candidate.length]) = true ∧
 GolfBatchIntervals.exterior tree (scan original) = GolfBatchIntervals.exterior tree (scan candidate) ∧
 GolfGenericWindow.jumps (scan original) = GolfGenericWindow.jumps (scan candidate) ∧
 (scan original).all (fun row => !row.2.2 || sites.all (fun site => !(site.pc < row.1 && row.1 < site.pc+site.before.length))) = true ∧
 (scan candidate).all (fun row => !row.2.2 || sites.all (fun site => !(site.pc < row.1 && row.1 < site.pc+site.before.length))) = true ∧
 copies.all (fun copy =>
   ((scan original).map (fun row => row.1)).contains copy.prefixStart &&
   ((scan candidate).map (fun row => row.1)).contains copy.prefixStart &&
   copyPrefix original copy && copyPrefix candidate copy &&
   (original.drop copy.prefixStart).take (copy.pc+1-copy.prefixStart) ==
     (candidate.drop copy.prefixStart).take (copy.pc+1-copy.prefixStart)) = true ∧
 copies.all (fun copy => copy.source+copy.length ≤ original.length &&
   copy.source+copy.length ≤ candidate.length) = true ∧
 copies.all (fun copy => (original.drop copy.source).take copy.length ==
   (candidate.drop copy.source).take copy.length) = true ∧
 sites.all (fun site => GolfGenericWindow.protectedCopies site copies) = true

theorem fast_sound {tree original candidate sites copies}
 (valid : GolfBatchIntervals.checkValid tree = true)
 (binding : GolfBatchIntervals.flatten tree = sites)
 (checked : FastChecks tree original candidate sites copies) :
 StructuralChecks original candidate sites copies := by
 unfold FastChecks at checked
 unfold StructuralChecks
 rw [noInterior_row_first, noInterior_row_first]
 rw [← GolfBatchIntervals.exterior_bound tree sites valid binding (scan original),
     ← GolfBatchIntervals.exterior_bound tree sites valid binding (scan candidate)]
 exact checked
end GolfGenericWindowBatch
