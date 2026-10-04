/- Exact immutable-original batch binding. Local Golf proofs and finite layout
   checks do not establish whole-EVM execution or gas equivalence. -/
namespace GolfGenericWindowBatch
open GolfLayout

-- The list index binds a typed local proof to every actual site. Parameters may
-- differ between sites; sharing a byte-pair proof never drops an occurrence.
inductive CertifiedLocals : List Site → Type where
 | nil : CertifiedLocals []
 | cons {site : Site} {sites : List Site} {required : Nat} {delta : Int}
     {peak beforeOps afterOps : Nat}
     (localProof : GolfGenericWindow.GenericLocal site required delta peak beforeOps afterOps)
     (tail : CertifiedLocals sites) : CertifiedLocals (site::sites)

def exterior (sites : List Site) (rows : List GolfGenericWindow.Row) :=
 rows.filter (fun row => !(sites.any (fun site => GolfGenericWindow.inSite site row.1)))

-- applySites enforces canonical order, disjoint nonempty ranges, equal local
-- lengths, and exact original slices. Only certified sites may hide scan rows.
abbrev StructuralChecks (original candidate : List Nat) (sites : List Site)
 (copies : List CodeCopy) : Prop :=
 sites ≠ [] ∧
 original.all (fun b => b<256) = true ∧
 candidate.all (fun b => b<256) = true ∧
 applySites original sites = some candidate ∧
 original.length = candidate.length ∧
 aligned sites ((scan original).map (fun row => row.1) ++ [original.length]) = true ∧
 aligned sites ((scan candidate).map (fun row => row.1) ++ [candidate.length]) = true ∧
 exterior sites (scan original) = exterior sites (scan candidate) ∧
 GolfGenericWindow.jumps (scan original) = GolfGenericWindow.jumps (scan candidate) ∧
 sites.all (fun site => GolfGenericWindow.noInterior site (scan original)) = true ∧
 sites.all (fun site => GolfGenericWindow.noInterior site (scan candidate)) = true ∧
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

structure Artifact (original candidate : List Nat) (sites : List Site)
 (copies : List CodeCopy) where
 localProofs : CertifiedLocals sites
 structural : StructuralChecks original candidate sites copies

def checkStructure (original candidate : List Nat) (sites : List Site)
 (copies : List CodeCopy) : Bool := decide (StructuralChecks original candidate sites copies)

theorem checkStructure_sound {original candidate sites copies}
 (checked : checkStructure original candidate sites copies = true) :
 StructuralChecks original candidate sites copies := of_decide_eq_true checked

def certify {original candidate sites copies}
 (localProofs : CertifiedLocals sites)
 (checked : checkStructure original candidate sites copies = true) :
 Artifact original candidate sites copies := ⟨localProofs,checkStructure_sound checked⟩

theorem copies_valid {original candidate sites copies}
 (h : StructuralChecks original candidate sites copies) : CodeCopyArtifact original candidate copies := by
 rcases h with ⟨_,_,_,_,_,_,_,_,_,_,_,prefixes,bounds,bytes,_⟩
 exact ⟨prefixes,bounds,bytes⟩
end GolfGenericWindowBatch
