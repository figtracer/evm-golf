namespace GolfGenericWindow
open GolfLayout

def checkStructure (original candidate : List Nat) (site : Site)
 (copies : List CodeCopy) : Bool := decide (StructuralChecks original candidate site copies)

theorem checkStructure_sound {original candidate site copies}
 (checked : checkStructure original candidate site copies = true) :
 StructuralChecks original candidate site copies := by
 exact of_decide_eq_true checked

-- The Boolean checker never manufactures a local proof for an unknown shape.
def certify {original candidate site copies required delta peak beforeOps afterOps}
 (localProof : GenericLocal site required delta peak beforeOps afterOps)
 (checked : checkStructure original candidate site copies = true) :
 GenericWindowArtifact original candidate site copies required delta peak beforeOps afterOps :=
 ⟨localProof,checkStructure_sound checked⟩
end GolfGenericWindow
