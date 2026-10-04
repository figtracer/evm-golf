/-! Shared PUSH-aware layout scan used by both certificate toolchains. -/
namespace GolfLayout

-- PUSH data is skipped even when its final immediate is truncated. The scanner
-- describes the entire artifact, including unreachable bytes and metadata.
def scanAux : Nat → Nat → List Nat → List (Nat × Nat × Bool)
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | fuel + 1, pc, op :: rest =>
    let immediate := if 96 ≤ op ∧ op ≤ 127 then op - 95 else 0
    (pc, immediate + 1, op == 91) ::
      scanAux fuel (pc + immediate + 1) (rest.drop immediate)

def scan (code : List Nat) : List (Nat × Nat × Bool) :=
  scanAux (code.length + 1) 0 code

end GolfLayout

namespace GolfWindowArtifact

abbrev Row := Nat × Nat × Bool
def jumpTargets (rows : List Row) := (rows.filter (fun row => row.2.2)).map (fun row => row.1)

end GolfWindowArtifact
