import EvmYul.EVM.Semantics
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM
namespace GolfScannerSpec

-- Natural cursors avoid wraparound; correspondence to UInt256 N is a separate obligation.
def parsed (code : ByteArray) (pc : Nat) : Option (Operation .EVM) :=
  code.get? pc >>= parseInstr

def next (pc : Nat) (op : Operation .EVM) : Nat :=
  pc + 1 + argOnNBytesOfInstr op

theorem next_progress (pc : Nat) (op : Operation .EVM) : pc < next pc op := by
  unfold next
  omega

-- None means budget exhaustion, never an accepted incomplete table.
-- A missing byte terminates successfully; unknown bytes parse as INVALID and advance.
def scan : Nat → ByteArray → Nat → Option (List Nat)
  | 0, _, _ => none
  | fuel+1, code, pc =>
    match parsed code pc with
    | none => some []
    | some op => do
      let rest ← scan fuel code (next pc op)
      pure (if op = .JUMPDEST then pc :: rest else rest)

-- Finite, completed traversal specification, independent of opaque D_J_aux.
inductive ScanTrace (code : ByteArray) : Nat → List Nat → Prop where
  | stop {pc} (missing : parsed code pc = none) : ScanTrace code pc []
  | step {pc op rest} (decoded : parsed code pc = some op)
      (tail : ScanTrace code (next pc op) rest) :
      ScanTrace code pc (if op = .JUMPDEST then pc :: rest else rest)

-- A reachable scanner boundary, not EVM execution reachability.
inductive Boundary (code : ByteArray) : Nat → Nat → Prop where
  | here {pc} (decoded : parsed code pc = some .JUMPDEST) : Boundary code pc pc
  | later {pc op destination} (decoded : parsed code pc = some op)
      (tail : Boundary code (next pc op) destination) : Boundary code pc destination

theorem scan_sound (fuel : Nat) (code : ByteArray) (pc : Nat) (destinations : List Nat)
    (checked : scan fuel code pc = some destinations) : ScanTrace code pc destinations := by
  induction fuel generalizing pc destinations with
  | zero => simp [scan] at checked
  | succ fuel ih =>
    cases decoded : parsed code pc with
    | none =>
      simp [scan, decoded] at checked
      subst destinations
      exact ScanTrace.stop decoded
    | some op =>
      cases tail : scan fuel code (next pc op) with
      | none => simp [scan, decoded, tail] at checked
      | some rest =>
        have trace := ih (next pc op) rest tail
        have result : (if op = .JUMPDEST then pc :: rest else rest) = destinations := by
          simpa [scan, decoded, tail] using checked
        rw [← result]
        exact ScanTrace.step decoded trace

theorem member_boundary {code pc destinations destination}
    (trace : ScanTrace code pc destinations) (member : destination ∈ destinations) :
    Boundary code pc destination := by
  induction trace with
  | stop missing => simp at member
  | @step pc op rest decoded tail ih =>
    by_cases hit : op = .JUMPDEST
    · subst op
      simp only [ite_true, List.mem_cons] at member
      rcases member with equal | member
      · subst destination
        exact Boundary.here decoded
      · exact Boundary.later decoded (ih member)
    · simp only [if_neg hit] at member
      exact Boundary.later decoded (ih member)

theorem boundary_decoded {code pc destination} (boundary : Boundary code pc destination) :
    parsed code destination = some .JUMPDEST := by
  induction boundary with
  | here decoded => exact decoded
  | later decoded tail ih => exact ih

theorem boundary_not_before {code pc destination} (boundary : Boundary code pc destination) :
    pc ≤ destination := by
  induction boundary with
  | here decoded => omega
  | @later pc op destination decoded tail ih =>
    have progress := next_progress pc op
    omega

end GolfScannerSpec

#print axioms GolfScannerSpec.next_progress
#print axioms GolfScannerSpec.scan_sound
#print axioms GolfScannerSpec.member_boundary
#print axioms GolfScannerSpec.boundary_decoded
#print axioms GolfScannerSpec.boundary_not_before
