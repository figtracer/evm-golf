import CheckedScannerSpec
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM
namespace GolfScannerSpec

theorem parsed_present_in_bounds (code : ByteArray) (pc : Nat) (op : Operation .EVM)
    (present : parsed code pc = some op) : pc < code.size := by
  by_contra outside
  simp [parsed, ByteArray.get?, outside] at present

theorem scan_complete (fuel : Nat) (code : ByteArray) (pc : Nat)
    (budget : code.size - pc + 1 ≤ fuel) :
    ∃ destinations, scan fuel code pc = some destinations := by
  induction fuel generalizing pc with
  | zero => omega
  | succ fuel ih =>
    cases decoded : parsed code pc with
    | none => exact ⟨[], by simp [scan, decoded]⟩
    | some op =>
      have inBounds := parsed_present_in_bounds code pc op decoded
      have progress := next_progress pc op
      have enough : code.size - next pc op + 1 ≤ fuel := by omega
      obtain ⟨rest, checked⟩ := ih (next pc op) enough
      exact ⟨if op = .JUMPDEST then pc :: rest else rest, by simp [scan, decoded, checked]⟩

theorem scan_complete_trace (code : ByteArray) (pc : Nat) :
    ∃ destinations,
      scan (code.size - pc + 1) code pc = some destinations ∧
      ScanTrace code pc destinations := by
  obtain ⟨destinations, checked⟩ := scan_complete (code.size - pc + 1) code pc (by omega)
  exact ⟨destinations, checked, scan_sound _ _ _ _ checked⟩

theorem full_image_complete (code : ByteArray) :
    ∃ destinations,
      scan (code.size + 1) code 0 = some destinations ∧
      ScanTrace code 0 destinations := by
  simpa only [Nat.sub_zero] using scan_complete_trace code 0

end GolfScannerSpec

#print axioms GolfScannerSpec.parsed_present_in_bounds
#print axioms GolfScannerSpec.scan_complete
#print axioms GolfScannerSpec.scan_complete_trace
#print axioms GolfScannerSpec.full_image_complete
