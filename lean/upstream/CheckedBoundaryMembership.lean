import CheckedAlignedSplice
import CheckedTableEquality
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option autoImplicit false
open EvmYul EvmYul.EVM GolfLayout GolfWindowArtifact GolfAlignedSplice
namespace GolfBoundaryMembership

-- Completeness starts at byte zero. It rules out a JUMPDEST byte hidden inside
-- PUSH data, including a PUSH straddling the proposed destination boundary.
theorem layout_member (lead suffix : List Nat) (steps : Nat)
    (complete : CompleteScanPrefix lead steps) :
    lead.length ∈ jumpTargets (scan (lead ++ (91 :: suffix))) := by
  let chunk : CompleteChunk := ⟨lead, steps, complete⟩
  have decomposition := scan_complete_chunks [chunk] (91 :: suffix)
  have split : scan (lead ++ (91 :: suffix)) =
      scanAux steps 0 lead ++ scanAux (91 :: suffix).length lead.length (91 :: suffix) := by
    simpa only [chunk, chunkBytes, chunkRows, List.append_nil, Nat.zero_add]
      using decomposition
  rw [split, targets_append]
  apply List.mem_append_right
  simp [scanAux, jumpTargets]

-- Exact complete-image list binding, not an unchecked host offset or cropped code.
-- suffix is arbitrary; no final-PUSH completeness assumption is introduced.
theorem contains_of_binding (whole lead : ByteArray) (suffix : List Nat) (steps : Nat)
    (complete : CompleteScanPrefix (lead.data.toList.map UInt8.toNat) steps)
    (binding : whole.data.toList.map UInt8.toNat =
      (lead.data.toList.map UInt8.toNat) ++ (91 :: suffix))
    (bound : whole.size + 32 < UInt256.size) :
    (D_J whole (UInt256.ofNat 0)).contains (UInt256.ofNat lead.size) = true := by
  have member : lead.size ∈ jumpTargets
      (scan (whole.data.toList.map UInt8.toNat)) := by
    rw [binding]
    simpa only [List.length_map, Array.length_toList] using
      layout_member (lead.data.toList.map UInt8.toNat) suffix steps complete
  rw [RevisedTableEquality.table_of_layout whole bound]
  simp
  refine ⟨lead.size, member, ?_⟩
  cases word : UInt256.ofNat lead.size with
  | mk value =>
    change (value == value) = true
    simp


-- ByteArray wrapper supplies the actual next-byte JUMPDEST as part of an exact
-- image equality. The only full-image rewrite is symbolic append/map, not scanning.
theorem contains_at_boundary (whole lead suffix : ByteArray) (steps : Nat)
    (complete : CompleteScanPrefix (lead.data.toList.map UInt8.toNat) steps)
    (image : whole = ByteArray.mk (lead.data ++ #[UInt8.ofNat 91] ++ suffix.data))
    (bound : whole.size + 32 < UInt256.size) :
    (D_J whole (UInt256.ofNat 0)).contains (UInt256.ofNat lead.size) = true := by
  apply contains_of_binding whole lead (suffix.data.toList.map UInt8.toNat) steps complete
  · simp [image, Array.toList_append, List.map_append, List.append_assoc]
  · exact bound

end GolfBoundaryMembership

#print axioms GolfBoundaryMembership.layout_member
#print axioms GolfBoundaryMembership.contains_of_binding
#print axioms GolfBoundaryMembership.contains_at_boundary
