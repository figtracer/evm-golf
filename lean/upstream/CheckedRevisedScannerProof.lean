import CheckedScannerComplete
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfScannerSpec
namespace RevisedScannerProof

theorem checked_of_scan (fuel : Nat) (code : ByteArray) (pc : Nat) (targets : List Nat)
    (checked : scan fuel code pc = some targets) (initial : Array UInt256) :
    D_J_checked fuel code pc initial = some (initial ++ (targets.map UInt256.ofNat).toArray) := by
  induction fuel generalizing pc targets initial with
  | zero => simp [scan] at checked
  | succ fuel ih =>
    cases decoded : parsed code pc with
    | none =>
      have result : targets = [] := by simpa [scan, decoded] using checked.symm
      have decodedRaw := decoded
      unfold parsed at decodedRaw
      simp [D_J_checked, decodedRaw, result]
    | some op =>
      cases tailResult : scan fuel code (next pc op) with
      | none => simp [scan, decoded, tailResult] at checked
      | some rest =>
        have result : (if op = .JUMPDEST then pc :: rest else rest) = targets := by
          simpa [scan, decoded, tailResult] using checked
        rw [← result]
        have decodedRaw := decoded
        unfold parsed at decodedRaw
        by_cases hit : op = .JUMPDEST
        · have tailProof := ih (next pc op) rest tailResult (initial.push (UInt256.ofNat pc))
          have order : initial.push (UInt256.ofNat pc) ++ (rest.map UInt256.ofNat).toArray =
              initial ++ ((pc :: rest).map UInt256.ofNat).toArray := by
            apply Array.toList_inj.mp
            simp [List.append_assoc]
          simpa [D_J_checked, decodedRaw, hit, next, order] using tailProof
        · have tailProof := ih (next pc op) rest tailResult initial
          simpa [D_J_checked, decodedRaw, hit, next] using tailProof

theorem checked_complete (code : ByteArray) (pc : Nat) (initial : Array UInt256)
    (fuel : Nat) (budget : code.size - pc + 1 ≤ fuel) :
    ∃ result, D_J_checked fuel code pc initial = some result := by
  obtain ⟨targets, checked⟩ := scan_complete fuel code pc budget
  exact ⟨initial ++ (targets.map UInt256.ofNat).toArray, checked_of_scan fuel code pc targets checked initial⟩

theorem bounded_wrapper (code : ByteArray) (cursor : UInt256) (targets : List Nat)
    (imageBound : code.size + 32 < UInt256.size)
    (checked : scan (code.size - cursor.toNat + 1) code cursor.toNat = some targets) :
    D_J code cursor = (targets.map UInt256.ofNat).toArray := by
  have complete := checked_of_scan _ code cursor.toNat targets checked #[]
  simp only [Array.empty_append] at complete
  simp only [D_J, imageBound, if_pos, complete]

theorem bounded_table_exists (code : ByteArray) (cursor : UInt256)
    (imageBound : code.size + 32 < UInt256.size) :
    ∃ targets, scan (code.size - cursor.toNat + 1) code cursor.toNat = some targets ∧
      D_J code cursor = (targets.map UInt256.ofNat).toArray := by
  obtain ⟨targets, checked⟩ := scan_complete (code.size - cursor.toNat + 1) code cursor.toNat (by omega)
  exact ⟨targets, checked, bounded_wrapper code cursor targets imageBound checked⟩

theorem outside_fallback (code : ByteArray) (cursor : UInt256)
    (outside : ¬ code.size + 32 < UInt256.size) :
    D_J code cursor = D_J_aux code cursor #[] := by
  simp [D_J, outside]

end RevisedScannerProof

#print axioms RevisedScannerProof.checked_of_scan
#print axioms RevisedScannerProof.checked_complete
#print axioms RevisedScannerProof.bounded_wrapper
#print axioms RevisedScannerProof.bounded_table_exists
#print axioms RevisedScannerProof.outside_fallback
