import CheckedParserFacts
import CheckedScannerComplete
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfScannerSpec GolfParserFacts GolfWindowArtifact
namespace GolfScannerBridge

theorem bytes_drop_head (code : ByteArray) (pc : Nat) (inside : pc < code.size) :
    code.data.toList.drop pc = code.get pc inside :: code.data.toList.drop (pc+1) := by
  exact List.drop_eq_getElem_cons inside

theorem targets_of_success (fuel : Nat) (code : ByteArray) (pc : Nat) (targets : List Nat)
    (checked : GolfScannerSpec.scan fuel code pc = some targets) :
    jumpTargets (GolfLayout.scanAux fuel pc ((code.data.toList.drop pc).map UInt8.toNat)) = targets := by
  induction fuel generalizing pc targets with
  | zero => simp [GolfScannerSpec.scan] at checked
  | succ fuel ih =>
    by_cases inside : pc < code.size
    · let byte := code.get pc inside
      let op := (parseInstr byte).getD .INVALID
      have decoded : parsed code pc = some op := by
        simpa only [parsed, ByteArray.get?, dif_pos inside, Option.bind_some] using parser_present byte
      cases tailResult : GolfScannerSpec.scan fuel code (next pc op) with
      | none => simp [GolfScannerSpec.scan, decoded, tailResult] at checked
      | some rest =>
        have result : (if op = .JUMPDEST then pc :: rest else rest) = targets := by
          simpa [GolfScannerSpec.scan, decoded, tailResult] using checked
        rw [← result]
        have tail := ih (next pc op) rest tailResult
        have width := parser_width byte
        have dest := parser_jumpdest byte
        rw [bytes_drop_head code pc inside]
        simp only [List.map_cons, GolfLayout.scanAux]
        change jumpTargets ((pc, (if 96 ≤ byte.toNat ∧ byte.toNat ≤ 127 then byte.toNat-95 else 0)+1,
          byte.toNat == 91) :: GolfLayout.scanAux fuel
          (pc+(if 96 ≤ byte.toNat ∧ byte.toNat ≤ 127 then byte.toNat-95 else 0)+1)
          (((code.data.toList.drop (pc+1)).map UInt8.toNat).drop
            (if 96 ≤ byte.toNat ∧ byte.toNat ≤ 127 then byte.toNat-95 else 0))) = _
        rw [← width]
        have cursor : pc + argOnNBytesOfInstr op + 1 = next pc op := by unfold next; omega
        rw [cursor]
        rw [← List.map_drop, List.drop_drop]
        change jumpTargets ((pc, argOnNBytesOfInstr op+1, byte.toNat == 91) ::
          GolfLayout.scanAux fuel (next pc op)
            ((code.data.toList.drop (next pc op)).map UInt8.toNat)) = _
        by_cases hit : op = .JUMPDEST
        · have byteHit : byte.toNat = 91 := dest.mp hit
          simpa [jumpTargets, byteHit, hit] using congrArg (List.cons pc) tail
        · have byteMiss : byte.toNat ≠ 91 := fun equal => hit (dest.mpr equal)
          simpa [jumpTargets, byteMiss, hit] using tail
    · have missing : parsed code pc = none := by simp [parsed, ByteArray.get?, inside]
      have empty : code.data.toList.drop pc = [] := List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_gt inside)
      have result : targets = [] := by simpa [GolfScannerSpec.scan, missing] using checked.symm
      simp [empty, result, GolfLayout.scanAux, jumpTargets]

theorem full_image_targets (code : ByteArray) :
    GolfScannerSpec.scan (code.size+1) code 0 =
      some (jumpTargets (GolfLayout.scan (code.data.toList.map UInt8.toNat))) := by
  obtain ⟨targets, checked, trace⟩ := full_image_complete code
  have aligned := targets_of_success (code.size+1) code 0 targets checked
  have same : jumpTargets (GolfLayout.scan (code.data.toList.map UInt8.toNat)) = targets := by
    simpa [GolfLayout.scan, ByteArray.size] using aligned
  rw [checked, same]

end GolfScannerBridge

#print axioms GolfScannerBridge.bytes_drop_head
#print axioms GolfScannerBridge.targets_of_success
#print axioms GolfScannerBridge.full_image_targets
