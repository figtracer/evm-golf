import CheckedScannerBridge
import CheckedRevisedScannerProof
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfWindowArtifact
namespace RevisedTableEquality

theorem table_of_layout (code : ByteArray)
    (bound : code.size + 32 < UInt256.size) :
    D_J code (UInt256.ofNat 0) =
      ((jumpTargets (GolfLayout.scan (code.data.toList.map UInt8.toNat))).map UInt256.ofNat).toArray := by
  apply RevisedScannerProof.bounded_wrapper code (UInt256.ofNat 0) _ bound
  simpa using GolfScannerBridge.full_image_targets code

theorem tables_equal (old new : ByteArray)
    (oldBound : old.size + 32 < UInt256.size)
    (newBound : new.size + 32 < UInt256.size)
    (targets : jumpTargets (GolfLayout.scan (old.data.toList.map UInt8.toNat)) =
      jumpTargets (GolfLayout.scan (new.data.toList.map UInt8.toNat))) :
    D_J old (UInt256.ofNat 0) = D_J new (UInt256.ofNat 0) := by
  rw [table_of_layout old oldBound, table_of_layout new newBound, targets]

end RevisedTableEquality

#print axioms RevisedTableEquality.table_of_layout
#print axioms RevisedTableEquality.tables_equal
