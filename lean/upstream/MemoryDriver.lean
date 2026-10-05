import MemorySupport
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition
namespace CanonicalMemory

def memoryPost (s : EVM.State) (address value : UInt256) (tail : List UInt256) : EVM.State :=
 storePost (charge s (memoryExpansionCost s .MSTORE)) address value tail 3

theorem X_mstore (s : EVM.State) (fuel : Nat) (jumps : Array UInt256)
 (address value : UInt256) (tail : List UInt256)
 (decoded : decode s.executionEnv.code s.pc = some (.MSTORE,none))
 (stack : s.stack = address::value::tail)
 (gas : memoryExpansionCost s .MSTORE + 3 ≤ s.gasAvailable.toNat)
 (height : tail.length ≤ 1024) :
 X (fuel+2) jumps s = X (fuel+1) jumps (memoryPost s address value tail) := by
 have enough := (expansion_charge_bounds s gas).2
 have noExpansion : ¬s.gasAvailable.toNat < memoryExpansionCost s .MSTORE := by omega
 have noOpcode : ¬(s.gasAvailable - UInt256.ofNat (memoryExpansionCost s .MSTORE)).toNat < 3 :=
   Nat.not_lt.mpr enough
 have noInputs : ¬s.stack.length < 2 := by simp [stack]
 have noOutputs : ¬1024 < s.stack.length - 2 := by simp [stack]; omega
 conv_lhs => unfold X
 simp only [decoded]
 simp [noExpansion,noOpcode,cost_mstore,Operation.isCreate,δ,α,noInputs,noOutputs]
 change (do
   let next ← EVM.step (fuel+1) 3 (some (.MSTORE,none)) (charge s (memoryExpansionCost s .MSTORE))
   X (fuel+1) jumps next) = _
 rw [step_mstore (charge s (memoryExpansionCost s .MSTORE)) fuel 3 none address value tail stack]
 rfl

-- Both candidate gas checks and its memory write follow from source conditions.
theorem mstore_pair {owner old new surplus skipped s t}
 (related : DeployedOffset owner old new surplus skipped s t)
 (address value : UInt256) (tail : List UInt256) (sourceFuel targetFuel : Nat)
 (oldJumps newJumps : Array UInt256)
 (sourceDecode : decode s.executionEnv.code s.pc = some (.MSTORE,none))
 (targetDecode : decode t.executionEnv.code t.pc = some (.MSTORE,none))
 (stack : s.stack = address::value::tail)
 (gas : memoryExpansionCost s .MSTORE + 3 ≤ s.gasAvailable.toNat)
 (height : tail.length ≤ 1024) :
 X (sourceFuel+2) oldJumps s = X (sourceFuel+1) oldJumps (memoryPost s address value tail) ∧
 X (targetFuel+2) newJumps t = X (targetFuel+1) newJumps (memoryPost t address value tail) ∧
 DeployedOffset owner old new surplus skipped (memoryPost s address value tail) (memoryPost t address value tail) := by
 have sameExpansion := expansion_equal related
 have targetGas : memoryExpansionCost t .MSTORE + 3 ≤ t.gasAvailable.toNat := by
  rw [←sameExpansion]
  have := related.gas
  omega
 have charged := charge_preserves related (memoryExpansionCost s .MSTORE)
   (expansion_charge_bounds s gas).1 (by omega)
 have nextRelated := store_preserves charged address value tail 3 (by decide) (expansion_charge_bounds s gas).2
 refine ⟨X_mstore s sourceFuel oldJumps address value tail sourceDecode stack gas height,
   X_mstore t targetFuel newJumps address value tail targetDecode ((offset_stack related).symm.trans stack) targetGas height,?_⟩
 simpa only [memoryPost,←sameExpansion] using nextRelated

#print axioms X_mstore
#print axioms mstore_pair
end CanonicalMemory
