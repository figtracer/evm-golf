import MemorySupport
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition CanonicalMemory
namespace CanonicalRevert

-- Canonical machine operation including its actual activeWords behavior.
def revertPost (s : EVM.State) (offset size : UInt256) (tail : List UInt256) (cost : Nat) : EVM.State :=
 let charged := charge s cost
 {charged with
  toMachineState := charged.toMachineState.evmRevert offset size
  stack := tail
  pc := s.pc + UInt256.ofNat 1
  execLength := s.execLength + 1}

def terminalPost (s : EVM.State) (offset size : UInt256) (tail : List UInt256) : EVM.State :=
 revertPost (charge s (memoryExpansionCost s .REVERT)) offset size tail 0

@[simp] theorem cost_revert (s : EVM.State) : C' s .REVERT = 0 := rfl

theorem step_revert (s : EVM.State) (fuel cost : Nat) (arg : Option (UInt256 × Nat))
 (offset size : UInt256) (tail : List UInt256) (stack : s.stack = offset::size::tail) :
 EVM.step (fuel+1) cost (some (.REVERT,arg)) s = .ok (revertPost s offset size tail cost) := by
 have specified : {s with stack := offset::size::tail} = s := by rw [←stack]
 rw [←specified]
 rfl

theorem expansion_equal {owner old new surplus skipped s t}
 (related : DeployedOffset owner old new surplus skipped s t) :
 memoryExpansionCost s .REVERT = memoryExpansionCost t .REVERT := by
 have stack := offset_stack related
 have active := congrArg (fun st : EVM.State => st.activeWords) related.frame
 change s.activeWords = t.activeWords at active
 simp only [memoryExpansionCost,memoryExpansionCost.μᵢ',stack,active]

theorem revert_preserves {owner old new surplus skipped s t}
 (related : DeployedOffset owner old new surplus skipped s t)
 (offset size : UInt256) (tail : List UInt256) (cost : Nat)
 (small : cost < UInt256.size) (enough : cost ≤ s.gasAvailable.toNat) :
 DeployedOffset owner old new surplus skipped
   (revertPost s offset size tail cost) (revertPost t offset size tail cost) := by
 refine ⟨?_,?_,?_,related.maps⟩
 · have h := congrArg (fun st : EVM.State => revertPost st offset size tail cost) related.frame
   simpa only [revertPost,charge,eraseCount,deployedFrame,eraseMaps,eraseCodeGas,
     MachineState.evmRevert,MachineState.evmReturn] using
     congrArg (fun st : EVM.State => eraseCount (deployedFrame st)) h
 · change s.execLength+1 = (t.execLength+1)+skipped
   have := related.count
   omega
 · exact gas_preservation s.gasAvailable t.gasAvailable cost surplus small enough related.gas


theorem terminal_gas (s : EVM.State) (offset size : UInt256) (tail : List UInt256)
 (enough : memoryExpansionCost s .REVERT ≤ s.gasAvailable.toNat) :
 (terminalPost s offset size tail).gasAvailable.toNat =
   s.gasAvailable.toNat-memoryExpansionCost s .REVERT := by
 have bound : s.gasAvailable.toNat < UInt256.size := s.gasAvailable.val.isLt
 have small : memoryExpansionCost s .REVERT < UInt256.size := by omega
 change ((s.gasAvailable-UInt256.ofNat (memoryExpansionCost s .REVERT))-UInt256.ofNat 0).toNat = _
 rw [word_sub_zero,word_sub_toNat _ _ small enough]

theorem terminal_count (s : EVM.State) (offset size : UInt256) (tail : List UInt256) :
 (terminalPost s offset size tail).execLength = s.execLength+1 := rfl

theorem terminal_output (s : EVM.State) (offset size : UInt256) (tail : List UInt256) :
 (terminalPost s offset size tail).H_return =
   s.memory.readWithPadding offset.toNat size.toNat := rfl

-- Canonical X terminates in ExecutionResult.revert, whose gas field is retained.
theorem X_revert (s : EVM.State) (fuel : Nat) (jumps : Array UInt256)
 (offset size : UInt256) (tail : List UInt256)
 (decoded : decode s.executionEnv.code s.pc = some (.REVERT,none))
 (stack : s.stack = offset::size::tail)
 (gas : memoryExpansionCost s .REVERT ≤ s.gasAvailable.toNat)
 (physical : s.stack.length ≤ 1024)
 (_readable : size.toNat < 2^64) :
 X (fuel+2) jumps s = .ok (.revert
   (terminalPost s offset size tail).gasAvailable
   (terminalPost s offset size tail).H_return) := by
 have noExpansion : ¬s.gasAvailable.toNat < memoryExpansionCost s .REVERT := Nat.not_lt.mpr gas
 have noInputs : ¬s.stack.length < 2 := by simp [stack]
 have noOutputs : ¬1024 < s.stack.length - 2 := by omega
 conv_lhs => unfold X
 simp only [decoded]
 simp [noExpansion,cost_revert,Operation.isCreate,δ,α,noInputs,noOutputs]
 change (do
   let next ← EVM.step (fuel+1) 0 (some (.REVERT,none)) (charge s (memoryExpansionCost s .REVERT))
   pure (ExecutionResult.revert next.gasAvailable next.H_return)) = _
 rw [step_revert (charge s (memoryExpansionCost s .REVERT)) fuel 0 none offset size tail stack]
 rfl

theorem revert_pair {owner old new surplus skipped s t}
 (related : DeployedOffset owner old new surplus skipped s t)
 (offset size : UInt256) (tail : List UInt256) (sourceFuel targetFuel : Nat)
 (oldJumps newJumps : Array UInt256)
 (oldDecode : decode s.executionEnv.code s.pc = some (.REVERT,none))
 (newDecode : decode t.executionEnv.code t.pc = some (.REVERT,none))
 (stack : s.stack = offset::size::tail)
 (gas : memoryExpansionCost s .REVERT ≤ s.gasAvailable.toNat)
 (physical : s.stack.length ≤ 1024)
 (readable : size.toNat < 2^64) :
 X (sourceFuel+2) oldJumps s = .ok (.revert (terminalPost s offset size tail).gasAvailable (terminalPost s offset size tail).H_return) ∧
 X (targetFuel+2) newJumps t = .ok (.revert (terminalPost t offset size tail).gasAvailable (terminalPost s offset size tail).H_return) ∧
 DeployedOffset owner old new surplus skipped (terminalPost s offset size tail) (terminalPost t offset size tail) := by
 have targetPhysical : t.stack.length ≤ 1024 := by
  rw [←offset_stack related]
  exact physical
 have sameExpansion := expansion_equal related
 have small : memoryExpansionCost s .REVERT < UInt256.size := by
  have bound : s.gasAvailable.toNat < UInt256.size := s.gasAvailable.val.isLt
  omega
 have targetGas : memoryExpansionCost t .REVERT ≤ t.gasAvailable.toNat := by
  rw [←sameExpansion]
  have := related.gas
  omega
 have charged := charge_preserves related (memoryExpansionCost s .REVERT) small gas
 have nextRelated := revert_preserves charged offset size tail 0 (by decide) (Nat.zero_le _)
 have finalRelated : DeployedOffset owner old new surplus skipped (terminalPost s offset size tail) (terminalPost t offset size tail) := by
  simpa only [terminalPost,←sameExpansion] using nextRelated
 have sameOutput := congrArg (fun st : EVM.State => st.H_return) finalRelated.frame
 change (terminalPost s offset size tail).H_return = (terminalPost t offset size tail).H_return at sameOutput
 refine ⟨X_revert s sourceFuel oldJumps offset size tail oldDecode stack gas physical readable,?_,finalRelated⟩
 rw [X_revert t targetFuel newJumps offset size tail newDecode ((offset_stack related).symm.trans stack) targetGas targetPhysical readable,←sameOutput]

#print axioms cost_revert
#print axioms expansion_equal
#print axioms terminal_gas
#print axioms terminal_count
#print axioms terminal_output
#print axioms step_revert
#print axioms X_revert
#print axioms revert_preserves
#print axioms revert_pair
end CanonicalRevert
