import PathSummary
import RevertTerminal
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition GolfChunk GolfPathSummary
namespace GolfPathRevert

def sourceCost {old new : ByteArray} (q : Summary old new) (s : EVM.State) : Nat :=
  q.cost s + memoryExpansionCost (q.post s) .REVERT

def terminalPost {old new : ByteArray} (q : Summary old new)
    (address size : UInt256) (tail : List UInt256) (s : EVM.State) : EVM.State :=
  CanonicalRevert.terminalPost (q.post s) address size tail

def output {old new : ByteArray} (q : Summary old new)
    (address size : UInt256) (s : EVM.State) : ByteArray :=
  (q.post s).memory.readWithPadding address.toNat size.toNat

theorem source_count {old new : ByteArray} (q : Summary old new)
    (address size : UInt256) (tail : List UInt256) (s : EVM.State) :
    (terminalPost q address size tail s).execLength = s.execLength+q.sourceSteps+1 := by
  change (q.post s).execLength+1 = _
  rw [q.count_eq]

theorem source_gas {old new : ByteArray} (q : Summary old new)
    (address size : UInt256) (tail : List UInt256) (s : EVM.State)
    (gas : sourceCost q s ≤ s.gasAvailable.toNat) :
    (terminalPost q address size tail s).gasAvailable.toNat =
      s.gasAvailable.toNat-sourceCost q s := by
  have total : q.cost s + memoryExpansionCost (q.post s) .REVERT ≤ s.gasAvailable.toNat := gas
  have midGas := q.gas_eq s (by omega)
  have enough : memoryExpansionCost (q.post s) .REVERT ≤ (q.post s).gasAvailable.toNat := by omega
  have finalGas := CanonicalRevert.terminal_gas (q.post s) address size tail enough
  change (terminalPost q address size tail s).gasAvailable.toNat =
    (q.post s).gasAvailable.toNat-memoryExpansionCost (q.post s) .REVERT at finalGas
  rw [finalGas,midGas]
  simp only [sourceCost]
  omega

theorem summary_revert {old new : ByteArray} (q : Summary old new)
    (oldDecoded : decode old q.exit = some (.REVERT,none))
    (newDecoded : decode new q.exit = some (.REVERT,none))
    {owner surplus skipped s t}
    (related : DeployedOffset owner old new surplus skipped s t)
    (xs : List UInt256) (address size : UInt256) (tail : List UInt256) (sourceFuel targetFuel : Nat)
    (pc : s.pc = q.entry) (stack : s.stack = xs)
    (gas : sourceCost q s ≤ s.gasAvailable.toNat)
    (low : q.required ≤ xs.length) (height : xs.length ≤ q.maximum)
    (revertStack : q.stackMap xs = address :: size :: tail)
    (physical : (q.stackMap xs).length ≤ 1024)
    (readable : size.toNat < 2^64) :
    ∃ ce : EVM.State,
      X (sourceFuel+q.sourceSteps+2) (D_J old (UInt256.ofNat 0)) s =
        .ok (.revert (terminalPost q address size tail s).gasAvailable (output q address size s)) ∧
      X (targetFuel+q.targetSteps+2) (D_J new (UInt256.ofNat 0)) t =
        .ok (.revert ce.gasAvailable (output q address size s)) ∧
      DeployedOffset owner old new (surplus+2*q.powers+9*q.masks)
        (skipped+3*q.masks) (terminalPost q address size tail s) ce ∧
      (terminalPost q address size tail s).stack = tail ∧ ce.stack = tail ∧
      (terminalPost q address size tail s).H_return = output q address size s ∧
      ce.H_return = output q address size s ∧
      (terminalPost q address size tail s).gasAvailable.toNat =
        s.gasAvailable.toNat-sourceCost q s ∧
      (terminalPost q address size tail s).execLength = s.execLength+q.sourceSteps+1 ∧
      ce.execLength = t.execLength+q.targetSteps+1 := by
  have total : q.cost s + memoryExpansionCost (q.post s) .REVERT ≤ s.gasAvailable.toNat := gas
  have chunk := q.trace s pc (by simpa only [stack] using low)
    (by simpa only [stack] using height) (by omega)
  obtain ⟨_,sourceRun,_,_⟩ := mixed_simulation (recover chunk (sourceFuel+1))
    t surplus skipped (D_J old (UInt256.ofNat 0)) (D_J new (UInt256.ofNat 0)) related
  obtain ⟨mid,_,targetRun,midRelated⟩ := mixed_simulation (recover chunk (targetFuel+1))
    t surplus skipped (D_J old (UInt256.ofNat 0)) (D_J new (UInt256.ofNat 0)) related
  have midPC := q.pc_eq s pc
  have midStack := q.stack_eq s xs stack
  have midGas := q.gas_eq s (by omega)
  have sourceDecode : decode (q.post s).executionEnv.code (q.post s).pc = some (.REVERT,none) := by
    rw [midRelated.maps.2.2.1.2.1,midPC]
    exact oldDecoded
  have targetDecode : decode mid.executionEnv.code mid.pc = some (.REVERT,none) := by
    rw [midRelated.maps.2.2.2.2.1,← offset_pc midRelated,midPC]
    exact newDecoded
  obtain ⟨sourceRevert,targetRevert,finalRelated⟩ := CanonicalRevert.revert_pair
    midRelated address size tail sourceFuel targetFuel (D_J old (UInt256.ofNat 0))
    (D_J new (UInt256.ofNat 0)) sourceDecode targetDecode
    (midStack.trans revertStack) (by omega) (by rw [midStack]; exact physical) readable
  have countSource := source_count q address size tail s
  have gap := GolfChunk.fuel_gap chunk
  have countTarget : (CanonicalRevert.terminalPost mid address size tail).execLength =
      t.execLength+q.targetSteps+1 := by
    have startCount := related.count
    have endCount := finalRelated.count
    change (terminalPost q address size tail s).execLength =
      (CanonicalRevert.terminalPost mid address size tail).execLength+(skipped+3*q.masks) at endCount
    omega
  have sameOutput := congrArg (fun st : EVM.State => st.H_return) finalRelated.frame
  change (terminalPost q address size tail s).H_return =
    (CanonicalRevert.terminalPost mid address size tail).H_return at sameOutput
  refine ⟨CanonicalRevert.terminalPost mid address size tail,?_,?_,finalRelated,
    rfl,rfl,rfl,sameOutput.symm,source_gas q address size tail s gas,countSource,countTarget⟩
  · have fuelEq : sourceFuel+q.sourceSteps+2 = (sourceFuel+1)+q.sourceSteps+1 := by omega
    rw [fuelEq]
    exact sourceRun.trans sourceRevert
  · have fuelEq : targetFuel+q.targetSteps+2 = (targetFuel+1)+q.targetSteps+1 := by omega
    rw [fuelEq]
    exact targetRun.trans targetRevert

#print axioms source_count
#print axioms source_gas
#print axioms summary_revert
end GolfPathRevert
