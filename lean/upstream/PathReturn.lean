import PathSummary
import ReturnTerminal
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition GolfChunk GolfPathSummary
namespace GolfPathReturn

def sourceCost {old new : ByteArray} (q : Summary old new) (s : EVM.State) : Nat :=
  q.cost s + memoryExpansionCost (q.post s) .RETURN

def terminalPost {old new : ByteArray} (q : Summary old new)
    (address size : UInt256) (tail : List UInt256) (s : EVM.State) : EVM.State :=
  CanonicalReturn.terminalReturn (q.post s) address size tail

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
  have total : q.cost s + memoryExpansionCost (q.post s) .RETURN ≤ s.gasAvailable.toNat := gas
  have midGas := q.gas_eq s (by omega)
  have enough : memoryExpansionCost (q.post s) .RETURN ≤ (q.post s).gasAvailable.toNat := by omega
  have finalGas := CanonicalReturn.terminalReturn_gas (q.post s) address size tail enough
  change (terminalPost q address size tail s).gasAvailable.toNat =
    (q.post s).gasAvailable.toNat-memoryExpansionCost (q.post s) .RETURN at finalGas
  rw [finalGas,midGas]
  simp only [sourceCost]
  omega

theorem summary_return {old new : ByteArray} (q : Summary old new)
    (oldDecoded : decode old q.exit = some (.RETURN,none))
    (newDecoded : decode new q.exit = some (.RETURN,none))
    {owner surplus skipped s t}
    (related : DeployedOffset owner old new surplus skipped s t)
    (xs : List UInt256) (address size : UInt256) (tail : List UInt256) (fuel : Nat)
    (pc : s.pc = q.entry) (stack : s.stack = xs)
    (gas : sourceCost q s ≤ s.gasAvailable.toNat)
    (low : q.required ≤ xs.length) (height : xs.length ≤ q.maximum)
    (returnStack : q.stackMap xs = address :: size :: tail)
    (physical : (q.stackMap xs).length ≤ 1024)
    (readable : size.toNat < 2^64) :
    ∃ ce : EVM.State,
      X (fuel+q.sourceSteps+2) (D_J old (UInt256.ofNat 0)) s =
        .ok (.success (terminalPost q address size tail s) (output q address size s)) ∧
      X (fuel+q.targetSteps+2) (D_J new (UInt256.ofNat 0)) t =
        .ok (.success ce (output q address size s)) ∧
      DeployedOffset owner old new (surplus+2*q.powers+9*q.masks)
        (skipped+3*q.masks) (terminalPost q address size tail s) ce ∧
      (terminalPost q address size tail s).stack = tail ∧ ce.stack = tail ∧
      (terminalPost q address size tail s).H_return = output q address size s ∧
      ce.H_return = output q address size s ∧
      (terminalPost q address size tail s).gasAvailable.toNat =
        s.gasAvailable.toNat-sourceCost q s ∧
      (terminalPost q address size tail s).execLength = s.execLength+q.sourceSteps+1 ∧
      ce.execLength = t.execLength+q.targetSteps+1 := by
  have total : q.cost s + memoryExpansionCost (q.post s) .RETURN ≤ s.gasAvailable.toNat := gas
  have chunk := q.trace s pc (by simpa only [stack] using low)
    (by simpa only [stack] using height) (by omega)
  have trace : MixedTrace old new (fuel+2) (fuel+q.sourceSteps+2)
      (fuel+q.targetSteps+2) q.powers q.masks s (q.post s) := by
    convert GolfChunk.recover chunk (fuel+1) using 1 <;> omega
  obtain ⟨mid,sourceRun,targetRun,midRelated⟩ :=
    mixed_simulation trace t surplus skipped (D_J old (UInt256.ofNat 0))
      (D_J new (UInt256.ofNat 0)) related
  have midPC := q.pc_eq s pc
  have midStack := q.stack_eq s xs stack
  have midGas := q.gas_eq s (by omega)
  have sourceDecode : decode (q.post s).executionEnv.code (q.post s).pc = some (.RETURN,none) := by
    rw [midRelated.maps.2.2.1.2.1,midPC]
    exact oldDecoded
  have targetDecode : decode mid.executionEnv.code mid.pc = some (.RETURN,none) := by
    rw [midRelated.maps.2.2.2.2.1,← offset_pc midRelated,midPC]
    exact newDecoded
  obtain ⟨sourceReturn,targetReturn,finalRelated⟩ := CanonicalReturn.return_pair
    midRelated address size tail fuel fuel (D_J old (UInt256.ofNat 0))
    (D_J new (UInt256.ofNat 0)) sourceDecode targetDecode
    (midStack.trans returnStack) (by omega) (by rw [midStack]; exact physical) readable
  have countSource := source_count q address size tail s
  have gap := GolfChunk.fuel_gap chunk
  have countTarget : (CanonicalReturn.terminalReturn mid address size tail).execLength =
      t.execLength+q.targetSteps+1 := by
    have startCount := related.count
    have endCount := finalRelated.count
    change (terminalPost q address size tail s).execLength =
      (CanonicalReturn.terminalReturn mid address size tail).execLength+(skipped+3*q.masks) at endCount
    omega
  have sameOutput := CanonicalReturn.return_bytes_equal midRelated address size
  exact ⟨CanonicalReturn.terminalReturn mid address size tail,
    sourceRun.trans sourceReturn,targetRun.trans targetReturn,finalRelated,
    rfl,rfl,rfl,sameOutput.symm,source_gas q address size tail s gas,countSource,countTarget⟩

#print axioms source_count
#print axioms source_gas
#print axioms summary_return
end GolfPathReturn
