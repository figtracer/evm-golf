import PathSummary
import CountOffset
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition GolfChunk GolfPathSummary
namespace GolfPathStop

theorem stopped_preserves {owner old new surplus skipped s t}
 (h : DeployedOffset owner old new surplus skipped s t) :
 DeployedOffset owner old new surplus skipped (stopped s) (stopped t) := by
 refine ⟨?_, ?_, h.gas, h.maps⟩
 · have updated := congrArg (fun st => stopped st) h.frame
   simpa [stopped,eraseCount,deployedFrame,eraseMaps,eraseCodeGas] using updated
 · change s.execLength+1 = (t.execLength+1)+skipped
   have := h.count
   omega

def terminalPost {old new : ByteArray} (q : Summary old new) (s : EVM.State) : EVM.State :=
  stopped (q.post s)

theorem source_count {old new : ByteArray} (q : Summary old new) (s : EVM.State) :
    (terminalPost q s).execLength = s.execLength+q.sourceSteps+1 := by
  change (q.post s).execLength+1 = _
  rw [q.count_eq]

theorem source_gas {old new : ByteArray} (q : Summary old new) (s : EVM.State)
    (gas : q.cost s ≤ s.gasAvailable.toNat) :
    (terminalPost q s).gasAvailable.toNat = s.gasAvailable.toNat-q.cost s := by
  exact q.gas_eq s gas

-- The generated wrapper must discharge both terminal decodes and the output bound.
theorem summary_stop {old new : ByteArray} (q : Summary old new)
    (outputBound : q.maximum-q.required+q.produced ≤ 1024)
    (oldDecoded : decode old q.exit = some (.STOP,none))
    (newDecoded : decode new q.exit = some (.STOP,none))
    {owner surplus skipped s t}
    (related : DeployedOffset owner old new surplus skipped s t)
    (xs : List UInt256) (fuel : Nat)
    (pc : s.pc = q.entry) (stack : s.stack = xs)
    (gas : q.cost s ≤ s.gasAvailable.toNat)
    (low : q.required ≤ xs.length) (height : xs.length ≤ q.maximum) :
    ∃ ce : EVM.State,
      X (fuel+q.sourceSteps+2) (D_J old (UInt256.ofNat 0)) s =
        .ok (.success (terminalPost q s) ByteArray.empty) ∧
      X (fuel+q.targetSteps+2) (D_J new (UInt256.ofNat 0)) t =
        .ok (.success ce ByteArray.empty) ∧
      DeployedOffset owner old new (surplus+2*q.powers+9*q.masks)
        (skipped+3*q.masks) (terminalPost q s) ce ∧
      (terminalPost q s).stack = q.stackMap xs ∧ ce.stack = q.stackMap xs ∧
      (terminalPost q s).gasAvailable.toNat = s.gasAvailable.toNat-q.cost s ∧
      (terminalPost q s).execLength = s.execLength+q.sourceSteps+1 ∧
      ce.execLength = t.execLength+q.targetSteps+1 := by
  have chunk := q.trace s pc (by simpa only [stack] using low)
    (by simpa only [stack] using height) gas
  have trace : MixedTrace old new (fuel+2) (fuel+q.sourceSteps+2)
      (fuel+q.targetSteps+2) q.powers q.masks s (q.post s) := by
    convert GolfChunk.recover chunk (fuel+1) using 1 <;> omega
  obtain ⟨mid,sourceRun,targetRun,midRelated⟩ :=
    mixed_simulation trace t surplus skipped (D_J old (UInt256.ofNat 0))
      (D_J new (UInt256.ofNat 0)) related
  have midPC := q.pc_eq s pc
  have midStack := q.stack_eq s xs stack
  have lengthEq := q.stack_length xs low
  have physical : (q.post s).stack.length ≤ 1024 := by
    rw [midStack]
    omega
  have targetHeight : mid.stack.length ≤ 1024 := by
    rw [← offset_stack midRelated]
    exact physical
  have sourceDecode : decode (q.post s).executionEnv.code (q.post s).pc = some (.STOP,none) := by
    rw [midRelated.maps.2.2.1.2.1,midPC]
    exact oldDecoded
  have targetDecode : decode mid.executionEnv.code mid.pc = some (.STOP,none) := by
    rw [midRelated.maps.2.2.2.2.1,← offset_pc midRelated,midPC]
    exact newDecoded
  have sourceStop := X_stop (q.post s) fuel (D_J old (UInt256.ofNat 0)) sourceDecode physical
  have targetStop := X_stop mid fuel (D_J new (UInt256.ofNat 0)) targetDecode targetHeight
  have finalRelated := stopped_preserves midRelated
  have countSource := source_count q s
  have gap := GolfChunk.fuel_gap chunk
  have countTarget : (stopped mid).execLength = t.execLength+q.targetSteps+1 := by
    have startCount := related.count
    have endCount := finalRelated.count
    change (terminalPost q s).execLength = (stopped mid).execLength+(skipped+3*q.masks) at endCount
    omega
  exact ⟨stopped mid,sourceRun.trans sourceStop,targetRun.trans targetStop,finalRelated,
    midStack,(offset_stack midRelated).symm.trans midStack,
    source_gas q s gas,countSource,countTarget⟩

#print axioms stopped_preserves
#print axioms source_count
#print axioms source_gas
#print axioms summary_stop
end GolfPathStop
