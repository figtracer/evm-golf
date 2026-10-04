import CountOffset
import Regions
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset
namespace GolfComposition
theorem offset_pc {owner old new surplus skipped s t}
 (h : DeployedOffset owner old new surplus skipped s t) : s.pc = t.pc := by
 simpa only [eraseCount,deployedFrame,eraseMaps,eraseCodeGas] using congrArg EVM.State.pc h.frame

theorem offset_stack {owner old new surplus skipped s t}
 (h : DeployedOffset owner old new surplus skipped s t) : s.stack = t.stack := by
 simpa only [eraseCount,deployedFrame,eraseMaps,eraseCodeGas] using congrArg EVM.State.stack h.frame

theorem offset_frame_code (s t : EVM.State) (old new : ByteArray)
 (h : eraseCount (deployedFrame s) = eraseCount (deployedFrame t)) :
 eraseCount (deployedFrame (withCode s old)) = eraseCount (deployedFrame (withCode t new)) := by
 simpa only [eraseCount,deployedFrame,eraseMaps,eraseCodeGas,withCode] using h

theorem offset_frame_push (s t : EVM.State) (value : UInt256) (width : Nat)
 (h : eraseCount (deployedFrame s) = eraseCount (deployedFrame t)) :
 eraseCount (deployedFrame (pushedWidth s value width)) = eraseCount (deployedFrame (pushedWidth t value width)) := by
 have hh := congrArg (fun st => pushedWidth st value width) h
 simpa only [eraseCount,deployedFrame,eraseMaps,eraseCodeGas,pushedWidth] using
   congrArg (fun st => eraseCount (deployedFrame st)) hh

theorem offset_frame_binary (s t : EVM.State) (value : UInt256) (tail : List UInt256) (cost : Nat)
 (h : eraseCount (deployedFrame s) = eraseCount (deployedFrame t)) :
 eraseCount (deployedFrame (binaryPost s value tail cost)) = eraseCount (deployedFrame (binaryPost t value tail cost)) := by
 have hh := congrArg (fun st => binaryPost st value tail cost) h
 simpa only [eraseCount,deployedFrame,eraseMaps,eraseCodeGas,binaryPost] using
   congrArg (fun st => eraseCount (deployedFrame st)) hh

theorem offset_power_boundary (owner : AccountAddress) (old new : ByteArray)
    (s t : EVM.State) (p : Operation.POp) (width k surplus skipped : Nat)
    (a : UInt256) (tail : List UInt256) (sourceFuel targetFuel : Nat)
    (oldJumps newJumps : Array UInt256)
    (related : DeployedOffset owner old new surplus skipped s t)
    (nonzero : p ≠ .PUSH0) (range : k < 256)
    (oldFragment : MulPowerAt old s.pc p width k)
    (newFragment : ShiftPowerAt new t.pc p width k)
    (stack : s.stack = a :: tail) (gas : 8 ≤ s.gasAvailable.toNat)
    (height : s.stack.length < 1024) :
    X (sourceFuel+3) oldJumps s = X (sourceFuel+1) oldJumps (mulPowerPost s old width k a tail) ∧
    X (targetFuel+3) newJumps t = X (targetFuel+1) newJumps (shiftPowerPost t new width k a tail) ∧
    DeployedOffset owner old new (surplus+2) skipped
      (mulPowerPost s old width k a tail) (shiftPowerPost t new width k a tail) := by
  have samePC := offset_pc related
  have sameStack := offset_stack related
  have targetStack : t.stack = a :: tail := sameStack.symm.trans stack
  have targetHeight : t.stack.length < 1024 := by rw [←sameStack]; exact height
  have targetGas : 8 ≤ t.gasAvailable.toNat := by rw [related.gas]; omega
  have original := fullX_power_refinement s old new p width k a tail sourceFuel oldJumps
    nonzero range oldFragment (by rw [samePC]; exact newFragment) stack gas height
  have candidate := fullX_power_refinement t old new p width k a tail targetFuel newJumps
    nonzero range (by rw [←samePC]; exact oldFragment) newFragment targetStack targetGas targetHeight
  have oldCode : withCode s old = s := by
    unfold withCode; rw [←related.maps.2.2.1.2.1]
  have newCode : withCode t new = t := by
    unfold withCode; rw [←related.maps.2.2.2.2.1]
  have oldRun := original.1
  have newRun := candidate.2.1
  rw [oldCode] at oldRun
  rw [newCode] at newRun
  refine ⟨oldRun, newRun, ?_, ?_, ?_, ?_⟩
  · have sameMul : eraseCount (deployedFrame (mulPowerPost s old width k a tail)) =
        eraseCount (deployedFrame (mulPowerPost t old width k a tail)) := by
      apply offset_frame_binary
      apply offset_frame_push
      exact offset_frame_code s t old old related.frame
    exact sameMul.trans (congrArg (fun st => eraseCount (eraseMaps st)) candidate.2.2.1)
  · change s.execLength+1+1 = (t.execLength+1+1)+skipped
    have := related.count
    omega
  · have pushGas := gas_preservation s.gasAvailable t.gasAvailable 3 surplus
      (by decide) (by omega) related.gas
    have remaining := word_sub_toNat s.gasAvailable 3 (by decide) (by omega)
    have mulGas := gas_preservation (s.gasAvailable - UInt256.ofNat 3)
      (t.gasAvailable - UInt256.ofNat 3) 5 surplus (by decide) (by omega) pushGas
    have gain := candidate.2.2.2
    change (shiftPowerPost t new width k a tail).gasAvailable.toNat =
      (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5).toNat + (surplus+2)
    change (shiftPowerPost t new width k a tail).gasAvailable.toNat =
      (t.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5).toNat + 2 at gain
    omega
  · exact ⟨related.maps.1, related.maps.2.1,
      ⟨related.maps.2.2.1.1, rfl, related.maps.2.2.1.2.2.1, related.maps.2.2.1.2.2.2⟩,
      ⟨related.maps.2.2.2.1, rfl, related.maps.2.2.2.2.2.1, related.maps.2.2.2.2.2.2⟩⟩

#print axioms offset_pc
#print axioms offset_stack
#print axioms offset_power_boundary
end GolfComposition
