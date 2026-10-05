import Jump
import CountOffset

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfJump
namespace GolfOffsetJump

theorem jump_preserves {owner old new surplus skipped s t}
    (related : DeployedOffset owner old new surplus skipped s t)
    (destination : UInt256) (tail : List UInt256)
    (gas : 8 ≤ s.gasAvailable.toNat) :
    DeployedOffset owner old new surplus skipped
      (jumpPost s destination tail) (jumpPost t destination tail) := by
  refine ⟨?_, ?_, gas_preservation s.gasAvailable t.gasAvailable 8 surplus
    (by decide) gas related.gas, related.maps⟩
  · have updated := congrArg (fun st => jumpPost st destination tail) related.frame
    simpa [eraseCount, deployedFrame, eraseMaps, eraseCodeGas, jumpPost] using
      congrArg (fun st => eraseCount (deployedFrame st)) updated
  · simp only [jumpPost]
    have := related.count
    omega

-- Two independent residual fuels and actual canonical tables for the linked images.
theorem paired_jump {owner old new surplus skipped s t}
    (related : DeployedOffset owner old new surplus skipped s t)
    (destination : UInt256) (tail : List UInt256)
    (sourceFuel targetFuel : Nat)
    (oldDecoded : decode old s.pc = some (.JUMP, none))
    (newDecoded : decode new t.pc = some (.JUMP, none))
    (stack : s.stack = destination :: tail)
    (gas : 8 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1024)
    (oldValid : (D_J old (UInt256.ofNat 0)).contains destination = true)
    (newValid : (D_J new (UInt256.ofNat 0)).contains destination = true) :
    X (sourceFuel+2) (D_J old (UInt256.ofNat 0)) s =
      X (sourceFuel+1) (D_J old (UInt256.ofNat 0)) (jumpPost s destination tail) ∧
    X (targetFuel+2) (D_J new (UInt256.ofNat 0)) t =
      X (targetFuel+1) (D_J new (UInt256.ofNat 0)) (jumpPost t destination tail) ∧
    DeployedOffset owner old new surplus skipped
      (jumpPost s destination tail) (jumpPost t destination tail) := by
  have stackEq : s.stack = t.stack := by
    simpa only [eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
      congrArg EVM.State.stack related.frame
  have candidateStack := stackEq.symm.trans stack
  have candidateGas : 8 ≤ t.gasAvailable.toNat := by
    have := related.gas
    omega
  have sourceDecode : decode s.executionEnv.code s.pc = some (.JUMP, none) := by
    rw [related.maps.2.2.1.2.1]
    exact oldDecoded
  have targetDecode : decode t.executionEnv.code t.pc = some (.JUMP, none) := by
    rw [related.maps.2.2.2.2.1]
    exact newDecoded
  exact ⟨GolfJump.X_jump s destination tail sourceFuel (D_J old (UInt256.ofNat 0))
      sourceDecode stack gas height oldValid,
    GolfJump.X_jump t destination tail targetFuel (D_J new (UInt256.ofNat 0))
      targetDecode candidateStack candidateGas height newValid,
    jump_preserves related destination tail gas⟩

#print axioms jump_preserves
#print axioms paired_jump
end GolfOffsetJump
