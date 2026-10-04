import PowerRegion
/- Canonical JUMP extension for the checked-scanner certificate. -/
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream
namespace GolfJump

def jumpPost (s : EVM.State) (destination : UInt256) (tail : List UInt256) : EVM.State :=
  { s with
    pc := destination
    stack := tail
    gasAvailable := s.gasAvailable - UInt256.ofNat 8
    execLength := s.execLength + 1 }

@[simp] theorem cost_jump (s : EVM.State) : C' s .JUMP = 8 := rfl

@[simp] theorem mem_jump (s : EVM.State) : memoryExpansionCost s .JUMP = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

theorem step_jump (s : EVM.State) (destination : UInt256) (tail : List UInt256)
    (fuel : Nat) (stack : s.stack = destination :: tail) :
    EVM.step (fuel + 1) 8 (some (.JUMP, none)) s =
      .ok (jumpPost s destination tail) := by
  have specified : { s with stack := destination :: tail } = s := by rw [← stack]
  rw [← specified]
  rfl

theorem X_jump (s : EVM.State) (destination : UInt256) (tail : List UInt256)
    (fuel : Nat) (jumps : Array UInt256)
    (decoded : decode s.executionEnv.code s.pc = some (.JUMP, none))
    (stack : s.stack = destination :: tail)
    (gas : 8 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1024)
    (valid : jumps.contains destination = true) :
    X (fuel + 2) jumps s = X (fuel + 1) jumps (jumpPost s destination tail) := by
  have canonical := step_jump s destination tail fuel stack
  have inputBound : ¬s.stack.length < 1 := by simp [stack]
  have outputBound : ¬1024 < s.stack.length - 1 := by simpa [stack] using Nat.not_lt.mpr height
  have validAt : X.notIn s.stack[0]? jumps = false := by simp [X.notIn, X.belongs, stack, valid]
  conv_lhs => unfold X
  simp only [decoded]
  simp [mem_jump, cost_jump, Operation.isCreate, δ, α,
    validAt, inputBound, outputBound, Nat.not_lt.mpr gas]
  change (do
    let n ← EVM.step (fuel + 1) 8 (some (.JUMP, none)) s
    X (fuel + 1) jumps n) = _
  rw [canonical]
  rfl

theorem jump_preserves {owner old new surplus s t}
    (related : DeployedFrameWithGas owner old new surplus s t)
    (destination : UInt256) (tail : List UInt256)
    (gas : 8 ≤ s.gasAvailable.toNat) :
    DeployedFrameWithGas owner old new surplus
      (jumpPost s destination tail) (jumpPost t destination tail) := by
  refine ⟨?_, gas_preservation s.gasAvailable t.gasAvailable 8 surplus
    (by decide) gas related.gas, related.maps⟩
  have updated := congrArg (fun st => jumpPost st destination tail) related.frame
  simpa only [deployedFrame, eraseMaps, eraseCodeGas, jumpPost] using
    congrArg deployedFrame updated

-- Exact canonical jump tables; the generated membership module discharges both.
theorem paired_jump {owner old new surplus s t}
    (related : DeployedFrameWithGas owner old new surplus s t)
    (destination : UInt256) (tail : List UInt256) (fuel : Nat)
    (oldDecoded : decode old s.pc = some (.JUMP, none))
    (newDecoded : decode new t.pc = some (.JUMP, none))
    (stack : s.stack = destination :: tail)
    (gas : 8 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1024)
    (oldValid : (D_J old (UInt256.ofNat 0)).contains destination = true)
    (newValid : (D_J new (UInt256.ofNat 0)).contains destination = true) :
    X (fuel+2) (D_J old (UInt256.ofNat 0)) s =
      X (fuel+1) (D_J old (UInt256.ofNat 0)) (jumpPost s destination tail) ∧
    X (fuel+2) (D_J new (UInt256.ofNat 0)) t =
      X (fuel+1) (D_J new (UInt256.ofNat 0)) (jumpPost t destination tail) ∧
    DeployedFrameWithGas owner old new surplus
      (jumpPost s destination tail) (jumpPost t destination tail) := by
  have candidateStack := (deployed_frame_stack related).symm.trans stack
  have candidateGas : 8 ≤ t.gasAvailable.toNat := by
    have h := related.gas
    omega
  have sourceDecode : decode s.executionEnv.code s.pc = some (.JUMP,none) := by
    rw [related.maps.2.2.1.2.1]
    exact oldDecoded
  have targetDecode : decode t.executionEnv.code t.pc = some (.JUMP,none) := by
    rw [related.maps.2.2.2.2.1]
    exact newDecoded
  exact ⟨X_jump s destination tail fuel (D_J old (UInt256.ofNat 0)) sourceDecode stack gas height oldValid,
    X_jump t destination tail fuel (D_J new (UInt256.ofNat 0)) targetDecode candidateStack candidateGas height newValid,
    jump_preserves related destination tail gas⟩


-- Keep the deployed code abstract while reducing state-field projections.
theorem compiler_jump_count (code : ByteArray) (destination : Nat)
    (s : EVM.State) (a b c : UInt256) (tail output : List UInt256) :
    (jumpPost (GolfPowerRegion.compilerExit code destination s a b c tail)
      (UInt256.ofNat destination) output).execLength = s.execLength+9 := by
  simp only [jumpPost, GolfPowerRegion.compilerExit,
    GolfPowerRegion.compilerDupB, GolfPowerRegion.compilerDupA,
    GolfPowerRegion.compilerZero, GolfPowerRegion.compilerSwap, GolfPowerRegion.compilerAdd,
    GolfPowerRegion.compilerPower, mulPowerPost, binaryPost, pushedWidth, withCode]

#print axioms cost_jump
#print axioms mem_jump
#print axioms step_jump
#print axioms X_jump
#print axioms jump_preserves
#print axioms paired_jump
#print axioms compiler_jump_count
end GolfJump
