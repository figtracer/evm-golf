import Transport

/-! Canonical EVM region proof support against the pinned upstream semantics. -/
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM
namespace GolfUpstream

theorem deployed_power_boundary (owner : AccountAddress) (old new : ByteArray)
    (s t : EVM.State) (p : Operation.POp) (width k surplus : Nat)
    (a : UInt256) (tail : List UInt256) (fuel : Nat)
    (oldJumps newJumps : Array UInt256)
    (related : DeployedFrameWithGas owner old new surplus s t)
    (nonzero : p ≠ .PUSH0) (range : k < 256)
    (oldFragment : MulPowerAt old s.pc p width k)
    (newFragment : ShiftPowerAt new t.pc p width k)
    (stack : s.stack = a :: tail) (gas : 8 ≤ s.gasAvailable.toNat)
    (height : s.stack.length < 1024) :
    X (fuel+3) oldJumps s = X (fuel+1) oldJumps (mulPowerPost s old width k a tail) ∧
    X (fuel+3) newJumps t = X (fuel+1) newJumps (shiftPowerPost t new width k a tail) ∧
    DeployedFrameWithGas owner old new (surplus+2)
      (mulPowerPost s old width k a tail) (shiftPowerPost t new width k a tail) := by
  have samePC := deployed_frame_pc related
  have sameStack := deployed_frame_stack related
  have targetStack : t.stack = a :: tail := sameStack.symm.trans stack
  have targetHeight : t.stack.length < 1024 := by rw [←sameStack]; exact height
  have targetGas : 8 ≤ t.gasAvailable.toNat := by rw [related.gas]; omega
  have original := fullX_power_refinement s old new p width k a tail fuel oldJumps
    nonzero range oldFragment (by rw [samePC]; exact newFragment) stack gas height
  have candidate := fullX_power_refinement t old new p width k a tail fuel newJumps
    nonzero range (by rw [←samePC]; exact oldFragment) newFragment targetStack targetGas targetHeight
  have oldCode : withCode s old = s := by
    unfold withCode; rw [←related.maps.2.2.1.2.1]
  have newCode : withCode t new = t := by
    unfold withCode; rw [←related.maps.2.2.2.2.1]
  have oldRun := original.1
  have newRun := candidate.2.1
  rw [oldCode] at oldRun
  rw [newCode] at newRun
  refine ⟨oldRun, newRun, ?_, ?_, ?_⟩
  · have sameMul : deployedFrame (mulPowerPost s old width k a tail) =
        deployedFrame (mulPowerPost t old width k a tail) := by
      apply frame_binary_deployed
      apply frame_push_deployed
      exact frame_code s t old old related.frame
    exact sameMul.trans (congrArg eraseMaps candidate.2.2.1)
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

inductive OpenRegionTrace (old new : ByteArray) (residualFuel : Nat) :
    Nat → Nat → EVM.State → EVM.State → Prop where
  | done (s : EVM.State) : OpenRegionTrace old new residualFuel residualFuel 0 s s
  | same (s next final : EVM.State) (fuel count : Nat)
      (op : Operation .EVM) (arg : Option (UInt256 × Nat))
      (allowed : NonterminalStackOp op)
      (oldDecode : decode old s.pc = some (op,arg))
      (newDecode : decode new s.pc = some (op,arg))
      (bounds : FullXBounds s op)
      (canonical : EVM.step (fuel+1) (C' s op) (some (op,arg)) s = .ok next)
      (rest : OpenRegionTrace old new residualFuel (fuel+1) count next final) :
      OpenRegionTrace old new residualFuel (fuel+2) count s final
  | extended (s next final : EVM.State) (fuel count : Nat)
      (op : Operation .EVM) (arg : Option (UInt256 × Nat))
      (allowed : ExtendedStackOp op)
      (oldDecode : decode old s.pc = some (op,arg))
      (newDecode : decode new s.pc = some (op,arg))
      (bounds : FullXBounds s op)
      (canonical : EVM.step (fuel+1) (C' s op) (some (op,arg)) s = .ok next)
      (rest : OpenRegionTrace old new residualFuel (fuel+1) count next final) :
      OpenRegionTrace old new residualFuel (fuel+2) count s final
  | power (s final : EVM.State) (fuel count : Nat)
      (p : Operation.POp) (width k : Nat) (a : UInt256) (tail : List UInt256)
      (nonzero : p ≠ .PUSH0) (range : k < 256)
      (oldFragment : MulPowerAt old s.pc p width k)
      (newFragment : ShiftPowerAt new s.pc p width k)
      (stack : s.stack = a :: tail) (gas : 8 ≤ s.gasAvailable.toNat)
      (height : s.stack.length < 1024)
      (rest : OpenRegionTrace old new residualFuel (fuel+1) count
        (mulPowerPost s old width k a tail) final) :
      OpenRegionTrace old new residualFuel (fuel+3) (count+1) s final

theorem open_region_simulation (owner : AccountAddress) (old new : ByteArray)
    (fuel residualFuel count : Nat) (s candidate final : EVM.State) (surplus : Nat)
    (oldJumps newJumps : Array UInt256)
    (trace : OpenRegionTrace old new residualFuel fuel count s final)
    (related : DeployedFrameWithGas owner old new surplus s candidate) :
    ∃ candidateFinal : EVM.State,
      X fuel oldJumps s = X residualFuel oldJumps final ∧
      X fuel newJumps candidate = X residualFuel newJumps candidateFinal ∧
      DeployedFrameWithGas owner old new (surplus+2*count) final candidateFinal := by
  induction trace generalizing candidate surplus with
  | done s => exact ⟨candidate,rfl,rfl,by simpa using related⟩
  | same s next final fuel count op arg allowed oldDecode newDecode bounds canonical rest ih =>
    obtain ⟨cn, cb, cstep, nextRelated, _, _⟩ :=
      deployed_step_transport s candidate next fuel surplus owner old new op arg allowed bounds related canonical
    have sourceDecode : decode s.executionEnv.code s.pc = some (op,arg) := by
      rw [related.maps.2.2.1.2.1]; exact oldDecode
    have targetDecode : decode candidate.executionEnv.code candidate.pc = some (op,arg) := by
      rw [related.maps.2.2.2.2.1, ←deployed_frame_pc related]; exact newDecode
    obtain ⟨cf, sourceRun, targetRun, finalRelated⟩ := ih cn surplus nextRelated
    exact ⟨cf, (X_next s next fuel oldJumps op arg allowed sourceDecode bounds canonical).trans sourceRun,
      (X_next candidate cn fuel newJumps op arg allowed targetDecode cb cstep).trans targetRun, finalRelated⟩
  | extended s next final fuel count op arg allowed oldDecode newDecode bounds canonical rest ih =>
    obtain ⟨cn, cb, cstep, nextRelated, _, _⟩ :=
      extended_step_transport s candidate next fuel surplus owner old new op arg allowed bounds related canonical
    have sourceDecode : decode s.executionEnv.code s.pc = some (op,arg) := by
      rw [related.maps.2.2.1.2.1]; exact oldDecode
    have targetDecode : decode candidate.executionEnv.code candidate.pc = some (op,arg) := by
      rw [related.maps.2.2.2.2.1, ←deployed_frame_pc related]; exact newDecode
    obtain ⟨cf, sourceRun, targetRun, finalRelated⟩ := ih cn surplus nextRelated
    exact ⟨cf, (X_next_extended s next fuel oldJumps op arg allowed sourceDecode bounds canonical).trans sourceRun,
      (X_next_extended candidate cn fuel newJumps op arg allowed targetDecode cb cstep).trans targetRun, finalRelated⟩
  | power s final fuel count p width k a tail nz range oldFragment newFragment stack gas height rest ih =>
    have boundary := deployed_power_boundary owner old new s candidate p width k surplus a tail fuel
      oldJumps newJumps related nz range oldFragment
      (by rw [←deployed_frame_pc related]; exact newFragment) stack gas height
    obtain ⟨cf, sourceRun, targetRun, finalRelated⟩ := ih
      (shiftPowerPost candidate new width k a tail) (surplus+2) boundary.2.2
    refine ⟨cf,boundary.1.trans sourceRun,boundary.2.1.trans targetRun,?_⟩
    convert finalRelated using 1 <;> omega


#print axioms deployed_power_boundary
#print axioms open_region_simulation
end GolfUpstream
