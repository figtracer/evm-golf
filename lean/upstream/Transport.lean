import StateRelation
import Power

/-! Canonical EVM region proof support against the pinned upstream semantics. -/
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM
namespace GolfUpstream

structure DeployedFrameWithGas (owner : AccountAddress) (old new : ByteArray)
    (surplus : Nat) (baseline candidate : EVM.State) : Prop where
  frame : deployedFrame baseline = deployedFrame candidate
  gas : candidate.gasAvailable.toNat = baseline.gasAvailable.toNat + surplus
  maps : DeployedMaps owner old new baseline candidate

theorem deployed_frame_pc {owner old new surplus s c}
    (frame : DeployedFrameWithGas owner old new surplus s c) : s.pc = c.pc := by
  simpa only [deployedFrame, eraseMaps, eraseCodeGas] using congrArg EVM.State.pc frame.frame

theorem deployed_frame_stack {owner old new surplus s c}
    (frame : DeployedFrameWithGas owner old new surplus s c) : s.stack = c.stack := by
  simpa only [deployedFrame, eraseMaps, eraseCodeGas] using congrArg EVM.State.stack frame.frame

theorem deployed_frame_push {owner old new surplus s c} (v : UInt256) (width : Nat)
    (frame : DeployedFrameWithGas owner old new surplus s c) (enough : 3 ≤ s.gasAvailable.toNat) :
    DeployedFrameWithGas owner old new surplus (pushedWidth s v width) (pushedWidth c v width) := by
  exact ⟨frame_push_deployed s c v width frame.frame,
    gas_preservation s.gasAvailable c.gasAvailable 3 surplus (by decide) enough frame.gas, frame.maps⟩

theorem deployed_frame_binary {owner old new surplus s c} (v : UInt256)
    (tail : List UInt256) (cost : Nat) (small : cost < UInt256.size)
    (frame : DeployedFrameWithGas owner old new surplus s c) (enough : cost ≤ s.gasAvailable.toNat) :
    DeployedFrameWithGas owner old new surplus (binaryPost s v tail cost) (binaryPost c v tail cost) := by
  exact ⟨frame_binary_deployed s c v tail cost frame.frame,
    gas_preservation s.gasAvailable c.gasAvailable cost surplus small enough frame.gas, frame.maps⟩

theorem deployed_frame_stop {owner old new surplus s c}
    (frame : DeployedFrameWithGas owner old new surplus s c) :
    DeployedFrameWithGas owner old new surplus (stopped s) (stopped c) := by
  exact ⟨frame_stop_deployed s c frame.frame, frame.gas, frame.maps⟩

theorem deployed_step_transport (s c next : EVM.State) (fuel surplus : Nat)
    (owner : AccountAddress) (old new : ByteArray)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (allowed : NonterminalStackOp op) (bounds : FullXBounds s op)
    (frame : DeployedFrameWithGas owner old new surplus s c)
    (canonical : EVM.step (fuel + 1) (C' s op) (some (op, arg)) s = .ok next) :
    ∃ cn : EVM.State,
      FullXBounds c op ∧
      EVM.step (fuel + 1) (C' c op) (some (op, arg)) c = .ok cn ∧
      DeployedFrameWithGas owner old new surplus next cn ∧
      next.executionEnv.code = s.executionEnv.code ∧
      cn.executionEnv.code = c.executionEnv.code := by
  have stackEq := deployed_frame_stack frame
  have costs : C' c op = C' s op := by
    cases allowed with
    | push p nz => rw [cost_push c p nz, cost_push s p nz]
    | mul => rfl
    | shl => rfl
  have cb : FullXBounds c op := {
    gas := by rw [costs]; have := bounds.gas; have := frame.gas; omega
    inputs := by rw [← stackEq]; exact bounds.inputs
    outputs := by rw [← stackEq]; exact bounds.outputs }
  cases allowed with
  | push p nz =>
    cases arg with
    | none =>
      have bad : EVM.step (fuel + 1) (C' s (.Push p)) (some (.Push p, none)) s =
          .error .StackUnderflow := by
        cases p <;> first | exact False.elim (nz rfl) | rfl
      rw [bad] at canonical
      contradiction
    | some pair =>
      rcases pair with ⟨v, width⟩
      rw [cost_push s p nz, step_push s p v width fuel 3 nz] at canonical
      have post : next = pushedWidth s v width := (Except.ok.inj canonical).symm
      subst next
      refine ⟨pushedWidth c v width, cb, ?_, ?_, rfl, rfl⟩
      · rw [cost_push c p nz]
        exact step_push c p v width fuel 3 nz
      · exact deployed_frame_push v width frame (by simpa [cost_push s p nz] using bounds.gas)
  | mul =>
    have two : 2 ≤ s.stack.length := bounds.inputs
    obtain ⟨b, a, tail, stack⟩ : ∃ b a tail, s.stack = b :: a :: tail := by
      cases hs : s.stack with
      | nil => simp [hs] at two
      | cons b xs =>
        cases xs with
        | nil => simp [hs] at two
        | cons a tail => exact ⟨b, a, tail, rfl⟩
    rw [cost_mul, step_mul s fuel 5 arg a b tail stack] at canonical
    have post : next = binaryPost s (UInt256.mul b a) tail 5 := (Except.ok.inj canonical).symm
    subst next
    refine ⟨binaryPost c (UInt256.mul b a) tail 5, cb, ?_, ?_, rfl, rfl⟩
    · exact step_mul c fuel 5 arg a b tail (stackEq.symm.trans stack)
    · exact deployed_frame_binary _ tail 5 (by decide) frame bounds.gas
  | shl =>
    have two : 2 ≤ s.stack.length := bounds.inputs
    obtain ⟨b, a, tail, stack⟩ : ∃ b a tail, s.stack = b :: a :: tail := by
      cases hs : s.stack with
      | nil => simp [hs] at two
      | cons b xs =>
        cases xs with
        | nil => simp [hs] at two
        | cons a tail => exact ⟨b, a, tail, rfl⟩
    rw [cost_shl, step_shl s fuel 3 arg a b tail stack] at canonical
    have post : next = binaryPost s (UInt256.shiftLeft a b) tail 3 := (Except.ok.inj canonical).symm
    subst next
    refine ⟨binaryPost c (UInt256.shiftLeft a b) tail 3, cb, ?_, ?_, rfl, rfl⟩
    · exact step_shl c fuel 3 arg a b tail (stackEq.symm.trans stack)
    · exact deployed_frame_binary _ tail 3 (by decide) frame bounds.gas

theorem extended_step_transport (s c next : EVM.State) (fuel surplus : Nat)
    (owner : AccountAddress) (old new : ByteArray)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (allowed : ExtendedStackOp op) (bounds : FullXBounds s op)
    (frame : DeployedFrameWithGas owner old new surplus s c)
    (canonical : EVM.step (fuel+1) (C' s op) (some (op,arg)) s = .ok next) :
    ∃ cn : EVM.State,
      FullXBounds c op ∧
      EVM.step (fuel+1) (C' c op) (some (op,arg)) c = .ok cn ∧
      DeployedFrameWithGas owner old new surplus next cn ∧
      next.executionEnv.code = s.executionEnv.code ∧
      cn.executionEnv.code = c.executionEnv.code := by
  have stackEq := deployed_frame_stack frame
  have costs : C' c op = C' s op := by cases allowed <;> rfl
  have cb : FullXBounds c op := {
    gas := by rw [costs]; have := bounds.gas; have := frame.gas; omega
    inputs := by rw [←stackEq]; exact bounds.inputs
    outputs := by rw [←stackEq]; exact bounds.outputs }
  cases allowed with
  | add =>
    have two : 2 ≤ s.stack.length := bounds.inputs
    obtain ⟨b,a,tail,stack⟩ : ∃ b a tail, s.stack = b :: a :: tail := by
      cases hs : s.stack with
      | nil => simp [hs] at two
      | cons b xs =>
        cases xs with
        | nil => simp [hs] at two
        | cons a tail => exact ⟨b,a,tail,rfl⟩
    rw [cost_add, step_add s fuel 3 arg a b tail stack] at canonical
    have post : next = binaryPost s (UInt256.add b a) tail 3 := (Except.ok.inj canonical).symm
    subst next
    refine ⟨binaryPost c (UInt256.add b a) tail 3, cb, ?_, ?_, rfl, rfl⟩
    · exact step_add c fuel 3 arg a b tail (stackEq.symm.trans stack)
    · exact deployed_frame_binary _ tail 3 (by decide) frame bounds.gas
  | swap1 =>
    have two : 2 ≤ s.stack.length := bounds.inputs
    obtain ⟨b,a,tail,stack⟩ : ∃ b a tail, s.stack = b :: a :: tail := by
      cases hs : s.stack with
      | nil => simp [hs] at two
      | cons b xs =>
        cases xs with
        | nil => simp [hs] at two
        | cons a tail => exact ⟨b,a,tail,rfl⟩
    rw [cost_swap1, step_swap1 s fuel 3 arg a b tail stack] at canonical
    have post : next = binaryPost s a (b :: tail) 3 := (Except.ok.inj canonical).symm
    subst next
    refine ⟨binaryPost c a (b :: tail) 3, cb, ?_, ?_, rfl, rfl⟩
    · exact step_swap1 c fuel 3 arg a b tail (stackEq.symm.trans stack)
    · exact deployed_frame_binary _ (b :: tail) 3 (by decide) frame bounds.gas
  | push0 =>
    rw [cost_push0, step_push0 s fuel 2 arg] at canonical
    have post : next = binaryPost s (UInt256.ofNat 0) s.stack 2 := (Except.ok.inj canonical).symm
    subst next
    refine ⟨binaryPost c (UInt256.ofNat 0) s.stack 2, cb, ?_, ?_, rfl, rfl⟩
    · rw [stackEq]; exact step_push0 c fuel 2 arg
    · exact deployed_frame_binary _ s.stack 2 (by decide) frame bounds.gas
  | dup1 =>
    have one : 1 ≤ s.stack.length := bounds.inputs
    obtain ⟨a,tail,stack⟩ : ∃ a tail, s.stack = a :: tail := by
      cases hs : s.stack with
      | nil => simp [hs] at one
      | cons a tail => exact ⟨a,tail,rfl⟩
    rw [cost_dup1, step_dup1 s fuel 3 arg a tail stack] at canonical
    have post : next = binaryPost s a (a :: tail) 3 := (Except.ok.inj canonical).symm
    subst next
    refine ⟨binaryPost c a (a :: tail) 3, cb, ?_, ?_, rfl, rfl⟩
    · exact step_dup1 c fuel 3 arg a tail (stackEq.symm.trans stack)
    · exact deployed_frame_binary _ (a :: tail) 3 (by decide) frame bounds.gas


#print axioms deployed_step_transport
#print axioms extended_step_transport
end GolfUpstream
