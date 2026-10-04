import OffsetPower
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset
namespace GolfComposition
theorem binary_preserves {owner old new surplus skipped s t}
 (h : DeployedOffset owner old new surplus skipped s t)
 (value : UInt256) (tail : List UInt256) (cost : Nat)
 (small : cost < UInt256.size) (enough : cost ≤ s.gasAvailable.toNat) :
 DeployedOffset owner old new surplus skipped (binaryPost s value tail cost) (binaryPost t value tail cost) := by
 refine ⟨?_,?_,gas_preservation s.gasAvailable t.gasAvailable cost surplus small enough h.gas,h.maps⟩
 · have hh := congrArg (fun st => binaryPost st value tail cost) h.frame
   simpa [eraseCount,deployedFrame,eraseMaps,eraseCodeGas,binaryPost] using
     congrArg (fun st => eraseCount (deployedFrame st)) hh
 · simp only [binaryPost]
   have := h.count
   omega

theorem push_preserves {owner old new surplus skipped s t}
 (h : DeployedOffset owner old new surplus skipped s t)
 (value : UInt256) (width : Nat) (enough : 3 ≤ s.gasAvailable.toNat) :
 DeployedOffset owner old new surplus skipped (pushedWidth s value width) (pushedWidth t value width) := by
 refine ⟨?_,?_,gas_preservation s.gasAvailable t.gasAvailable 3 surplus (by decide) enough h.gas,h.maps⟩
 · have hh := congrArg (fun st => pushedWidth st value width) h.frame
   simpa [eraseCount,deployedFrame,eraseMaps,eraseCodeGas,pushedWidth] using
     congrArg (fun st => eraseCount (deployedFrame st)) hh
 · simp only [pushedWidth]
   have := h.count
   omega

theorem offset_step_transport (s c next : EVM.State) (fuel candidateFuel surplus skipped : Nat)
    (owner : AccountAddress) (old new : ByteArray)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (allowed : NonterminalStackOp op) (bounds : FullXBounds s op)
    (frame : DeployedOffset owner old new surplus skipped s c)
    (canonical : EVM.step (fuel + 1) (C' s op) (some (op, arg)) s = .ok next) :
    ∃ cn : EVM.State,
      FullXBounds c op ∧
      EVM.step (candidateFuel + 1) (C' c op) (some (op, arg)) c = .ok cn ∧
      DeployedOffset owner old new surplus skipped next cn ∧
      next.executionEnv.code = s.executionEnv.code ∧
      cn.executionEnv.code = c.executionEnv.code := by
  have stackEq := offset_stack frame
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
        exact step_push c p v width candidateFuel 3 nz
      · exact push_preserves frame v width (by simpa [cost_push s p nz] using bounds.gas)
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
    · exact step_mul c candidateFuel 5 arg a b tail (stackEq.symm.trans stack)
    · exact binary_preserves frame _ tail 5 (by decide) bounds.gas
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
    · exact step_shl c candidateFuel 3 arg a b tail (stackEq.symm.trans stack)
    · exact binary_preserves frame _ tail 3 (by decide) bounds.gas

theorem offset_extended_transport (s c next : EVM.State) (fuel candidateFuel surplus skipped : Nat)
    (owner : AccountAddress) (old new : ByteArray)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (allowed : ExtendedStackOp op) (bounds : FullXBounds s op)
    (frame : DeployedOffset owner old new surplus skipped s c)
    (canonical : EVM.step (fuel+1) (C' s op) (some (op,arg)) s = .ok next) :
    ∃ cn : EVM.State,
      FullXBounds c op ∧
      EVM.step (candidateFuel+1) (C' c op) (some (op,arg)) c = .ok cn ∧
      DeployedOffset owner old new surplus skipped next cn ∧
      next.executionEnv.code = s.executionEnv.code ∧
      cn.executionEnv.code = c.executionEnv.code := by
  have stackEq := offset_stack frame
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
    · exact step_add c candidateFuel 3 arg a b tail (stackEq.symm.trans stack)
    · exact binary_preserves frame _ tail 3 (by decide) bounds.gas
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
    · exact step_swap1 c candidateFuel 3 arg a b tail (stackEq.symm.trans stack)
    · exact binary_preserves frame _ (b :: tail) 3 (by decide) bounds.gas
  | push0 =>
    rw [cost_push0, step_push0 s fuel 2 arg] at canonical
    have post : next = binaryPost s (UInt256.ofNat 0) s.stack 2 := (Except.ok.inj canonical).symm
    subst next
    refine ⟨binaryPost c (UInt256.ofNat 0) s.stack 2, cb, ?_, ?_, rfl, rfl⟩
    · rw [stackEq]; exact step_push0 c candidateFuel 2 arg
    · exact binary_preserves frame _ s.stack 2 (by decide) bounds.gas
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
    · exact step_dup1 c candidateFuel 3 arg a tail (stackEq.symm.trans stack)
    · exact binary_preserves frame _ (a :: tail) 3 (by decide) bounds.gas

#print axioms offset_step_transport
#print axioms offset_extended_transport
end GolfComposition
