import OffsetPower
import MaskSupport
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

theorem offset_extra_transport (s c next : EVM.State) (fuel candidateFuel surplus skipped : Nat)
    (owner : AccountAddress) (old new : ByteArray)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (allowed : CanonicalMaskWindow.ExtraOp op) (bounds : FullXBounds s op)
    (frame : DeployedOffset owner old new surplus skipped s c)
    (canonical : EVM.step (fuel+1) (C' s op) (some (op,arg)) s = .ok next) :
    ∃ cn : EVM.State,
      FullXBounds c op ∧
      EVM.step (candidateFuel+1) (C' c op) (some (op,arg)) c = .ok cn ∧
      DeployedOffset owner old new surplus skipped next cn ∧
      next.executionEnv.code = s.executionEnv.code ∧
      cn.executionEnv.code = c.executionEnv.code := by
  have stackEq := offset_stack frame
  have costs : C' c op = C' s op := by
    cases allowed with
    | lt => rfl
    | iszero => rfl
    | sub => rfl
    | and => rfl
    | not => rfl
    | bor => rfl
    | exchange e => rw [GolfSwapFamily.cost, GolfSwapFamily.cost]
  have cb : FullXBounds c op := {
    gas := by rw [costs]; have := bounds.gas; have := frame.gas; omega
    inputs := by rw [←stackEq]; exact bounds.inputs
    outputs := by rw [←stackEq]; exact bounds.outputs }
  cases allowed with
  | sub =>
    have two : 2 ≤ s.stack.length := bounds.inputs
    obtain ⟨b,a,tail,stack⟩ : ∃ b a tail, s.stack = b :: a :: tail := by
      cases hs : s.stack with
      | nil => simp [hs] at two
      | cons b xs =>
        cases xs with
        | nil => simp [hs] at two
        | cons a tail => exact ⟨b,a,tail,rfl⟩
    rw [(show C' s .SUB = 3 from rfl), step_sub s fuel 3 arg a b tail stack] at canonical
    have post : next = binaryPost s (UInt256.sub b a) tail 3 := (Except.ok.inj canonical).symm
    subst next
    refine ⟨binaryPost c (UInt256.sub b a) tail 3, cb, ?_, ?_, rfl, rfl⟩
    · exact step_sub c candidateFuel 3 arg a b tail (stackEq.symm.trans stack)
    · exact binary_preserves frame _ tail 3 (by decide) bounds.gas
  | and =>
    have two : 2 ≤ s.stack.length := bounds.inputs
    obtain ⟨b,a,tail,stack⟩ : ∃ b a tail, s.stack = b :: a :: tail := by
      cases hs : s.stack with
      | nil => simp [hs] at two
      | cons b xs =>
        cases xs with
        | nil => simp [hs] at two
        | cons a tail => exact ⟨b,a,tail,rfl⟩
    rw [(show C' s .AND = 3 from rfl), step_and s fuel 3 arg a b tail stack] at canonical
    have post : next = binaryPost s (b &&& a) tail 3 := (Except.ok.inj canonical).symm
    subst next
    refine ⟨binaryPost c (b &&& a) tail 3, cb, ?_, ?_, rfl, rfl⟩
    · exact step_and c candidateFuel 3 arg a b tail (stackEq.symm.trans stack)
    · exact binary_preserves frame _ tail 3 (by decide) bounds.gas
  | not =>
    have one : 1 ≤ s.stack.length := bounds.inputs
    obtain ⟨a,tail,stack⟩ : ∃ a tail, s.stack = a :: tail := by
      cases hs : s.stack with
      | nil => simp [hs] at one
      | cons a tail => exact ⟨a,tail,rfl⟩
    rw [(show C' s .NOT = 3 from rfl), step_not s fuel 3 arg a tail stack] at canonical
    have post : next = binaryPost s (UInt256.lnot a) tail 3 := (Except.ok.inj canonical).symm
    subst next
    refine ⟨binaryPost c (UInt256.lnot a) tail 3, cb, ?_, ?_, rfl, rfl⟩
    · exact step_not c candidateFuel 3 arg a tail (stackEq.symm.trans stack)
    · exact binary_preserves frame _ tail 3 (by decide) bounds.gas

  | lt =>
    have two : 2 ≤ s.stack.length := bounds.inputs
    obtain ⟨b,a,tail,stack⟩ : ∃ b a tail, s.stack = b :: a :: tail := by
      cases hs : s.stack with
      | nil => simp [hs] at two
      | cons b xs =>
        cases xs with
        | nil => simp [hs] at two
        | cons a tail => exact ⟨b,a,tail,rfl⟩
    rw [(show C' s .LT = 3 from rfl), step_lt s fuel 3 arg a b tail stack] at canonical
    have post : next = binaryPost s (UInt256.lt b a) tail 3 := (Except.ok.inj canonical).symm
    subst next
    refine ⟨binaryPost c (UInt256.lt b a) tail 3, cb, ?_, ?_, rfl, rfl⟩
    · exact step_lt c candidateFuel 3 arg a b tail (stackEq.symm.trans stack)
    · exact binary_preserves frame _ tail 3 (by decide) bounds.gas
  | iszero =>
    have one : 1 ≤ s.stack.length := bounds.inputs
    obtain ⟨a,tail,stack⟩ : ∃ a tail, s.stack = a :: tail := by
      cases hs : s.stack with
      | nil => simp [hs] at one
      | cons a tail => exact ⟨a,tail,rfl⟩
    rw [(show C' s .ISZERO = 3 from rfl), step_iszero s fuel 3 arg a tail stack] at canonical
    have post : next = binaryPost s (UInt256.isZero a) tail 3 := (Except.ok.inj canonical).symm
    subst next
    refine ⟨binaryPost c (UInt256.isZero a) tail 3, cb, ?_, ?_, rfl, rfl⟩
    · exact step_iszero c candidateFuel 3 arg a tail (stackEq.symm.trans stack)
    · exact binary_preserves frame _ tail 3 (by decide) bounds.gas

  | bor =>
    have two : 2 ≤ s.stack.length := bounds.inputs
    obtain ⟨b,a,tail,stack⟩ : ∃ b a tail, s.stack = b :: a :: tail := by
      cases hs : s.stack with
      | nil => simp [hs] at two
      | cons b xs =>
        cases xs with
        | nil => simp [hs] at two
        | cons a tail => exact ⟨b,a,tail,rfl⟩
    rw [(show C' s .OR = 3 from rfl), step_or s fuel 3 arg a b tail stack] at canonical
    have post : next = binaryPost s (b ||| a) tail 3 := (Except.ok.inj canonical).symm
    subst next
    refine ⟨binaryPost c (b ||| a) tail 3, cb, ?_, ?_, rfl, rfl⟩
    · exact step_or c candidateFuel 3 arg a b tail (stackEq.symm.trans stack)
    · exact binary_preserves frame _ tail 3 (by decide) bounds.gas
  | exchange e =>
    have low : GolfSwapFamily.depth e+1 ≤ s.stack.length := by
      simpa only [GolfSwapFamily.inputs,Option.getD_some] using bounds.inputs
    obtain ⟨a,z,middle,tail,index,stack⟩ := GolfSwapFamily.stack_decompose s e low
    rw [GolfSwapFamily.cost,
      GolfSwapFamily.step_prefix s e fuel 3 arg a z middle tail index stack] at canonical
    have post : next = binaryPost s z (middle ++ a :: tail) 3 :=
      (Except.ok.inj canonical).symm
    subst next
    refine ⟨binaryPost c z (middle ++ a :: tail) 3, cb, ?_, ?_, rfl, rfl⟩
    · rw [GolfSwapFamily.cost]
      exact GolfSwapFamily.step_prefix c e candidateFuel 3 arg a z middle tail index
        (stackEq.symm.trans stack)
    · exact binary_preserves frame z (middle ++ a :: tail) 3 (by decide)
        (by simpa only [GolfSwapFamily.cost] using bounds.gas)

#print axioms offset_step_transport
#print axioms offset_extended_transport
#print axioms offset_extra_transport
end GolfComposition
