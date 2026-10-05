import Driver

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream
namespace GolfSwapFamily

def depth (e : Operation.ExOp) : Nat := (serializeSwapInstr e).toNat - 143

theorem depth_range (e : Operation.ExOp) : 1 ≤ depth e ∧ depth e ≤ 16 := by
  cases e <;> decide

theorem inputs (e : Operation.ExOp) : δ (.Exchange e) = some (depth e + 1) := by
  cases e <;> rfl

theorem outputs (e : Operation.ExOp) : α (.Exchange e) = some (depth e + 1) := by
  cases e <;> rfl

theorem cost (s : EVM.State) (e : Operation.ExOp) : C' s (.Exchange e) = 3 := by
  cases e <;> rfl

theorem memory (s : EVM.State) (e : Operation.ExOp) :
    memoryExpansionCost s (.Exchange e) = 0 := by
  cases e <;> simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

-- The executed path is EvmYul.step -> EvmYul.swap, not the duplicate EVM.swap.
theorem step_dispatch (s : EVM.State) (e : Operation.ExOp)
    (fuel gas : Nat) (arg : Option (UInt256 × Nat)) :
    EVM.step (fuel+1) gas (some (.Exchange e,arg)) s =
      EvmYul.swap (depth e)
        {s with gasAvailable := s.gasAvailable-UInt256.ofNat gas,
                execLength := s.execLength+1} := by
  cases e <;> rfl

private theorem prefix_split (front suffix : List UInt256) :
    (front ++ suffix).take front.length = front ∧
    (front ++ suffix).drop front.length = suffix := by
  induction front with
  | nil => simp
  | cons x xs ih => simp_all

-- The index is witnessed by the exact intervening list; no default-word lookup.
theorem swap_prefix (s : EVM.State) (a z : UInt256)
    (middle tail : List UInt256)
    (stack : s.stack = a :: (middle ++ z :: tail)) :
    EvmYul.swap (middle.length+1) s =
      .ok (s.replaceStackAndIncrPC (z :: (middle ++ a :: tail))) := by
  let front := a :: (middle ++ [z])
  have represented : s.stack = front ++ tail := by
    simpa only [front,List.cons_append,List.append_assoc,List.singleton_append] using stack
  have length : front.length = middle.length+2 := by simp [front]
  have parts := prefix_split front tail
  have takePart : s.stack.take (middle.length+1+1) = front := by
    rw [represented,←length]
    exact parts.1
  have dropPart : s.stack.drop (middle.length+1+1) = tail := by
    rw [represented,←length]
    exact parts.2
  have last : front.getLast? = some z := by
    exact List.getLast?_concat (l := a :: middle) (a := z)
  unfold EvmYul.swap
  rw [takePart,dropPart]
  simp only [List.getLast!_eq_getLast?_getD,last,Option.getD_some]
  simp [front,List.append_assoc]

theorem step_prefix (s : EVM.State) (e : Operation.ExOp)
    (fuel gas : Nat) (arg : Option (UInt256 × Nat))
    (a z : UInt256) (middle tail : List UInt256)
    (index : middle.length+1 = depth e)
    (stack : s.stack = a :: (middle ++ z :: tail)) :
    EVM.step (fuel+1) gas (some (.Exchange e,arg)) s =
      .ok (binaryPost s z (middle ++ a :: tail) gas) := by
  rw [step_dispatch,←index]
  have swapped := swap_prefix
    {s with gasAvailable := s.gasAvailable-UInt256.ofNat gas,
            execLength := s.execLength+1} a z middle tail stack
  rw [swapped]
  rfl

private theorem split_at (xs : List UInt256) (n : Nat) (inside : n < xs.length) :
    ∃ middle z tail, middle.length = n ∧ xs = middle ++ z :: tail := by
  induction n generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at inside
    | cons z tail => exact ⟨[],z,tail,rfl,rfl⟩
  | succ n ih =>
    cases xs with
    | nil => simp at inside
    | cons a xs =>
      have smaller : n < xs.length := by
        simp only [List.length_cons] at inside
        omega
      obtain ⟨middle,z,tail,len,shape⟩ := ih xs smaller
      refine ⟨a::middle,z,tail,?_,?_⟩
      · simp only [List.length_cons,len]
      · simp only [List.cons_append,shape]

theorem stack_decompose (s : EVM.State) (e : Operation.ExOp)
    (low : depth e+1 ≤ s.stack.length) :
    ∃ a z middle tail, middle.length+1 = depth e ∧
      s.stack = a :: (middle ++ z :: tail) := by
  have range := depth_range e
  cases hs : s.stack with
  | nil => simp only [hs,List.length_nil] at low; omega
  | cons a xs =>
    have inside : depth e-1 < xs.length := by
      simp only [hs,List.length_cons] at low
      omega
    obtain ⟨middle,z,tail,len,shape⟩ := split_at xs (depth e-1) inside
    refine ⟨a,z,middle,tail,?_,?_⟩
    · omega
    · simp only [hs,shape]

theorem bounds (s : EVM.State) (e : Operation.ExOp)
    (gas : 3 ≤ s.gasAvailable.toNat) (low : depth e+1 ≤ s.stack.length)
    (high : s.stack.length ≤ 1024) : FullXBounds s (.Exchange e) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [cost] using gas
  · simpa only [inputs,Option.getD_some] using low
  · simp only [inputs,outputs,Option.getD_some]
    omega

theorem X_next (s next : EVM.State) (e : Operation.ExOp)
    (fuel : Nat) (jumps : Array UInt256) (arg : Option (UInt256 × Nat))
    (decoded : decode s.executionEnv.code s.pc = some (.Exchange e,arg))
    (safe : FullXBounds s (.Exchange e))
    (canonical : EVM.step (fuel+1) (C' s (.Exchange e))
      (some (.Exchange e,arg)) s = .ok next) :
    X (fuel+2) jumps s = X (fuel+1) jumps next := by
  have gas : ¬ s.gasAvailable.toNat < 3 := by
    have h := safe.gas
    rw [cost] at h
    omega
  have low : ¬s.stack.length < depth e+1 := by
    have h := safe.inputs
    simp only [inputs,Option.getD_some] at h
    omega
  have high : ¬1024 < s.stack.length-(depth e+1)+(depth e+1) := by
    have h := safe.outputs
    simp only [inputs,outputs,Option.getD_some] at h
    omega
  conv_lhs => unfold X
  simp only [decoded]
  simp [memory,cost,Operation.isCreate,inputs,outputs,gas,low,high]
  change (do
    let next ← EVM.step (fuel+1) 3 (some (.Exchange e,arg)) s
    X (fuel+1) jumps next) = _
  rw [cost] at canonical
  rw [canonical]
  rfl

#print axioms depth_range
#print axioms inputs
#print axioms outputs
#print axioms cost
#print axioms memory
#print axioms step_dispatch
#print axioms swap_prefix
#print axioms step_prefix
#print axioms stack_decompose
#print axioms bounds
#print axioms X_next
end GolfSwapFamily
