import WholeWOp
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition

/-! Interpreter facts for arithmetic window instructions. -/
namespace GolfWhole

theorem wfacts_un (f : UnK) : WFacts (.un f) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k e => by cases e⟩ <;> cases f <;> first
      | (intro s; rfl; done)
      | (intro s; simp [WOp.op, memoryExpansionCost, memoryExpansionCost.μᵢ']; done)
      | (intro μ; simp [H, WOp.op]; done)
      | rfl
      | (simp [WOp.op, δ]; done)
      | (intro l hl; simp only [WOp.need] at hl
         match l, hl with
         | x :: l', _ => simp [WOp.op, WOp.apply, δ, α])
      | (simp [WOp.op]; done)
      | (intro st; simp [WOp.op, W]; done)
      | (intro f u h
         simp only [WOp.need] at h
         obtain ⟨x, l', hs⟩ : ∃ x l', u.stack = x :: l' := by
           match e : u.stack, h with
           | x :: l', _ => exact ⟨x, l', rfl⟩
         change EVM.execUnOp _ (bump u _) = _
         unfold EVM.execUnOp
         have : ∀ c, (bump u c).stack = x :: l' := fun _ => hs
         simp only [this, Stack.pop, WOp.apply, hs]
         rfl)

theorem wfacts_bin (f : BinK) : WFacts (.bin f) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k e => by cases e⟩ <;> cases f <;> first
      | (intro s; rfl; done)
      | (intro s; simp [WOp.op, memoryExpansionCost, memoryExpansionCost.μᵢ']; done)
      | (intro μ; simp [H, WOp.op]; done)
      | rfl
      | (simp [WOp.op, δ]; done)
      | (intro l hl; simp only [WOp.need] at hl
         match l, hl with
         | x :: y :: l', _ => simp [WOp.op, WOp.apply, δ, α])
      | (simp [WOp.op]; done)
      | (intro st; simp [WOp.op, W]; done)
      | (intro f u h
         simp only [WOp.need] at h
         obtain ⟨x, y, l', hs⟩ : ∃ x y l', u.stack = x :: y :: l' := by
           match e : u.stack, h with
           | x :: y :: l', _ => exact ⟨x, y, l', rfl⟩
         change EVM.execBinOp _ (bump u _) = _
         unfold EVM.execBinOp
         have : ∀ c, (bump u c).stack = x :: y :: l' := fun _ => hs
         simp only [this, Stack.pop2, WOp.apply, hs]
         rfl)

theorem wfacts (op : WOp) (v : op.valid = true) : WFacts op := by
  cases op with
  | push p x w =>
    have nz : p ≠ .PUSH0 := by simpa [WOp.valid] using v
    refine ⟨fun s => cost_push s p nz, fun s => mem_push s p, fun _ => by simp [H, WOp.op], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cases p <;> first | exact absurd rfl nz | rfl
    · cases p <;> first | exact absurd rfl nz | simp [WOp.op, δ]
    · intro l _; cases p <;> first | exact absurd rfl nz | simp [WOp.op, WOp.apply, WOp.need, δ, α]
    · simp [WOp.op]
    · intro st; cases p <;> first | exact absurd rfl nz | simp [WOp.op, W]
    · cases p <;> first | exact absurd rfl nz | rfl
    · intro f u _
      have e : EVM.step (f + 1) 3 (some (.Push p, some (x, w))) u = EvmYul.step (.Push p) (some (x, w)) (bump u 3) := by
        cases p <;> first | exact absurd rfl nz | rfl
      simp only [WOp.op, WOp.arg, WOp.cost, WOp.apply, WOp.len]
      rw [e]
      cases p <;> first | exact absurd rfl nz | rfl
    · intro k h; cases h
  | push0 =>
    refine ⟨fun _ => rfl, fun s => by simp [WOp.op, memoryExpansionCost, memoryExpansionCost.μᵢ'],
      fun _ => by simp [H, WOp.op], rfl, by simp [WOp.op, δ], ?_, by simp [WOp.op],
      fun st => by simp [WOp.op, W], rfl, fun f u _ => rfl, fun k e => by cases e⟩
    intro l _; simp [WOp.op, WOp.apply, δ, α]
  | dup k => exact wfacts_dup k v
  | swap k => exact wfacts_swap k v
  | pop =>
    refine ⟨fun _ => rfl, fun s => by simp [WOp.op, memoryExpansionCost, memoryExpansionCost.μᵢ'],
      fun _ => by simp [H, WOp.op], rfl, by simp [WOp.op, δ], ?_, by simp [WOp.op], fun st => by simp [WOp.op, W],
      rfl, ?_, fun k e => by cases e⟩
    · intro l hl; simp [WOp.op, WOp.apply, WOp.need, δ, α] at hl ⊢
    · intro f u h
      simp only [WOp.need] at h
      obtain ⟨x, xs, hs⟩ : ∃ x xs, u.stack = x :: xs := by
        match e : u.stack, h with
        | x :: xs, _ => exact ⟨x, xs, rfl⟩
      change (match (bump u 2).stack.pop with
        | some ⟨s, _⟩ => Except.ok ((bump u 2).replaceStackAndIncrPC s)
        | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) = _
      have : (bump u 2).stack = x :: xs := hs
      simp [this, Stack.pop, WOp.apply, hs]
      rfl
  | un f => exact wfacts_un f
  | bin f => exact wfacts_bin f

#print axioms wfacts

end GolfWhole
