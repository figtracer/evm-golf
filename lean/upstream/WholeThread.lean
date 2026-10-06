import WholeProgram
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition

/-! Jump threading `PUSH X; JUMPI` → `PUSH Y; JUMPI` where `X: JUMPDEST; PUSH Y; JUMP`. -/
namespace GolfWhole

theorem gasCut_zero {s : State} {op : Operation .EVM} (m : memoryExpansionCost s op = 0) :
    gasCut s op = s := by
  simp only [gasCut, m, word_sub_zero]

/-- One source step through a memory-free, non-halting instruction. -/
theorem source_step {j : Array UInt256} {s : State} {op : Operation .EVM}
    {arg : Option (UInt256 × Nat)} {f : ℕ} {r : ExecutionResult State}
    (decoded : decode s.executionEnv.code s.pc = some (op, arg)) (running : Running op)
    (m : memoryExpansionCost s op = 0) (ok : X (f + 1) j s = .ok r) :
    ZOk j op s ∧ ∃ g n, f = g + 1 ∧ EVM.step (g + 1) (C' s op) (some (op, arg)) s = .ok n ∧
      X (g + 1) j n = .ok r := by
  obtain ⟨z, n, step, rest⟩ := X_inv (getD_of decoded) ok
  rw [running] at rest
  rw [gasCut_zero m] at step
  refine ⟨z, ?_⟩
  cases f with
  | zero => rw [step_zero] at step; cases step
  | succ g => exact ⟨g, n, rfl, step, rest⟩

theorem candidate_run {j : Array UInt256} {t n : State} {op : Operation .EVM}
    {arg : Option (UInt256 × Nat)}
    (decoded : decode t.executionEnv.code t.pc = some (op, arg)) (running : Running op)
    (m : memoryExpansionCost t op = 0) (z : ZOk j op t)
    (step : ∀ g, EVM.step (g + 1) (C' t op) (some (op, arg)) t = .ok n) :
    ∀ g, X (g + 2) j t = X (g + 1) j n := by
  intro g
  have sg := step g
  rw [← gasCut_zero m] at sg
  rw [X_run (getD_of decoded) z sg, running]

def pushS (s : State) (v : UInt256) (w : ℕ) : State :=
  { s with
    stack := v :: s.stack
    pc := s.pc + UInt256.ofNat (w + 1)
    gasAvailable := s.gasAvailable - UInt256.ofNat 3
    execLength := s.execLength + 1 }

def jumpiS (s : State) (a b : UInt256) (tail : List UInt256) : State :=
  { bump s 10 with
    pc := if b != ⟨0⟩ then a else s.pc + ⟨1⟩
    stack := tail }

theorem step_jumpi' (f : ℕ) (s : State) (a b : UInt256) (tail : List UInt256)
    (stack : s.stack = a :: b :: tail) :
    EVM.step (f + 1) 10 (some (.JUMPI, none)) s = .ok (jumpiS s a b tail) := by
  have e : EVM.step (f + 1) 10 (some (.JUMPI, none)) s =
      (match (bump s 10).stack.pop2 with
        | some ⟨stack, μ₀, μ₁⟩ =>
          Except.ok { bump s 10 with pc := if μ₁ != ⟨0⟩ then μ₀ else (bump s 10).pc + ⟨1⟩, stack := stack }
        | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := rfl
  rw [e]
  have hp : (bump s 10).stack.pop2 = some (tail, a, b) := by simp [bump, stack, Stack.pop2]
  rw [hp]
  rfl

theorem step_jumpdest' (f : ℕ) (s : State) :
    EVM.step (f + 1) 1 (some (.JUMPDEST, none)) s = .ok (bump s 1).incrPC := rfl

def jumpS (s : State) (a : UInt256) (tail : List UInt256) : State :=
  { bump s 8 with
    pc := a
    stack := tail }

theorem step_jump' (f : ℕ) (s : State) (a : UInt256) (tail : List UInt256)
    (stack : s.stack = a :: tail) :
    EVM.step (f + 1) 8 (some (.JUMP, none)) s = .ok (jumpS s a tail) := by
  have e : EVM.step (f + 1) 8 (some (.JUMP, none)) s =
      (match (bump s 8).stack.pop with
        | some ⟨stack, μ₀⟩ => Except.ok { bump s 8 with pc := μ₀, stack := stack }
        | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := rfl
  rw [e]
  have hp : (bump s 8).stack.pop = some (tail, a) := by simp [bump, stack, Stack.pop]
  rw [hp]
  rfl

theorem mem_jumpi (s : State) : memoryExpansionCost s .JUMPI = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
theorem mem_jumpdest (s : State) : memoryExpansionCost s .JUMPDEST = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
theorem mem_jump' (s : State) : memoryExpansionCost s .JUMP = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

theorem bne_of_ne {c : UInt256} (h : c ≠ ⟨0⟩) : (c != ⟨0⟩) = true := by
  obtain ⟨v⟩ := c
  have hv : v ≠ 0 := fun e => h (by rw [e])
  have e : ((⟨v⟩ : UInt256) == ⟨0⟩) = (v == 0) := rfl
  simp [bne, e, hv]

theorem bne_zero : ((⟨0⟩ : UInt256) != ⟨0⟩) = false := by decide

theorem contains_of_notIn {j : Array UInt256} {a : UInt256} (h : ¬X.notIn (some a) j = true) :
    j.contains a = true := by
  simpa [X.notIn, X.belongs] using h

theorem thread_segment (owner : AccountAddress) (old new : ByteArray) (oj nj : Array UInt256)
    (Q : UInt256 → List UInt256 → Prop) (A : List UInt256 → Prop) (pc : UInt256) (p q : Operation.POp) (w w' : ℕ) (x y : UInt256)
    (nzp : p ≠ .PUSH0) (nzq : q ≠ .PUSH0)
    (o : decode old pc = some (.Push p, some (x, w)))
    (n : decode new pc = some (.Push p, some (y, w)))
    (oi : decode old (pc + UInt256.ofNat (w + 1)) = some (.JUMPI, none))
    (ni : decode new (pc + UInt256.ofNat (w + 1)) = some (.JUMPI, none))
    (t1 : decode old x = some (.JUMPDEST, none))
    (t2 : decode old (x + UInt256.ofNat 1) = some (.Push q, some (y, w')))
    (t3 : decode old (x + UInt256.ofNat 1 + UInt256.ofNat (w' + 1)) = some (.JUMP, none))
    (fall : ∀ tail, A (⟨0⟩ :: tail) → Q (pc + UInt256.ofNat (w + 1) + UInt256.ofNat 1) tail)
    (target : ∀ c tail, A (c :: tail) → c ≠ ⟨0⟩ → Q y tail)
    (jumps : ∀ z, oj.contains z = true → nj.contains z = true) :
    Segment owner old new oj nj Q A pc := by
  intro fuel s t surplus skipped r rel hpc hA ok
  have sc : s.executionEnv.code = old := rel.maps.2.2.1.2.1
  have tc : t.executionEnv.code = new := rel.maps.2.2.2.2.1
  have samePC := offset_pc rel
  have st := rel_stack rel
  subst hpc
  cases fuel with
  | zero => rw [X_zero] at ok; cases ok
  | succ f =>
  -- source PUSH x
  obtain ⟨zA, fA, nA, rfl, stepA, restA⟩ :=
    source_step (by rw [sc]; exact o) (fun _ => by simp [H]) (mem_push _ _) ok
  rw [cost_push s p nzp, step_push s p x w fA 3 nzp] at stepA
  injection stepA with hA
  subst hA
  -- source JUMPI
  obtain ⟨zB, fB, nB, rfl, stepB, restB⟩ :=
    source_step (s := pushS s x w) (by show decode s.executionEnv.code _ = _; rw [sc]; exact oi)
      (fun _ => by simp [H]) (mem_jumpi _) restA
  have inB := zB.inputs
  simp only [δ, Option.getD, pushS, List.length_cons] at inB
  obtain ⟨c, tail, hs⟩ : ∃ c tail, s.stack = c :: tail := by
    match h : s.stack, inB with
    | c :: tail, _ => exact ⟨c, tail, rfl⟩
  rw [show C' (pushS s x w) .JUMPI = 10 from rfl,
    step_jumpi' fB (pushS s x w) x c tail (by simp [pushS, hs])] at stepB
  injection stepB with hB
  subst hB
  have gA := zA.cost
  rw [gasCut_zero (mem_push _ _), cost_push _ p nzp] at gA
  have gB := zB.cost
  rw [gasCut_zero (mem_jumpi _), show C' (pushS s x w) .JUMPI = 10 from rfl] at gB
  change 10 ≤ (s.gasAvailable - UInt256.ofNat 3).toNat at gB
  rw [word_sub_toNat _ 3 (by decide) gA] at gB
  have tg : t.gasAvailable.toNat = s.gasAvailable.toNat + surplus := rel.gas
  -- candidate PUSH y then JUMPI
  have dtA : decode t.executionEnv.code t.pc = some (.Push p, some (y, w)) := by
    rw [tc, ← samePC]; exact n
  have zt := (Z_transport rel (w := .Push p) (by rw [gasCut_zero (mem_push _ _),
    gasCut_zero (mem_push _ _), cost_push _ p nzp, cost_push _ p nzp]) jumps zA).1
  have candA : ∀ g, X (g + 2) nj t = X (g + 1) nj (pushS t y w) := candidate_run dtA
    (fun _ => by simp [H]) (mem_push _ _) zt (fun g => by
      rw [cost_push t p nzp, step_push t p y w g 3 nzp]; rfl)
  have dtB : decode (pushS t y w).executionEnv.code (pushS t y w).pc = some (.JUMPI, none) := by
    show decode t.executionEnv.code (t.pc + _) = _; rw [tc, ← samePC]; exact ni
  have tStack : t.stack = c :: tail := st ▸ hs
  have ztB : (c ≠ ⟨0⟩ → nj.contains y = true) → ZOk nj .JUMPI (pushS t y w) := by
    intro valid
    have tg3 : 3 ≤ t.gasAvailable.toNat := by omega
    refine ⟨by rw [mem_jumpi]; omega, ?_, by simp [δ], ?_, by simp, ?_, by simp, ?_, ?_, by simp,
      by rintro ⟨h, -⟩; exact absurd h (by decide)⟩
    · rw [gasCut_zero (mem_jumpi _), show C' (pushS t y w) .JUMPI = 10 from rfl]
      change 10 ≤ (t.gasAvailable - UInt256.ofNat 3).toNat
      rw [word_sub_toNat _ 3 (by decide) tg3]; omega
    · simp [δ, pushS, tStack]
    · rintro ⟨-, h1, h2⟩
      simp only [pushS, tStack, List.getElem?_cons_succ, List.getElem?_cons_zero, ne_eq,
        Option.some.injEq] at h1 h2
      have := valid h1
      simp [X.notIn, X.belongs, this] at h2
    · simp [δ, α, pushS, tStack]
      have := zA.outputs
      simp [δ, α, hs] at this
      omega
    · simp [W]
  have sub := fun (g : UInt256) (k : ℕ) (hk : k < UInt256.size) (h : k ≤ g.toNat) =>
    word_sub_toNat g k hk h
  by_cases hc : c = ⟨0⟩
  · -- fall through: both continue after JUMPI with equal gas spent
    subst hc
    have candB : ∀ g, X (g + 2) nj (pushS t y w) = X (g + 1) nj (jumpiS (pushS t y w) y ⟨0⟩ tail) :=
      candidate_run dtB (fun _ => by simp [H]) (mem_jumpi _) (ztB (fun h => absurd rfl h))
        (fun g => by rw [show C' (pushS t y w) .JUMPI = 10 from rfl,
          step_jumpi' g _ y ⟨0⟩ tail (by simp [pushS, tStack])])
    refine ⟨fB + 1, jumpiS (pushS s x w) x ⟨0⟩ tail, jumpiS (pushS t y w) y ⟨0⟩ tail, surplus, skipped,
      2, by omega, restB, ?_, ?_, fun g => by rw [show g + 1 + 2 = (g + 1) + 2 by omega, candA, candB]⟩
    · simp only [jumpiS, bne_zero, Bool.false_eq_true, if_false, pushS]
      rw [hs] at hA
      exact fall tail hA
    · refine ⟨?_, ?_, ?_, rel.maps⟩
      · have h := congrArg (fun z : State => ({ z with
          stack := tail
          pc := z.pc + UInt256.ofNat (w + 1) + ⟨1⟩ } : State)) rel.frame
        simpa [eraseCount, deployedFrame, eraseMaps, eraseCodeGas, jumpiS, pushS, bump, bne_zero] using h
      · simp only [jumpiS, pushS, bump]; have := rel.count; omega
      · simp only [jumpiS, pushS, bump]
        have t3' : 3 ≤ t.gasAvailable.toNat := by omega
        rw [sub _ 10 (by decide) (by rw [sub _ 3 (by decide) t3']; omega), sub _ 3 (by decide) t3',
          sub _ 10 (by decide) (by rw [sub _ 3 (by decide) gA]; omega), sub _ 3 (by decide) gA]
        omega
  · -- taken: the source runs the trampoline, the candidate jumps straight to y
    have validX : oj.contains x = true := by
      have zj := zB.jumpi
      simp only [pushS, hs, List.getElem?_cons_succ, List.getElem?_cons_zero, ne_eq,
        Option.some.injEq, true_and, hc, not_false_eq_true] at zj
      exact contains_of_notIn zj
    have pcB : (jumpiS (pushS s x w) x c tail).pc = x := by
      simp only [jumpiS, bne_of_ne hc, if_true]
    obtain ⟨zC, fC, nC, rfl, stepC, restC⟩ :=
      source_step (s := jumpiS (pushS s x w) x c tail)
        (by rw [pcB]; show decode s.executionEnv.code x = _; rw [sc]; exact t1)
        (fun _ => by simp [H]) (mem_jumpdest _) restB
    rw [show C' (jumpiS (pushS s x w) x c tail) .JUMPDEST = 1 from rfl, step_jumpdest'] at stepC
    injection stepC with hC
    subst hC
    have pcC : (bump (jumpiS (pushS s x w) x c tail) 1).incrPC.pc = x + UInt256.ofNat 1 := by
      simp only [EVM.State.incrPC, bump, pcB]
    have stC : (bump (jumpiS (pushS s x w) x c tail) 1).incrPC.stack = tail := rfl
    obtain ⟨zD, fD, nD, rfl, stepD, restD⟩ :=
      source_step (s := (bump (jumpiS (pushS s x w) x c tail) 1).incrPC)
        (by rw [pcC]; show decode s.executionEnv.code _ = _; rw [sc]; exact t2)
        (fun _ => by simp [H]) (mem_push _ _) restC
    rw [cost_push _ q nzq, step_push _ q y w' fD 3 nzq] at stepD
    injection stepD with hD
    subst hD
    obtain ⟨zE, fE, nE, rfl, stepE, restE⟩ :=
      source_step (op := .JUMP) (arg := none)
        (by
          show decode s.executionEnv.code ((bump (jumpiS (pushS s x w) x c tail) 1).incrPC.pc +
            UInt256.ofNat (w' + 1)) = _
          rw [pcC, sc]; exact t3)
        (fun _ => by simp [H]) (mem_jump' _) restD
    rw [show C' _ .JUMP = 8 from rfl, step_jump' fE _ y tail (by simp [stC])] at stepE
    injection stepE with hE
    subst hE
    have validY : oj.contains y = true := by
      have zj := zE.jump
      simp only [stC, List.getElem?_cons_zero, true_and] at zj
      exact contains_of_notIn zj
    have candB : ∀ g, X (g + 2) nj (pushS t y w) = X (g + 1) nj (jumpiS (pushS t y w) y c tail) :=
      candidate_run dtB (fun _ => by simp [H]) (mem_jumpi _) (ztB (fun _ => jumps y validY))
        (fun g => by rw [show C' (pushS t y w) .JUMPI = 10 from rfl,
          step_jumpi' g _ y c tail (by simp [pushS, tStack])])
    refine ⟨fE + 1, _, jumpiS (pushS t y w) y c tail, surplus + 12, skipped + 3, 2, by omega, restE,
      by rw [hs] at hA; simpa only [jumpS] using target c tail hA hc, ?_,
      fun g => by rw [show g + 1 + 2 = (g + 1) + 2 by omega, candA, candB]⟩
    -- gas spent: source 3+10+1+3+8 = 25, candidate 3+10 = 13
    have h1 : (s.gasAvailable - UInt256.ofNat 3).toNat = s.gasAvailable.toNat - 3 :=
      sub _ 3 (by decide) gA
    have h2 : (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 10).toNat = s.gasAvailable.toNat - 13 := by
      rw [sub _ 10 (by decide) (by omega), h1]; omega
    have gC := zC.cost
    rw [gasCut_zero (mem_jumpdest _), show C' _ .JUMPDEST = 1 from rfl] at gC
    change 1 ≤ (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 10).toNat at gC
    rw [h2] at gC
    have h3 : (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 10 - UInt256.ofNat 1).toNat =
        s.gasAvailable.toNat - 14 := by
      rw [sub _ 1 (by decide) (by omega), h2]; omega
    have gD := zD.cost
    rw [gasCut_zero (mem_push _ _), cost_push _ q nzq] at gD
    change 3 ≤ (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 10 - UInt256.ofNat 1).toNat at gD
    rw [h3] at gD
    have h4 : (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 10 - UInt256.ofNat 1 -
        UInt256.ofNat 3).toNat = s.gasAvailable.toNat - 17 := by
      rw [sub _ 3 (by decide) (by omega), h3]; omega
    have gE := zE.cost
    rw [gasCut_zero (mem_jump' _), show C' _ .JUMP = 8 from rfl] at gE
    change 8 ≤ (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 10 - UInt256.ofNat 1 -
      UInt256.ofNat 3).toNat at gE
    rw [h4] at gE
    have h5 : (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 10 - UInt256.ofNat 1 -
        UInt256.ofNat 3 - UInt256.ofNat 8).toNat = s.gasAvailable.toNat - 25 := by
      rw [sub _ 8 (by decide) (by omega), h4]; omega
    have t3' : 3 ≤ t.gasAvailable.toNat := by omega
    have k1 : (t.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 10).toNat = t.gasAvailable.toNat - 13 := by
      rw [sub _ 10 (by decide) (by rw [sub _ 3 (by decide) t3']; omega), sub _ 3 (by decide) t3']; omega
    refine ⟨?_, ?_, ?_, rel.maps⟩
    · have h := congrArg (fun z : State => ({ z with
        stack := tail
        pc := y } : State)) rel.frame
      simpa [eraseCount, deployedFrame, eraseMaps, eraseCodeGas, jumpiS, pushS, bump, jumpS,
        EVM.State.incrPC, bne_of_ne hc] using h
    · simp only [jumpS, bump, EVM.State.incrPC, jumpiS, pushS]; have := rel.count; omega
    · change (t.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 10).toNat =
        (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 10 - UInt256.ofNat 1 -
          UInt256.ofNat 3 - UInt256.ofNat 8).toNat + (surplus + 12)
      rw [k1, h5]; omega

#print axioms thread_segment

end GolfWhole
