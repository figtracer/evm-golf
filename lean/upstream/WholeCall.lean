import WholeTheta
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition GolfXiEntry

/-! Calls: the environment assumptions, gas accounting for a callee given extra gas, and
the call case of the whole-program certificate. -/
namespace GolfWhole

/-- The assumption on callees other than the owner's code: on related account maps and with
at least the original's gas, the candidate's call returns the same created set, substate,
status and output, related maps, no less gas than the original and no more than it was
given. The original's call keeps the owner's account. -/
def CalleeSummary (owner : AccountAddress) (old new : ByteArray) : Prop :=
  ∀ (fuel : ℕ) (bvh : List ByteArray) (created : Batteries.RBSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ τ τ₀ : AccountMap .EVM) (A : Substate)
    (s o r t : AccountAddress) (g gC p v v' : UInt256) (d : ByteArray) (depth : ℕ)
    (H : BlockHeader) (w : Bool) (cA : Batteries.RBSet AccountAddress compare)
    (σ' : AccountMap .EVM) (g' : UInt256) (A' : Substate) (z : Bool) (out : ByteArray),
    MapsRelated owner old new σ τ → MapsRelated owner old new σ₀ τ₀ →
    (∃ a, σ.find? owner = some a ∧ a.code = old) → (∃ a, τ.find? owner = some a ∧ a.code = new) →
    t ≠ owner → g.toNat ≤ gC.toNat →
    Θ fuel bvh created genesis blocks σ σ₀ A s o r (toExecute .EVM σ t) g p v v' d depth H w =
      .ok (cA, σ', g', A', z, out) →
    (∃ a, σ'.find? owner = some a ∧ a.code = old) ∧
    ∀ fuel', fuel ≤ fuel' → ∃ τ' g'',
      Θ fuel' bvh created genesis blocks τ τ₀ A s o r (toExecute .EVM τ t) gC p v v' d depth H w =
        .ok (cA, τ', g'', A', z, out) ∧
      MapsRelated owner old new σ' τ' ∧ g'.toNat ≤ g''.toNat ∧ g''.toNat ≤ gC.toNat

/-- Calls back into the owner's code do not halt exceptionally in the original run. -/
def Reentry (owner : AccountAddress) (old : ByteArray) : Prop :=
  ∀ (fuel : ℕ) (bvh : List ByteArray) (created : Batteries.RBSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (depth : ℕ) (H : BlockHeader) (w : Bool)
    (Q : Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate × Bool × ByteArray),
    (∃ a, σ.find? owner = some a ∧ a.code = old) →
    Θ (fuel + 1) bvh created genesis blocks σ σ₀ A s o owner (.Code old) g p v v' d depth H w = .ok Q →
    ∃ R, Ξ fuel created genesis blocks (transfer σ s owner v) σ₀ g A
      (thetaEnv bvh s o owner old p v' d depth H w) = .ok R

theorem theta_zero (bvh : List ByteArray) (created : Batteries.RBSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (c : ToExecute .EVM) (g p v v' : UInt256) (d : ByteArray) (depth : ℕ)
    (H : BlockHeader) (w : Bool) :
    Θ 0 bvh created genesis blocks σ σ₀ A s o r c g p v v' d depth H w = .error .OutOfFuel :=
  Θ.eq_1 bvh created genesis blocks σ σ₀ A s o r c g p v v' d depth H w

theorem linked_of_related {owner : AccountAddress} {old new : ByteArray} {σ τ : AccountMap .EVM}
    (rel : MapsRelated owner old new σ τ) (h : ∃ a, σ.find? owner = some a ∧ a.code = old) :
    ∃ a, τ.find? owner = some a ∧ a.code = new := by
  obtain ⟨a, ha, -⟩ := h
  rcases related_find rel owner with ⟨e, -⟩ | ⟨b, b', e, e', hb⟩
  · rw [ha] at e; cases e
  · obtain ⟨-, -, -, -, c⟩ := hb
    rw [if_pos rfl] at c
    exact ⟨b', e', c.2⟩

theorem toExecute_rel {owner : AccountAddress} {old new : ByteArray} {σ τ : AccountMap .EVM}
    (t : AccountAddress) (ht : t ≠ owner) (rel : MapsRelated owner old new σ τ) :
    toExecute .EVM σ t = toExecute .EVM τ t := by
  unfold toExecute
  split
  · rfl
  · simp only [Id.run]
    rcases related_find rel t with ⟨e, e'⟩ | ⟨a, a', e, e', h⟩
    · rw [e, e']
    · rw [e, e']
      obtain ⟨-, -, -, -, c⟩ := h
      rw [if_neg ht] at c
      show ToExecute.Code a.code = ToExecute.Code a'.code
      rw [c]

/-- One Θ call from related states: owner code by the certificate, other code by the
summary. -/
theorem theta_call {owner : AccountAddress} {old new : ByteArray}
    (summary : CalleeSummary owner old new) (reentry : Reentry owner old) (notPre : owner ∉ π)
    (N : ℕ) (cert : Cert owner old new N) (fuel : ℕ) (hN : fuel ≤ N) (bvh : List ByteArray)
    (created : Batteries.RBSet AccountAddress compare) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (σ σ₀ τ τ₀ : AccountMap .EVM) (A : Substate) (s o r t : AccountAddress)
    (hr : t = owner → r = owner) (g gC : UInt256) (e : ℕ) (hg : gC.toNat = g.toNat + e)
    (p v v' : UInt256) (d : ByteArray) (depth : ℕ) (H : BlockHeader) (w : Bool)
    (current : MapsRelated owner old new σ τ)
    (original : MapsRelated owner old new σ₀ τ₀)
    (oldCurrent : ∃ a, σ.find? owner = some a ∧ a.code = old)
    (oldOriginal : ∃ a, σ₀.find? owner = some a ∧ a.code = old)
    (newCurrent : ∃ a, τ.find? owner = some a ∧ a.code = new)
    (newOriginal : ∃ a, τ₀.find? owner = some a ∧ a.code = new)
    (cA : Batteries.RBSet AccountAddress compare) (σ' : AccountMap .EVM) (g' : UInt256)
    (A' : Substate) (z : Bool) (out : ByteArray)
    (run : Θ fuel bvh created genesis blocks σ σ₀ A s o r (toExecute .EVM σ t) g p v v' d depth H w =
      .ok (cA, σ', g', A', z, out)) :
    (∃ a, σ'.find? owner = some a ∧ a.code = old) ∧
    ∀ fuel', fuel ≤ fuel' → ∃ τ' g'',
      Θ fuel' bvh created genesis blocks τ τ₀ A s o r (toExecute .EVM τ t) gC p v v' d depth H w =
        .ok (cA, τ', g'', A', z, out) ∧
      MapsRelated owner old new σ' τ' ∧ (∃ a, τ'.find? owner = some a ∧ a.code = new) ∧
      g'.toNat ≤ g''.toNat ∧ g''.toNat ≤ gC.toNat := by
  by_cases ht : t = owner
  · have hr := hr ht
    rw [ht, hr, toExecute_owner σ owner old notPre oldCurrent] at run
    rw [ht, hr, toExecute_owner τ owner new notPre newCurrent]
    cases fuel with
    | zero => rw [theta_zero] at run; cases run
    | succ fuel =>
    obtain ⟨R, inner⟩ := reentry fuel bvh created genesis blocks σ σ₀ A s o g p v v' d depth H w _
      oldCurrent run
    obtain ⟨Q, runO, cand⟩ := theta_refines owner old new N cert fuel (by omega) bvh created genesis
      blocks σ σ₀ τ τ₀ A s o g gC e hg p v v' d depth H w current original oldCurrent oldOriginal
      newCurrent newOriginal R inner
    rw [runO] at run
    injection run with run
    subst run
    refine ⟨?_, fun fuel' hf => ?_⟩
    · obtain ⟨Q', -, -, -, lo, -, -, -, -, -⟩ := cand fuel (le_refl _)
      exact lo
    · cases fuel' with
      | zero => omega
      | succ fuel' =>
      obtain ⟨Q', runN, ec, hm, lo, ln, hg, cap, eA, ez⟩ := cand fuel' (by omega)
      obtain ⟨cA', τ', g'', A'', z', out'⟩ := Q'
      simp only at ec hm lo ln hg cap eA ez
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj ez
      subst ec eA
      exact ⟨τ', g'', runN, hm, ln, hg, cap⟩
  · obtain ⟨lo, cand⟩ := summary fuel bvh created genesis blocks σ σ₀ τ τ₀ A s o r t g gC p v v' d
      depth H w cA σ' g' A' z out current original oldCurrent newCurrent ht (by omega) run
    refine ⟨lo, fun fuel' hf => ?_⟩
    obtain ⟨τ', g'', runN, hm, hg, cap⟩ := cand fuel' hf
    exact ⟨τ', g'', runN, hm, linked_of_related hm lo, hg, cap⟩

/-! Gas forwarded to a callee that has extra gas. -/

theorem L_mono (a s : ℕ) : L a ≤ L (a + s) ∧ L (a + s) ≤ L a + s := by
  unfold L; omega

theorem gascap_le (a s g d : ℕ) (hd : d ≤ s) :
    min (L a) g ≤ min (L (a + s)) (g + d) ∧ min (L (a + s)) (g + d) ≤ min (L a) g + s := by
  have := L_mono a s
  omega

theorem dead_rel {owner : AccountAddress} {old new : ByteArray} {σ τ : AccountMap .EVM}
    (rel : MapsRelated owner old new σ τ) (ho : 0 < old.size) (hn : 0 < new.size) (t : AccountAddress) :
    EvmYul.State.dead σ t = EvmYul.State.dead τ t := by
  unfold EvmYul.State.dead
  rcases related_find rel t with ⟨e, e'⟩ | ⟨a, a', e, e', h⟩
  · rw [e, e']
  · rw [e, e']
    obtain ⟨n, b, -, -, c⟩ := h
    simp only [Option.option, Account.emptyAccount, n, b]
    split at c
    · obtain ⟨c1, c2⟩ := c
      have h1 : a.code.isEmpty = false := by
        rw [c1]; simp only [ByteArray.isEmpty]; exact decide_eq_false (by omega)
      have h2 : a'.code.isEmpty = false := by
        rw [c2]; simp only [ByteArray.isEmpty]; exact decide_eq_false (by omega)
      rw [h1, h2]
    · rw [c]

theorem cextra_rel {owner : AccountAddress} {old new : ByteArray} {σ τ : AccountMap .EVM}
    (rel : MapsRelated owner old new σ τ) (ho : 0 < old.size) (hn : 0 < new.size)
    (t r : AccountAddress) (v : UInt256) (A : Substate) :
    Cextra t r v σ A = Cextra t r v τ A := by
  simp only [Cextra, Cnew, dead_rel rel ho hn r]

theorem balance_rel {owner : AccountAddress} {old new : ByteArray} {σ τ : AccountMap .EVM}
    (rel : MapsRelated owner old new σ τ) (k : AccountAddress) :
    (σ.find? k).map (fun a => a.balance) = (τ.find? k).map (fun a => a.balance) := by
  rcases related_find rel k with ⟨e, e'⟩ | ⟨a, a', e, e', h⟩
  · rw [e, e']
  · rw [e, e']
    obtain ⟨-, b, -, -, -⟩ := h
    simp only [Option.map, b]

theorem ccallgas_zero (t r : AccountAddress) (g : UInt256) (σ : AccountMap .EVM) (μ : MachineState)
    (A : Substate) : Ccallgas t r ⟨0⟩ g σ μ A = Cgascap t r ⟨0⟩ g σ μ A := rfl

theorem ccallgas_pos (t r : AccountAddress) (v g : UInt256) (σ : AccountMap .EVM) (μ : MachineState)
    (A : Substate) (hv : v ≠ ⟨0⟩) :
    Ccallgas t r v g σ μ A = Cgascap t r v g σ μ A + GasConstants.Gcallstipend := by
  unfold Ccallgas
  obtain ⟨⟨n, hn⟩⟩ := v
  cases n with
  | zero => exact absurd rfl hv
  | succ n => rfl

theorem cxfer_pos (v : UInt256) (hv : v ≠ ⟨0⟩) : Cxfer v = GasConstants.Gcallvalue := by
  unfold Cxfer
  obtain ⟨⟨n, hn⟩⟩ := v
  cases n with
  | zero => exact absurd rfl hv
  | succ n => rfl

/-- The candidate's call costs at most `surplus` more, and hands the callee exactly that
much more gas; the gas handed over never exceeds the cost. -/
theorem ccall_rel (t r : AccountAddress) (v gas gas' : UInt256) (σ τ : AccountMap .EVM)
    (μ μ' : MachineState) (A : Substate) (surplus d : ℕ)
    (hx : Cextra t r v σ A = Cextra t r v τ A)
    (hμ : μ'.gasAvailable.toNat = μ.gasAvailable.toNat + surplus)
    (hd : gas'.toNat = gas.toNat + d) (hds : d ≤ surplus)
    (enough : Ccall t r v gas σ μ A ≤ μ.gasAvailable.toNat) :
    Ccall t r v gas σ μ A ≤ Ccall t r v gas' τ μ' A ∧
    Ccall t r v gas' τ μ' A ≤ Ccall t r v gas σ μ A + surplus ∧
    Ccallgas t r v gas' τ μ' A + Ccall t r v gas σ μ A =
      Ccallgas t r v gas σ μ A + Ccall t r v gas' τ μ' A ∧
    Ccallgas t r v gas σ μ A ≤ Ccall t r v gas σ μ A ∧
    Ccallgas t r v gas' τ μ' A ≤ Ccall t r v gas' τ μ' A := by
  have ex : Cxfer v ≤ Cextra t r v τ A := by unfold Cextra; omega
  have stip : Ccallgas t r v gas σ μ A = Cgascap t r v gas σ μ A + (if v = ⟨0⟩ then 0 else GasConstants.Gcallstipend) ∧
      Ccallgas t r v gas' τ μ' A = Cgascap t r v gas' τ μ' A + (if v = ⟨0⟩ then 0 else GasConstants.Gcallstipend) ∧
      (if v = ⟨0⟩ then 0 else GasConstants.Gcallstipend) ≤ Cxfer v := by
    by_cases hv : v = ⟨0⟩
    · subst hv; simp only [if_true, ccallgas_zero, Nat.add_zero, Nat.zero_le, and_self]
    · simp only [if_neg hv, ccallgas_pos _ _ _ _ _ _ _ hv, cxfer_pos v hv, true_and]; decide
  obtain ⟨s1, s2, s3⟩ := stip
  have e1 : Ccall t r v gas σ μ A = Cgascap t r v gas σ μ A + Cextra t r v σ A := rfl
  have e2 : Ccall t r v gas' τ μ' A = Cgascap t r v gas' τ μ' A + Cextra t r v τ A := rfl
  have hX : Cextra t r v σ A ≤ μ.gasAvailable.toNat := by rw [e1] at enough; omega
  have g1 : Cgascap t r v gas σ μ A = min (L (μ.gasAvailable.toNat - Cextra t r v σ A)) gas.toNat := by
    unfold Cgascap; rw [if_pos hX]
  have g2 : Cgascap t r v gas' τ μ' A =
      min (L (μ.gasAvailable.toNat - Cextra t r v σ A + surplus)) (gas.toNat + d) := by
    unfold Cgascap
    rw [if_pos (by rw [← hx]; omega), ← hx, hd,
      show μ'.gasAvailable.toNat - Cextra t r v σ A = μ.gasAvailable.toNat - Cextra t r v σ A + surplus by omega]
  have cap := gascap_le (μ.gasAvailable.toNat - Cextra t r v σ A) surplus gas.toNat d hds
  rw [s1, s2, e1, e2, g1, g2, ← hx]
  rw [e1, g1] at enough
  omega

/-! The CALL and STATICCALL steps. -/

theorem step_call_of (f c : ℕ) (arg : Option (UInt256 × Nat)) (u : State)
    (stack : Stack UInt256) (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ x : UInt256) (state' : State)
    (h : u.stack.pop7 = some (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆))
    (hc : call f c u.executionEnv.blobVersionedHashes μ₀ (.ofNat u.executionEnv.codeOwner) μ₁ μ₁
      μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ u.executionEnv.perm { u with execLength := u.execLength + 1 } = .ok (x, state')) :
    EVM.step (f + 1) c (some (.CALL, arg)) u = .ok (state'.replaceStackAndIncrPC (stack.push x)) := by
  unfold EVM.step
  simp only [h, hc, bind, Except.bind, pure, Except.pure, liftM, monadLift, MonadLiftT.monadLift,
    MonadLift.monadLift, instMonadLiftOptionExceptExecutionException, Option.option]

theorem step_call_inv (f c : ℕ) (arg : Option (UInt256 × Nat)) (u v : State)
    (step : EVM.step (f + 1) c (some (.CALL, arg)) u = .ok v) :
    ∃ stack μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ x state', u.stack.pop7 = some (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) ∧
      call f c u.executionEnv.blobVersionedHashes μ₀ (.ofNat u.executionEnv.codeOwner) μ₁ μ₁
        μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ u.executionEnv.perm { u with execLength := u.execLength + 1 } = .ok (x, state') ∧
      v = state'.replaceStackAndIncrPC (stack.push x) := by
  unfold EVM.step at step
  cases h : u.stack.pop7 with
  | none =>
    simp only [h, bind, Except.bind, pure, Except.pure, liftM, monadLift, MonadLiftT.monadLift,
      MonadLift.monadLift, instMonadLiftOptionExceptExecutionException, Option.option] at step
    cases step
  | some p =>
    obtain ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩ := p
    simp only [h, bind, Except.bind, pure, Except.pure, liftM, monadLift, MonadLiftT.monadLift,
      MonadLift.monadLift, instMonadLiftOptionExceptExecutionException, Option.option] at step
    cases hc : call f c u.executionEnv.blobVersionedHashes μ₀ (.ofNat u.executionEnv.codeOwner) μ₁ μ₁
        μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ u.executionEnv.perm { u with execLength := u.execLength + 1 } with
    | error e => rw [hc] at step; cases step
    | ok w =>
      obtain ⟨x, state'⟩ := w
      rw [hc] at step
      injection step with step
      exact ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆, x, state', rfl, hc, step.symm⟩

theorem step_staticcall_of (f c : ℕ) (arg : Option (UInt256 × Nat)) (u : State)
    (stack : Stack UInt256) (μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ x : UInt256) (state' : State)
    (h : u.stack.pop6 = some (stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆))
    (hc : call f c u.executionEnv.blobVersionedHashes μ₀ (.ofNat u.executionEnv.codeOwner) μ₁ μ₁
      ⟨0⟩ ⟨0⟩ μ₃ μ₄ μ₅ μ₆ false { u with execLength := u.execLength + 1 } = .ok (x, state')) :
    EVM.step (f + 1) c (some (.STATICCALL, arg)) u = .ok (state'.replaceStackAndIncrPC (stack.push x)) := by
  unfold EVM.step
  simp only [h, hc, bind, Except.bind, pure, Except.pure, liftM, monadLift, MonadLiftT.monadLift,
    MonadLift.monadLift, instMonadLiftOptionExceptExecutionException, Option.option]

theorem step_staticcall_inv (f c : ℕ) (arg : Option (UInt256 × Nat)) (u v : State)
    (step : EVM.step (f + 1) c (some (.STATICCALL, arg)) u = .ok v) :
    ∃ stack μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ x state', u.stack.pop6 = some (stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆) ∧
      call f c u.executionEnv.blobVersionedHashes μ₀ (.ofNat u.executionEnv.codeOwner) μ₁ μ₁
        ⟨0⟩ ⟨0⟩ μ₃ μ₄ μ₅ μ₆ false { u with execLength := u.execLength + 1 } = .ok (x, state') ∧
      v = state'.replaceStackAndIncrPC (stack.push x) := by
  unfold EVM.step at step
  cases h : u.stack.pop6 with
  | none =>
    simp only [h, bind, Except.bind, pure, Except.pure, liftM, monadLift, MonadLiftT.monadLift,
      MonadLift.monadLift, instMonadLiftOptionExceptExecutionException, Option.option] at step
    cases step
  | some p =>
    obtain ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩ := p
    simp only [h, bind, Except.bind, pure, Except.pure, liftM, monadLift, MonadLiftT.monadLift,
      MonadLift.monadLift, instMonadLiftOptionExceptExecutionException, Option.option] at step
    cases hc : call f c u.executionEnv.blobVersionedHashes μ₀ (.ofNat u.executionEnv.codeOwner) μ₁ μ₁
        ⟨0⟩ ⟨0⟩ μ₃ μ₄ μ₅ μ₆ false { u with execLength := u.execLength + 1 } with
    | error e => rw [hc] at step; cases step
    | ok w =>
      obtain ⟨x, state'⟩ := w
      rw [hc] at step
      injection step with step
      exact ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆, x, state', rfl, hc, step.symm⟩

theorem step_callcode_of (f c : ℕ) (arg : Option (UInt256 × Nat)) (u : State)
    (stack : Stack UInt256) (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ x : UInt256) (state' : State)
    (h : u.stack.pop7 = some (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆))
    (hc : call f c u.executionEnv.blobVersionedHashes μ₀ (.ofNat u.executionEnv.codeOwner)
      (.ofNat u.executionEnv.codeOwner) μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ u.executionEnv.perm
      { u with execLength := u.execLength + 1 } = .ok (x, state')) :
    EVM.step (f + 1) c (some (.CALLCODE, arg)) u = .ok (state'.replaceStackAndIncrPC (stack.push x)) := by
  unfold EVM.step
  simp only [h, hc, bind, Except.bind, pure, Except.pure, liftM, monadLift, MonadLiftT.monadLift,
    MonadLift.monadLift, instMonadLiftOptionExceptExecutionException, Option.option]

theorem step_callcode_inv (f c : ℕ) (arg : Option (UInt256 × Nat)) (u v : State)
    (step : EVM.step (f + 1) c (some (.CALLCODE, arg)) u = .ok v) :
    ∃ stack μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ x state', u.stack.pop7 = some (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) ∧
      call f c u.executionEnv.blobVersionedHashes μ₀ (.ofNat u.executionEnv.codeOwner)
        (.ofNat u.executionEnv.codeOwner) μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ u.executionEnv.perm
        { u with execLength := u.execLength + 1 } = .ok (x, state') ∧
      v = state'.replaceStackAndIncrPC (stack.push x) := by
  unfold EVM.step at step
  cases h : u.stack.pop7 with
  | none =>
    simp only [h, bind, Except.bind, pure, Except.pure, liftM, monadLift, MonadLiftT.monadLift,
      MonadLift.monadLift, instMonadLiftOptionExceptExecutionException, Option.option] at step
    cases step
  | some p =>
    obtain ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩ := p
    simp only [h, bind, Except.bind, pure, Except.pure, liftM, monadLift, MonadLiftT.monadLift,
      MonadLift.monadLift, instMonadLiftOptionExceptExecutionException, Option.option] at step
    cases hc : call f c u.executionEnv.blobVersionedHashes μ₀ (.ofNat u.executionEnv.codeOwner)
        (.ofNat u.executionEnv.codeOwner) μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ u.executionEnv.perm
        { u with execLength := u.execLength + 1 } with
    | error e => rw [hc] at step; cases step
    | ok w =>
      obtain ⟨x, state'⟩ := w
      rw [hc] at step
      injection step with step
      exact ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆, x, state', rfl, hc, step.symm⟩

theorem step_delegatecall_of (f c : ℕ) (arg : Option (UInt256 × Nat)) (u : State)
    (stack : Stack UInt256) (μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ x : UInt256) (state' : State)
    (h : u.stack.pop6 = some (stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆))
    (hc : call f c u.executionEnv.blobVersionedHashes μ₀ (.ofNat u.executionEnv.source)
      (.ofNat u.executionEnv.codeOwner) μ₁ ⟨0⟩ u.executionEnv.weiValue μ₃ μ₄ μ₅ μ₆ u.executionEnv.perm
      { u with execLength := u.execLength + 1 } = .ok (x, state')) :
    EVM.step (f + 1) c (some (.DELEGATECALL, arg)) u = .ok (state'.replaceStackAndIncrPC (stack.push x)) := by
  unfold EVM.step
  simp only [h, hc, bind, Except.bind, pure, Except.pure, liftM, monadLift, MonadLiftT.monadLift,
    MonadLift.monadLift, instMonadLiftOptionExceptExecutionException, Option.option]

theorem step_delegatecall_inv (f c : ℕ) (arg : Option (UInt256 × Nat)) (u v : State)
    (step : EVM.step (f + 1) c (some (.DELEGATECALL, arg)) u = .ok v) :
    ∃ stack μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ x state', u.stack.pop6 = some (stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆) ∧
      call f c u.executionEnv.blobVersionedHashes μ₀ (.ofNat u.executionEnv.source)
        (.ofNat u.executionEnv.codeOwner) μ₁ ⟨0⟩ u.executionEnv.weiValue μ₃ μ₄ μ₅ μ₆ u.executionEnv.perm
        { u with execLength := u.execLength + 1 } = .ok (x, state') ∧
      v = state'.replaceStackAndIncrPC (stack.push x) := by
  unfold EVM.step at step
  cases h : u.stack.pop6 with
  | none =>
    simp only [h, bind, Except.bind, pure, Except.pure, liftM, monadLift, MonadLiftT.monadLift,
      MonadLift.monadLift, instMonadLiftOptionExceptExecutionException, Option.option] at step
    cases step
  | some p =>
    obtain ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩ := p
    simp only [h, bind, Except.bind, pure, Except.pure, liftM, monadLift, MonadLiftT.monadLift,
      MonadLift.monadLift, instMonadLiftOptionExceptExecutionException, Option.option] at step
    cases hc : call f c u.executionEnv.blobVersionedHashes μ₀ (.ofNat u.executionEnv.source)
        (.ofNat u.executionEnv.codeOwner) μ₁ ⟨0⟩ u.executionEnv.weiValue μ₃ μ₄ μ₅ μ₆ u.executionEnv.perm
        { u with execLength := u.execLength + 1 } with
    | error e => rw [hc] at step; cases step
    | ok w =>
      obtain ⟨x, state'⟩ := w
      rw [hc] at step
      injection step with step
      exact ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆, x, state', rfl, hc, step.symm⟩

theorem ofNat_toNat (n : ℕ) (h : n < UInt256.size) : (UInt256.ofNat n).toNat = n := by
  show (Fin.ofNat UInt256.size n).val = n
  simp only [Fin.ofNat, Nat.mod_eq_of_lt h]

/-- An address pushed as a word and read back. -/
theorem ofUInt256_ofNat (a : AccountAddress) : AccountAddress.ofUInt256 (UInt256.ofNat a.val) = a := by
  have lt : a.val < UInt256.size := lt_trans a.isLt (by decide)
  have e : (UInt256.ofNat a.val).toNat = a.val := ofNat_toNat a.val lt
  unfold AccountAddress.ofUInt256
  apply Fin.ext
  show ((UInt256.ofNat a.val).toNat % AccountAddress.size) % AccountAddress.size = a.val
  rw [e, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt a.isLt]

/-! The body of `call`. -/

/-- The gas handed to the callee, as `call` computes it for code at `t` and recipient `rcp`. -/
def callGas (t rcp v gas : UInt256) (u : State) : ℕ :=
  Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 rcp) v gas u.accountMap
    u.toMachineState u.substate

/-- The callee run of `call`: Θ on the code at `t` for recipient `rcp`, or the no-call result. -/
def callRun (f : ℕ) (bvh : List ByteArray) (gas src rcp t v v' io is : UInt256) (perm : Bool)
    (u : State) :
    Except EVM.ExecutionException
      (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate × Bool × ByteArray) :=
  if v ≤ (u.accountMap.find? u.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
      u.executionEnv.depth < 1024 then
    Θ f bvh u.createdAccounts u.genesisBlockHeader u.blocks u.accountMap u.σ₀
      (u.addAccessedAccount (AccountAddress.ofUInt256 t)).substate (AccountAddress.ofUInt256 src)
      u.executionEnv.sender (AccountAddress.ofUInt256 rcp) (toExecute .EVM u.accountMap (AccountAddress.ofUInt256 t))
      (.ofNat (callGas t rcp v gas u)) (.ofNat u.executionEnv.gasPrice) v v'
      (u.memory.readWithPadding io.toNat is.toNat) (u.executionEnv.depth + 1) u.executionEnv.header perm
  else
    .ok (u.createdAccounts, u.accountMap, .ofNat (callGas t rcp v gas u),
      (u.addAccessedAccount (AccountAddress.ofUInt256 t)).substate, false, .empty)

/-- The status word `call` pushes. -/
def callStatus (u : State) (v : UInt256) (z : Bool) : UInt256 :=
  if (!z) || decide (v > (u.accountMap.find? u.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))) ||
      (u.executionEnv.depth == 1024) then ⟨0⟩ else ⟨1⟩

/-- The caller's state after `call`, before the stack push. -/
def callPost (u : State) (gasCost : ℕ) (io is oo os : UInt256)
    (q : Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate × Bool × ByteArray) :
    State :=
  let u₁ : State := { u with gasAvailable := u.gasAvailable - .ofNat gasCost }
  let o := q.2.2.2.2.2
  let n : UInt256 := min os (.ofNat o.size)
  let μ := writeBytes o 0 u₁.toMachineState oo.toNat n.toNat
  { u₁ with
    accountMap := q.2.1, substate := q.2.2.2.1, createdAccounts := q.1,
    toMachineState := { μ with
      returnData := o
      gasAvailable := μ.gasAvailable + q.2.2.1
      activeWords := .ofNat (MachineState.M (MachineState.M u₁.activeWords.toNat io.toNat is.toNat)
        oo.toNat os.toNat) } }

theorem call_inv {f gasCost : ℕ} {bvh : List ByteArray} {gas src rcp t v v' io is oo os : UInt256}
    {perm : Bool} {u : State} {x : UInt256} {r : State}
    (h : call (f + 1) gasCost bvh gas src rcp t v v' io is oo os perm u = .ok (x, r)) :
    ∃ q, callRun f bvh gas src rcp t v v' io is perm u = .ok q ∧ x = callStatus u v q.2.2.2.2.1 ∧
      r = callPost u gasCost io is oo os q := by
  unfold call at h
  unfold callRun
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h <;> rename_i hc
  · rw [if_pos hc]
    split at h <;> rename_i q hΘ
    · cases h
    · obtain ⟨cA, σ', g', A', z, o⟩ := q
      injection h with h
      injection h with hx hr
      exact ⟨_, hΘ, hx.symm, hr.symm⟩
  · rw [if_neg hc]
    injection h with h
    injection h with hx hr
    exact ⟨_, rfl, hx.symm, hr.symm⟩

theorem call_of {f gasCost : ℕ} {bvh : List ByteArray} {gas src rcp t v v' io is oo os : UInt256}
    {perm : Bool} {u : State}
    {q : Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate × Bool × ByteArray}
    (h : callRun f bvh gas src rcp t v v' io is perm u = .ok q) :
    call (f + 1) gasCost bvh gas src rcp t v v' io is oo os perm u =
      .ok (callStatus u v q.2.2.2.2.1, callPost u gasCost io is oo os q) := by
  unfold call
  unfold callRun at h
  simp only [bind, Except.bind, pure, Except.pure]
  split <;> rename_i hc
  · rw [if_pos hc] at h
    split <;> rename_i q' hΘ
    · exact absurd (h.symm.trans hΘ) (by simp)
    · have e := h.symm.trans hΘ
      injection e with e
      subst e
      obtain ⟨cA, σ', g', A', z, o⟩ := q
      rfl
  · rw [if_neg hc] at h
    injection h with h
    subst h
    rfl

theorem step_zero (c : ℕ) (i : Option (Operation .EVM × Option (UInt256 × Nat))) (u : State) :
    EVM.step 0 c i u = .error .OutOfFuel := rfl

theorem call_zero (gasCost : ℕ) (bvh : List ByteArray) (gas src rcp t v v' io is oo os : UInt256)
    (perm : Bool) (u : State) :
    call 0 gasCost bvh gas src rcp t v v' io is oo os perm u = .error .OutOfFuel := rfl

/-- Frames after `call` do not see the cost, the callee's maps or its remaining gas. -/
theorem callPost_erased (u : State) (c c' : ℕ) (io is oo os : UInt256)
    (cA : Batteries.RBSet AccountAddress compare) (σ' σ'' : AccountMap .EVM) (g' g'' : UInt256)
    (A' : Substate) (z : Bool) (out : ByteArray) :
    E (callPost u c io is oo os (cA, σ', g', A', z, out)) =
      E (callPost u c' io is oo os (cA, σ'', g'', A', z, out)) := by
  simp only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas, callPost, writeBytes]

/-- Frames after `call` depend only on the frame before it. -/
theorem callPost_frame (u : State) (c : ℕ) (io is oo os : UInt256)
    (q : Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate × Bool × ByteArray) :
    E (callPost u c io is oo os q) = E (callPost (E u) c io is oo os q) := by
  simp only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas, callPost, writeBytes]

theorem cost_call (u : State) (g₀ a₁ a₂ : UInt256) (rest : List UInt256)
    (hs : u.stack = g₀ :: a₁ :: a₂ :: rest) :
    C' u .CALL = Ccall (AccountAddress.ofUInt256 a₁) (AccountAddress.ofUInt256 a₁) a₂ g₀ u.accountMap
      u.toMachineState u.substate := by
  simp only [C', hs]
  rfl

theorem cost_staticcall (u : State) (g₀ a₁ : UInt256) (rest : List UInt256) (hs : u.stack = g₀ :: a₁ :: rest) :
    C' u .STATICCALL = Ccall (AccountAddress.ofUInt256 a₁) (AccountAddress.ofUInt256 a₁) ⟨0⟩ g₀ u.accountMap
      u.toMachineState u.substate := by
  simp only [C', hs]
  rfl

theorem cost_callcode (u : State) (g₀ a₁ a₂ : UInt256) (rest : List UInt256)
    (hs : u.stack = g₀ :: a₁ :: a₂ :: rest) :
    C' u .CALLCODE = Ccall (AccountAddress.ofUInt256 a₁) u.executionEnv.codeOwner a₂ g₀ u.accountMap
      u.toMachineState u.substate := by
  simp only [C', hs]
  rfl

theorem cost_delegatecall (u : State) (g₀ a₁ : UInt256) (rest : List UInt256)
    (hs : u.stack = g₀ :: a₁ :: rest) :
    C' u .DELEGATECALL = Ccall (AccountAddress.ofUInt256 a₁) u.executionEnv.codeOwner ⟨0⟩ g₀ u.accountMap
      u.toMachineState u.substate := by
  simp only [C', hs]
  rfl

theorem mem_call_eq {op : Operation .EVM} {k : ℕ} (hop : CallOp op k) (a b : State) (x y : UInt256)
    (rest : List UInt256) (ha : a.stack = x :: rest) (hb : b.stack = y :: rest)
    (hw : a.activeWords = b.activeWords) : memoryExpansionCost a op = memoryExpansionCost b op := by
  cases hop <;> simp [memoryExpansionCost, memoryExpansionCost.μᵢ', ha, hb, hw]

theorem pop7_eq {st stk : List UInt256} {a b c d e f g : UInt256}
    (h : Stack.pop7 st = some (stk, a, b, c, d, e, f, g)) : st = [a, b, c, d, e, f, g] ++ stk := by
  match st, h with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h =>
    simp only [Stack.pop7, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; rfl

theorem pop6_eq {st stk : List UInt256} {a b c d e g : UInt256}
    (h : Stack.pop6 st = some (stk, a, b, c, d, e, g)) : st = [a, b, c, d, e, g] ++ stk := by
  match st, h with
  | _ :: _ :: _ :: _ :: _ :: _ :: _, h =>
    simp only [Stack.pop6, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; rfl

theorem rel_count {owner : AccountAddress} {old new : ByteArray} {surplus skipped : ℕ} {u u' : State}
    (h : DeployedOffset owner old new surplus skipped u u') :
    DeployedOffset owner old new surplus skipped { u with execLength := u.execLength + 1 }
      { u' with execLength := u'.execLength + 1 } := by
  refine ⟨?_, ?_, h.gas, h.maps⟩
  · have hh := congrArg (fun x : State => { x with execLength := 0 }) h.frame
    simpa [eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using hh
  · change u.execLength + 1 = (u'.execLength + 1) + skipped
    have := h.count; omega

/-- One `call` from related callers whose gas arguments differ by `d ≤ surplus`. The candidate
pushes the same status and reaches a related state for every fuel at least the original's. -/
theorem call_rel {owner : AccountAddress} {old new : ByteArray}
    (summary : CalleeSummary owner old new) (reentry : Reentry owner old) (notPre : owner ∉ π)
    (N : ℕ) (cert : Cert owner old new N) (ho : 0 < old.size) (hn : 0 < new.size)
    (f : ℕ) (hN : f ≤ N) (bvh : List ByteArray) (gas gas' src rcp t v v' io is oo os : UInt256)
    (perm : Bool) (u u' : State) (surplus skipped d gasCost gasCost' : ℕ) (x : UInt256) (r : State)
    (rel : DeployedOffset owner old new surplus skipped u { u' with stack := u.stack })
    (hr : AccountAddress.ofUInt256 t = owner → AccountAddress.ofUInt256 rcp = owner)
    (hd : gas'.toNat = gas.toNat + d) (hds : d ≤ surplus)
    (hc : gasCost = Ccall (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 rcp) v gas u.accountMap
      u.toMachineState u.substate)
    (hc' : gasCost' = Ccall (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 rcp) v gas' u'.accountMap
      u'.toMachineState u'.substate)
    (enough : gasCost ≤ u.gasAvailable.toNat)
    (run : call (f + 1) gasCost bvh gas src rcp t v v' io is oo os perm u = .ok (x, r)) :
    (x = ⟨0⟩ ∨ x = ⟨1⟩) ∧ gasCost' ≤ gasCost + surplus ∧ r.stack = u.stack ∧ r.pc = u.pc ∧
    ∀ f', f ≤ f' → ∃ r' surplus',
      call (f' + 1) gasCost' bvh gas' src rcp t v v' io is oo os perm u' = .ok (x, r') ∧
      DeployedOffset owner old new surplus' skipped r { r' with stack := r.stack } ∧
      r'.gasAvailable.toNat ≤ u'.gasAvailable.toNat ∧ r'.stack = u'.stack ∧ r'.pc = u'.pc := by
  obtain ⟨q, hq, hx, hr⟩ := call_inv run
  obtain ⟨cA, σ', g', A', z, out⟩ := q
  simp only at hx hr
  subst hx hr
  have ownU : u.executionEnv.codeOwner = owner := rel.maps.2.2.1.1
  have ownU' : u'.executionEnv.codeOwner = owner := rel.maps.2.2.2.1
  have maps : MapsRelated owner old new u.accountMap u'.accountMap := rel.maps.1
  have maps0 : MapsRelated owner old new u.σ₀ u'.σ₀ := rel.maps.2.1
  have lo : ∃ a, u.accountMap.find? owner = some a ∧ a.code = old := rel.maps.2.2.1.2.2.1
  have lo0 : ∃ a, u.σ₀.find? owner = some a ∧ a.code = old := rel.maps.2.2.1.2.2.2
  have ln : ∃ a, u'.accountMap.find? owner = some a ∧ a.code = new := rel.maps.2.2.2.2.2.1
  have ln0 : ∃ a, u'.σ₀.find? owner = some a ∧ a.code = new := rel.maps.2.2.2.2.2.2
  have codeU : u.executionEnv.code = old := rel.maps.2.2.1.2.1
  have codeU' : u'.executionEnv.code = new := rel.maps.2.2.2.2.1
  have gasU : u'.gasAvailable.toNat = u.gasAvailable.toNat + surplus := rel.gas
  have F : E u = E { u' with stack := u.stack } := rel.frame
  have sub : u.substate = u'.substate := by
    simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
      congrArg (fun x : State => x.substate) F
  have cr : u.createdAccounts = u'.createdAccounts := by
    simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
      congrArg (fun x : State => x.createdAccounts) F
  have gen : u.genesisBlockHeader = u'.genesisBlockHeader := by
    simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
      congrArg (fun x : State => x.genesisBlockHeader) F
  have bl : u.blocks = u'.blocks := by
    simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
      congrArg (fun x : State => x.blocks) F
  have snd : u.executionEnv.sender = u'.executionEnv.sender := by
    simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
      congrArg (fun x : State => x.executionEnv.sender) F
  have gp : u.executionEnv.gasPrice = u'.executionEnv.gasPrice := by
    simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
      congrArg (fun x : State => x.executionEnv.gasPrice) F
  have dep : u.executionEnv.depth = u'.executionEnv.depth := by
    simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
      congrArg (fun x : State => x.executionEnv.depth) F
  have hdr : u.executionEnv.header = u'.executionEnv.header := by
    simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
      congrArg (fun x : State => x.executionEnv.header) F
  have mem : u.memory = u'.memory := by
    simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
      congrArg (fun x : State => x.memory) F
  rw [← sub] at hc'
  have cx := cextra_rel maps ho hn (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 rcp) v u.substate
  obtain ⟨c1, c2, c3, c4, c5⟩ := ccall_rel (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 rcp) v gas gas'
    u.accountMap u'.accountMap u.toMachineState u'.toMachineState u.substate surplus d cx gasU hd hds
    (hc ▸ enough)
  rw [← hc, ← hc'] at c1 c2 c3
  rw [← hc] at c4
  rw [← hc'] at c5
  have cg : callGas t rcp v gas u = Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 rcp) v gas
      u.accountMap u.toMachineState u.substate := rfl
  have cg' : callGas t rcp v gas' u' = Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 rcp)
      v gas' u'.accountMap u'.toMachineState u.substate := by unfold callGas; rw [sub]
  rw [← cg] at c3 c4
  rw [← cg'] at c3 c5
  have bound : u.gasAvailable.toNat < UInt256.size := u.gasAvailable.val.isLt
  have bound' : u'.gasAvailable.toNat < UInt256.size := u'.gasAvailable.val.isLt
  have hgC : (UInt256.ofNat (callGas t rcp v gas' u')).toNat =
      (UInt256.ofNat (callGas t rcp v gas u)).toNat + (gasCost' - gasCost) := by
    rw [ofNat_toNat _ (by omega), ofNat_toNat _ (by omega)]; omega
  have bal := balance_rel maps owner
  have status : callStatus u' v z = callStatus u v z := by
    unfold callStatus
    rw [ownU, ownU', ← dep]
    rcases related_find maps owner with ⟨e, e'⟩ | ⟨a, a', e, e', h⟩
    · rw [e, e']
    · rw [e, e']
      obtain ⟨-, b, -, -, -⟩ := h
      simp only [Option.elim, b]
  have xs : callStatus u v z = ⟨0⟩ ∨ callStatus u v z = ⟨1⟩ := by
    unfold callStatus; split <;> simp
  have cond : (v ≤ (u.accountMap.find? u.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
      u.executionEnv.depth < 1024) ↔
      (v ≤ (u'.accountMap.find? u'.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
      u'.executionEnv.depth < 1024) := by
    rw [ownU, ownU', ← dep]
    rcases related_find maps owner with ⟨e, e'⟩ | ⟨a, a', e, e', h⟩
    · rw [e, e']
    · rw [e, e']
      obtain ⟨-, b, -, -, -⟩ := h
      simp only [Option.option, b]
  have key : (∃ a, σ'.find? owner = some a ∧ a.code = old) ∧ ∀ f', f ≤ f' → ∃ τ' g'',
      callRun f' bvh gas' src rcp t v v' io is perm u' = .ok (cA, τ', g'', A', z, out) ∧
      MapsRelated owner old new σ' τ' ∧ (∃ a, τ'.find? owner = some a ∧ a.code = new) ∧
      g'.toNat ≤ g''.toNat ∧ g''.toNat ≤ gasCost' := by
    unfold callRun at hq
    split at hq <;> rename_i hcond
    · have hcond' := cond.mp hcond
      obtain ⟨lo', cand⟩ := theta_call summary reentry notPre N cert f hN bvh u.createdAccounts
        u.genesisBlockHeader u.blocks u.accountMap u.σ₀ u'.accountMap u'.σ₀
        (u.addAccessedAccount (AccountAddress.ofUInt256 t)).substate
        (AccountAddress.ofUInt256 src) u.executionEnv.sender
        (AccountAddress.ofUInt256 rcp) (AccountAddress.ofUInt256 t) hr
        (.ofNat (callGas t rcp v gas u)) (.ofNat (callGas t rcp v gas' u')) (gasCost' - gasCost) hgC
        (.ofNat u.executionEnv.gasPrice) v v' (u.memory.readWithPadding io.toNat is.toNat)
        (u.executionEnv.depth + 1) u.executionEnv.header perm maps maps0 lo lo0 ln ln0 cA σ' g' A' z out hq
      refine ⟨lo', fun f' hf => ?_⟩
      obtain ⟨τ', g'', runN, hm, ln', hg, cap⟩ := cand f' hf
      refine ⟨τ', g'', ?_, hm, ln', hg, ?_⟩
      · unfold callRun
        rw [if_pos hcond']
        have subA : (u'.addAccessedAccount (AccountAddress.ofUInt256 t)).substate =
            (u.addAccessedAccount (AccountAddress.ofUInt256 t)).substate := by
          show Substate.addAccessedAccount u'.substate _ = Substate.addAccessedAccount u.substate _
          rw [sub]
        rw [← cr, ← gen, ← bl, ← snd, ← gp, ← mem, ← dep, ← hdr, subA]
        exact runN
      · rw [ofNat_toNat _ (by omega)] at cap; omega
    · have hcond' : ¬ (v ≤ (u'.accountMap.find? u'.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
          u'.executionEnv.depth < 1024) := fun h => hcond (cond.mpr h)
      injection hq with hq
      simp only [Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hq
      refine ⟨lo, fun f' hf => ⟨u'.accountMap, .ofNat (callGas t rcp v gas' u'), ?_, maps, ln, ?_, ?_⟩⟩
      · unfold callRun
        rw [if_neg hcond', ← cr]
        have subA : (u'.addAccessedAccount (AccountAddress.ofUInt256 t)).substate =
            (u.addAccessedAccount (AccountAddress.ofUInt256 t)).substate := by
          show Substate.addAccessedAccount u'.substate _ = Substate.addAccessedAccount u.substate _
          rw [sub]
        rw [subA]
      · rw [ofNat_toNat _ (by omega), ofNat_toNat _ (by omega)]; omega
      · rw [ofNat_toNat _ (by omega)]; omega
  obtain ⟨lo', key⟩ := key
  refine ⟨xs, c2, rfl, rfl, fun f' hf => ?_⟩
  obtain ⟨τ', g'', runN, hm, ln', hg, cap⟩ := key f' hf
  have gcap : gasCost' ≤ u'.gasAvailable.toNat := by omega
  refine ⟨callPost u' gasCost' io is oo os (cA, τ', g'', A', z, out),
    (u'.gasAvailable.toNat - gasCost' + g''.toNat) - (u.gasAvailable.toNat - gasCost + g'.toNat),
    ?_, ?_, ?_, rfl, rfl⟩
  · rw [← status]; exact call_of runN
  · refine ⟨?_, ?_, ?_, ?_⟩
    · show E (callPost u gasCost io is oo os (cA, σ', g', A', z, out)) =
        E { callPost u' gasCost' io is oo os (cA, τ', g'', A', z, out) with stack := u.stack }
      rw [callPost_erased u gasCost gasCost' io is oo os cA σ' τ' g' g'' A' z out, callPost_frame,
        show { callPost u' gasCost' io is oo os (cA, τ', g'', A', z, out) with stack := u.stack } =
          callPost { u' with stack := u.stack } gasCost' io is oo os (cA, τ', g'', A', z, out) from rfl,
        callPost_frame { u' with stack := u.stack }, F]
    · exact rel.count
    · show ((u'.gasAvailable - .ofNat gasCost') + g'').toNat =
        ((u.gasAvailable - .ofNat gasCost) + g').toNat + _
      rw [add_toNat, add_toNat, word_sub_toNat _ _ (by omega) gcap, word_sub_toNat _ _ (by omega) enough]
      · omega
      · rw [word_sub_toNat _ _ (by omega) enough]; omega
      · rw [word_sub_toNat _ _ (by omega) gcap]; omega
    · exact ⟨hm, maps0, ⟨ownU, codeU, lo', lo0⟩, ⟨ownU', codeU', ln', ln0⟩⟩
  · show ((u'.gasAvailable - .ofNat gasCost') + g'').toNat ≤ u'.gasAvailable.toNat
    rw [add_toNat, word_sub_toNat _ _ (by omega) gcap]
    · omega
    · rw [word_sub_toNat _ _ (by omega) gcap]; omega

/-- `Z` for a call in the candidate, from the original's `Z` and the bounded cost. -/
theorem zok_call {owner : AccountAddress} {old new : ByteArray} {surplus skipped : ℕ} {oj nj : Array UInt256}
    {op : Operation .EVM} {k : ℕ} (hop : CallOp op k) (s t : State) (g₀ g₀' : UInt256) (rest : List UInt256)
    (hs : s.stack = g₀ :: rest) (ht : t.stack = g₀' :: rest)
    (rel : DeployedOffset owner old new surplus skipped s { t with stack := s.stack })
    (memEq : memoryExpansionCost s op = memoryExpansionCost t op)
    (cost : C' (gasCut t op) op ≤ C' (gasCut s op) op + surplus)
    (z : ZOk oj op s) : ZOk nj op t := by
  have gasT : t.gasAvailable.toNat = s.gasAvailable.toNat + surplus := rel.gas
  have perm := rel_perm rel
  change s.executionEnv.perm = t.executionEnv.perm at perm
  have zm := z.mem
  have zc := z.cost
  have gs := word_sub_toNat s.gasAvailable (memoryExpansionCost s op)
    (lt_of_le_of_lt zm s.gasAvailable.val.isLt) zm
  have gt := word_sub_toNat t.gasAvailable (memoryExpansionCost t op)
    (by rw [← memEq]; exact lt_of_le_of_lt zm s.gasAvailable.val.isLt) (by rw [← memEq]; omega)
  refine ⟨by rw [← memEq]; omega, ?_, z.defined, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change C' (gasCut t op) op ≤ (t.gasAvailable - .ofNat (memoryExpansionCost t op)).toNat
    change C' (gasCut s op) op ≤ (s.gasAvailable - .ofNat (memoryExpansionCost s op)).toNat at zc
    rw [gt]; rw [gs] at zc; omega
  · have := z.inputs; rw [hs] at this; rw [ht]; simpa using this
  · rintro ⟨h, -⟩; cases hop <;> cases h
  · rintro ⟨h, -⟩; cases hop <;> cases h
  · rintro ⟨h, -⟩; cases hop <;> cases h
  · have := z.outputs; rw [hs] at this; rw [ht]; simpa using this
  · have := z.static
    rw [← perm]
    cases hop <;> simpa [W, hs, ht] using this
  · rintro ⟨h, -⟩; cases hop <;> cases h
  · rintro ⟨h, -⟩; cases hop <;> cases h

/-- The call case at the interpreter level: from related states at a CALL or STATICCALL whose
gas arguments differ by `d ≤ surplus`, the original's run continues from a state the
candidate matches for every fuel at least the original's. -/
theorem call_core {owner : AccountAddress} {old new : ByteArray}
    (summary : CalleeSummary owner old new) (reentry : Reentry owner old) (notPre : owner ∉ π)
    (N : ℕ) (cert : Cert owner old new N) (ho : 0 < old.size) (hn : 0 < new.size)
    {oj nj : Array UInt256} {op : Operation .EVM} {k : ℕ} (hop : CallOp op k)
    (s t : State) (surplus skipped f : ℕ) (r : ExecutionResult State)
    (g₀ g₀' : UInt256) (rest : List UInt256) (d : ℕ)
    (rel : DeployedOffset owner old new surplus skipped s { t with stack := s.stack })
    (hs : s.stack = g₀ :: rest) (ht : t.stack = g₀' :: rest)
    (hd : g₀'.toNat = g₀.toNat + d) (hds : d ≤ surplus)
    (o : decode old s.pc = some (op, none)) (n : decode new s.pc = some (op, none))
    (hN : f + 1 ≤ N) (ok : X (f + 1) oj s = .ok r) :
    ∃ (v : State) (x : UInt256), (x = ⟨0⟩ ∨ x = ⟨1⟩) ∧ X f oj v = .ok r ∧
      v.pc = s.pc + UInt256.ofNat 1 ∧ v.stack = x :: rest.drop (k - 1) ∧
      ∀ g, f ≤ g → ∃ v' surplus' skipped', X (g + 1) nj t = X g nj v' ∧
        DeployedOffset owner old new surplus' skipped' v v' ∧
        v'.gasAvailable.toNat ≤ t.gasAvailable.toNat := by
  have sc : s.executionEnv.code = old := rel.maps.2.2.1.2.1
  have tc : t.executionEnv.code = new := rel.maps.2.2.2.2.1
  have samePC := offset_pc rel
  change s.pc = t.pc at samePC
  have ds : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (op, none) :=
    getD_of (by rw [sc]; exact o)
  have dt : (decode t.executionEnv.code t.pc).getD (.STOP, .none) = (op, none) :=
    getD_of (by rw [tc, ← samePC]; exact n)
  have aw : s.activeWords = t.activeWords := by
    simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
      congrArg (fun x : State => x.activeWords) rel.frame
  have perm := rel_perm rel
  change s.executionEnv.perm = t.executionEnv.perm at perm
  obtain ⟨z, nx, step, rest'⟩ := X_inv ds ok
  have hH : H nx.toMachineState op = none := by cases hop <;> simp [H]
  rw [hH] at rest'
  cases f with
  | zero => rw [step_zero] at step; cases step
  | succ f₁ =>
  have memEq := mem_call_eq hop s t g₀ g₀' rest hs ht aw
  have memEq' := mem_call_eq hop { t with stack := s.stack } t g₀ g₀' rest hs ht rfl
  have relc : DeployedOffset owner old new surplus skipped (gasCut s op) { gasCut t op with stack := s.stack } := by
    have h := rel_gasCut rel op z.mem
    have e : gasCut { t with stack := s.stack } op = { gasCut t op with stack := s.stack } := by
      simp only [gasCut, memEq']
    rwa [e] at h
  have relu := rel_count relc
  have eu : ({ ({ gasCut t op with stack := s.stack } : State) with
      execLength := ({ gasCut t op with stack := s.stack } : State).execLength + 1 } : State) =
      { ({ gasCut t op with execLength := (gasCut t op).execLength + 1 } : State) with stack := s.stack } := rfl
  rw [eu] at relu
  have gasc : (gasCut s op).gasAvailable.toNat = s.gasAvailable.toNat - memoryExpansionCost s op :=
    word_sub_toNat _ _ (lt_of_le_of_lt z.mem s.gasAvailable.val.isLt) z.mem
  have zm := z.mem
  have gT : t.gasAvailable.toNat = s.gasAvailable.toNat + surplus := rel.gas
  have mt : memoryExpansionCost t op ≤ t.gasAvailable.toNat := by rw [← memEq]; omega
  have gasct : (gasCut t op).gasAvailable.toNat = t.gasAvailable.toNat - memoryExpansionCost t op :=
    word_sub_toNat t.gasAvailable (memoryExpansionCost t op) (lt_of_le_of_lt mt t.gasAvailable.val.isLt) mt
  have hstack : (gasCut s op).stack = g₀ :: rest := hs
  have htstack : (gasCut t op).stack = g₀' :: rest := ht
  have cut_t : (gasCut t op).gasAvailable.toNat ≤ t.gasAvailable.toNat := by rw [gasct]; omega
  cases hop with
  | call =>
    obtain ⟨stk, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆, x, state', hp, hcall, hnx⟩ := step_call_inv _ _ _ _ _ step
    subst hnx
    have hrest := pop7_eq hp
    rw [hstack] at hrest
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrest
    obtain ⟨rfl, hrest⟩ := hrest
    cases f₁ with
    | zero => rw [call_zero] at hcall; cases hcall
    | succ f₂ =>
    have hc := cost_call (gasCut s .CALL) g₀ μ₁ μ₂ _ (by rw [hstack, hrest])
    have hc' := cost_call (gasCut t .CALL) g₀' μ₁ μ₂ _ (by rw [htstack, hrest])
    obtain ⟨xs, c2, rstack, rpc, cand⟩ := call_rel summary reentry notPre N cert ho hn f₂ (by omega)
      (gasCut s .CALL).executionEnv.blobVersionedHashes g₀ g₀'
      (.ofNat (gasCut s .CALL).executionEnv.codeOwner) μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆
      (gasCut s .CALL).executionEnv.perm _ _ surplus skipped d _ _ x state' relu (fun h => h) hd hds hc hc'
      z.cost hcall
    refine ⟨_, x, xs, rest', ?_, ?_, fun g hg => ?_⟩
    · show state'.pc + UInt256.ofNat 1 = s.pc + UInt256.ofNat 1
      rw [rpc]; rfl
    · show x :: stk = x :: rest.drop 6; rw [hrest]; rfl
    · obtain ⟨g₂, rfl⟩ : ∃ g₂, g = g₂ + 2 := ⟨g - 2, by omega⟩
      obtain ⟨r', surplus', runC, relr, cap, rstack', rpc'⟩ := cand g₂ (by omega)
      have ht' : (gasCut t .CALL).stack.pop7 = some (stk, g₀', μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) := by
        rw [htstack, hrest]; rfl
      have bvhE : (gasCut t .CALL).executionEnv.blobVersionedHashes =
          (gasCut s .CALL).executionEnv.blobVersionedHashes := by
        simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
          (congrArg (fun x : State => x.executionEnv.blobVersionedHashes) rel.frame).symm
      have permE : (gasCut t .CALL).executionEnv.perm = (gasCut s .CALL).executionEnv.perm := perm.symm
      have ownE : (gasCut t .CALL).executionEnv.codeOwner = (gasCut s .CALL).executionEnv.codeOwner :=
        (rel.maps.2.2.2.1 : t.executionEnv.codeOwner = owner).trans
          (rel.maps.2.2.1.1 : s.executionEnv.codeOwner = owner).symm
      rw [← bvhE, ← permE, ← ownE] at runC
      have stepC := step_call_of (g₂ + 1) _ none _ _ _ _ _ _ _ _ _ _ _ ht' runC
      have zt := zok_call (nj := nj) CallOp.call s t g₀ g₀' rest hs ht rel memEq c2 z
      refine ⟨r'.replaceStackAndIncrPC (stk.push x), surplus', skipped, ?_, ?_, ?_⟩
      · show X (g₂ + 1 + 1 + 1) nj t = X (g₂ + 1 + 1) nj (r'.replaceStackAndIncrPC (stk.push x))
        rw [X_run dt zt stepC]
        simp [H]
      · have := (replace_frameless (stk.push x) 1).preserve relr
        rwa [rstack] at this
      · show r'.gasAvailable.toNat ≤ t.gasAvailable.toNat
        exact le_trans cap cut_t
  | staticcall =>
    obtain ⟨stk, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆, x, state', hp, hcall, hnx⟩ := step_staticcall_inv _ _ _ _ _ step
    subst hnx
    have hrest := pop6_eq hp
    rw [hstack] at hrest
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrest
    obtain ⟨rfl, hrest⟩ := hrest
    cases f₁ with
    | zero => rw [call_zero] at hcall; cases hcall
    | succ f₂ =>
    have hc := cost_staticcall (gasCut s .STATICCALL) g₀ μ₁ _ (by rw [hstack, hrest])
    have hc' := cost_staticcall (gasCut t .STATICCALL) g₀' μ₁ _ (by rw [htstack, hrest])
    obtain ⟨xs, c2, rstack, rpc, cand⟩ := call_rel summary reentry notPre N cert ho hn f₂ (by omega)
      (gasCut s .STATICCALL).executionEnv.blobVersionedHashes g₀ g₀'
      (.ofNat (gasCut s .STATICCALL).executionEnv.codeOwner) μ₁ μ₁ ⟨0⟩ ⟨0⟩ μ₃ μ₄ μ₅ μ₆
      false _ _ surplus skipped d _ _ x state' relu (fun h => h) hd hds hc hc' z.cost hcall
    refine ⟨_, x, xs, rest', ?_, ?_, fun g hg => ?_⟩
    · show state'.pc + UInt256.ofNat 1 = s.pc + UInt256.ofNat 1
      rw [rpc]; rfl
    · show x :: stk = x :: rest.drop 5; rw [hrest]; rfl
    · obtain ⟨g₂, rfl⟩ : ∃ g₂, g = g₂ + 2 := ⟨g - 2, by omega⟩
      obtain ⟨r', surplus', runC, relr, cap, rstack', rpc'⟩ := cand g₂ (by omega)
      have ht' : (gasCut t .STATICCALL).stack.pop6 = some (stk, g₀', μ₁, μ₃, μ₄, μ₅, μ₆) := by
        rw [htstack, hrest]; rfl
      have bvhE : (gasCut t .STATICCALL).executionEnv.blobVersionedHashes =
          (gasCut s .STATICCALL).executionEnv.blobVersionedHashes := by
        simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
          (congrArg (fun x : State => x.executionEnv.blobVersionedHashes) rel.frame).symm
      have ownE : (gasCut t .STATICCALL).executionEnv.codeOwner =
          (gasCut s .STATICCALL).executionEnv.codeOwner :=
        (rel.maps.2.2.2.1 : t.executionEnv.codeOwner = owner).trans
          (rel.maps.2.2.1.1 : s.executionEnv.codeOwner = owner).symm
      rw [← bvhE, ← ownE] at runC
      have stepC := step_staticcall_of (g₂ + 1) _ none _ _ _ _ _ _ _ _ _ _ ht' runC
      have zt := zok_call (nj := nj) CallOp.staticcall s t g₀ g₀' rest hs ht rel memEq c2 z
      refine ⟨r'.replaceStackAndIncrPC (stk.push x), surplus', skipped, ?_, ?_, ?_⟩
      · show X (g₂ + 1 + 1 + 1) nj t = X (g₂ + 1 + 1) nj (r'.replaceStackAndIncrPC (stk.push x))
        rw [X_run dt zt stepC]
        simp [H]
      · have := (replace_frameless (stk.push x) 1).preserve relr
        rwa [rstack] at this
      · show r'.gasAvailable.toNat ≤ t.gasAvailable.toNat
        exact le_trans cap cut_t

  | callcode =>
    obtain ⟨stk, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆, x, state', hp, hcall, hnx⟩ := step_callcode_inv _ _ _ _ _ step
    subst hnx
    have hrest := pop7_eq hp
    rw [hstack] at hrest
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrest
    obtain ⟨rfl, hrest⟩ := hrest
    cases f₁ with
    | zero => rw [call_zero] at hcall; cases hcall
    | succ f₂ =>
    have ownS : (gasCut s .CALLCODE).executionEnv.codeOwner = owner := rel.maps.2.2.1.1
    have ownT : (gasCut t .CALLCODE).executionEnv.codeOwner = owner := rel.maps.2.2.2.1
    have hc : C' (gasCut s .CALLCODE) .CALLCODE = Ccall (AccountAddress.ofUInt256 μ₁)
        (AccountAddress.ofUInt256 (.ofNat (gasCut s .CALLCODE).executionEnv.codeOwner)) μ₂ g₀
        (gasCut s .CALLCODE).accountMap (gasCut s .CALLCODE).toMachineState (gasCut s .CALLCODE).substate := by
      rw [cost_callcode (gasCut s .CALLCODE) g₀ μ₁ μ₂ _ (by rw [hstack, hrest]), ofUInt256_ofNat]
    have hc' : C' (gasCut t .CALLCODE) .CALLCODE = Ccall (AccountAddress.ofUInt256 μ₁)
        (AccountAddress.ofUInt256 (.ofNat (gasCut s .CALLCODE).executionEnv.codeOwner)) μ₂ g₀'
        (gasCut t .CALLCODE).accountMap (gasCut t .CALLCODE).toMachineState (gasCut t .CALLCODE).substate := by
      rw [cost_callcode (gasCut t .CALLCODE) g₀' μ₁ μ₂ _ (by rw [htstack, hrest]), ofUInt256_ofNat, ownS, ownT]
    obtain ⟨xs, c2, rstack, rpc, cand⟩ := call_rel summary reentry notPre N cert ho hn f₂ (by omega)
      (gasCut s .CALLCODE).executionEnv.blobVersionedHashes g₀ g₀'
      (.ofNat (gasCut s .CALLCODE).executionEnv.codeOwner) (.ofNat (gasCut s .CALLCODE).executionEnv.codeOwner)
      μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ (gasCut s .CALLCODE).executionEnv.perm _ _ surplus skipped d _ _ x state' relu
      (fun _ => by rw [ofUInt256_ofNat]; exact ownS) hd hds hc hc' z.cost hcall
    refine ⟨_, x, xs, rest', ?_, ?_, fun g hg => ?_⟩
    · show state'.pc + UInt256.ofNat 1 = s.pc + UInt256.ofNat 1
      rw [rpc]; rfl
    · show x :: stk = x :: rest.drop 6; rw [hrest]; rfl
    · obtain ⟨g₂, rfl⟩ : ∃ g₂, g = g₂ + 2 := ⟨g - 2, by omega⟩
      obtain ⟨r', surplus', runC, relr, cap, rstack', rpc'⟩ := cand g₂ (by omega)
      have ht' : (gasCut t .CALLCODE).stack.pop7 = some (stk, g₀', μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) := by
        rw [htstack, hrest]; rfl
      have bvhE : (gasCut t .CALLCODE).executionEnv.blobVersionedHashes =
          (gasCut s .CALLCODE).executionEnv.blobVersionedHashes := by
        simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
          (congrArg (fun x : State => x.executionEnv.blobVersionedHashes) rel.frame).symm
      have permE : (gasCut t .CALLCODE).executionEnv.perm = (gasCut s .CALLCODE).executionEnv.perm := perm.symm
      have ownE : (gasCut t .CALLCODE).executionEnv.codeOwner = (gasCut s .CALLCODE).executionEnv.codeOwner :=
        ownT.trans ownS.symm
      rw [← bvhE, ← permE, ← ownE] at runC
      have stepC := step_callcode_of (g₂ + 1) _ none _ _ _ _ _ _ _ _ _ _ _ ht' runC
      have zt := zok_call (nj := nj) CallOp.callcode s t g₀ g₀' rest hs ht rel memEq c2 z
      refine ⟨r'.replaceStackAndIncrPC (stk.push x), surplus', skipped, ?_, ?_, ?_⟩
      · show X (g₂ + 1 + 1 + 1) nj t = X (g₂ + 1 + 1) nj (r'.replaceStackAndIncrPC (stk.push x))
        rw [X_run dt zt stepC]
        simp [H]
      · have := (replace_frameless (stk.push x) 1).preserve relr
        rwa [rstack] at this
      · show r'.gasAvailable.toNat ≤ t.gasAvailable.toNat
        exact le_trans cap cut_t
  | delegatecall =>
    obtain ⟨stk, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆, x, state', hp, hcall, hnx⟩ := step_delegatecall_inv _ _ _ _ _ step
    subst hnx
    have hrest := pop6_eq hp
    rw [hstack] at hrest
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrest
    obtain ⟨rfl, hrest⟩ := hrest
    cases f₁ with
    | zero => rw [call_zero] at hcall; cases hcall
    | succ f₂ =>
    have ownS : (gasCut s .DELEGATECALL).executionEnv.codeOwner = owner := rel.maps.2.2.1.1
    have ownT : (gasCut t .DELEGATECALL).executionEnv.codeOwner = owner := rel.maps.2.2.2.1
    have hc : C' (gasCut s .DELEGATECALL) .DELEGATECALL = Ccall (AccountAddress.ofUInt256 μ₁)
        (AccountAddress.ofUInt256 (.ofNat (gasCut s .DELEGATECALL).executionEnv.codeOwner)) ⟨0⟩ g₀
        (gasCut s .DELEGATECALL).accountMap (gasCut s .DELEGATECALL).toMachineState
        (gasCut s .DELEGATECALL).substate := by
      rw [cost_delegatecall (gasCut s .DELEGATECALL) g₀ μ₁ _ (by rw [hstack, hrest]), ofUInt256_ofNat]
    have hc' : C' (gasCut t .DELEGATECALL) .DELEGATECALL = Ccall (AccountAddress.ofUInt256 μ₁)
        (AccountAddress.ofUInt256 (.ofNat (gasCut s .DELEGATECALL).executionEnv.codeOwner)) ⟨0⟩ g₀'
        (gasCut t .DELEGATECALL).accountMap (gasCut t .DELEGATECALL).toMachineState
        (gasCut t .DELEGATECALL).substate := by
      rw [cost_delegatecall (gasCut t .DELEGATECALL) g₀' μ₁ _ (by rw [htstack, hrest]), ofUInt256_ofNat,
        ownS, ownT]
    obtain ⟨xs, c2, rstack, rpc, cand⟩ := call_rel summary reentry notPre N cert ho hn f₂ (by omega)
      (gasCut s .DELEGATECALL).executionEnv.blobVersionedHashes g₀ g₀'
      (.ofNat (gasCut s .DELEGATECALL).executionEnv.source)
      (.ofNat (gasCut s .DELEGATECALL).executionEnv.codeOwner) μ₁ ⟨0⟩
      (gasCut s .DELEGATECALL).executionEnv.weiValue μ₃ μ₄ μ₅ μ₆ (gasCut s .DELEGATECALL).executionEnv.perm
      _ _ surplus skipped d _ _ x state' relu (fun _ => by rw [ofUInt256_ofNat]; exact ownS) hd hds hc hc'
      z.cost hcall
    refine ⟨_, x, xs, rest', ?_, ?_, fun g hg => ?_⟩
    · show state'.pc + UInt256.ofNat 1 = s.pc + UInt256.ofNat 1
      rw [rpc]; rfl
    · show x :: stk = x :: rest.drop 5; rw [hrest]; rfl
    · obtain ⟨g₂, rfl⟩ : ∃ g₂, g = g₂ + 2 := ⟨g - 2, by omega⟩
      obtain ⟨r', surplus', runC, relr, cap, rstack', rpc'⟩ := cand g₂ (by omega)
      have ht' : (gasCut t .DELEGATECALL).stack.pop6 = some (stk, g₀', μ₁, μ₃, μ₄, μ₅, μ₆) := by
        rw [htstack, hrest]; rfl
      have bvhE : (gasCut t .DELEGATECALL).executionEnv.blobVersionedHashes =
          (gasCut s .DELEGATECALL).executionEnv.blobVersionedHashes := by
        simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
          (congrArg (fun x : State => x.executionEnv.blobVersionedHashes) rel.frame).symm
      have srcE : (gasCut t .DELEGATECALL).executionEnv.source = (gasCut s .DELEGATECALL).executionEnv.source := by
        simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
          (congrArg (fun x : State => x.executionEnv.source) rel.frame).symm
      have weiE : (gasCut t .DELEGATECALL).executionEnv.weiValue =
          (gasCut s .DELEGATECALL).executionEnv.weiValue := by
        simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
          (congrArg (fun x : State => x.executionEnv.weiValue) rel.frame).symm
      have permE : (gasCut t .DELEGATECALL).executionEnv.perm = (gasCut s .DELEGATECALL).executionEnv.perm :=
        perm.symm
      have ownE : (gasCut t .DELEGATECALL).executionEnv.codeOwner =
          (gasCut s .DELEGATECALL).executionEnv.codeOwner := ownT.trans ownS.symm
      rw [← bvhE, ← srcE, ← weiE, ← permE, ← ownE] at runC
      have stepC := step_delegatecall_of (g₂ + 1) _ none _ _ _ _ _ _ _ _ _ _ ht' runC
      have zt := zok_call (nj := nj) CallOp.delegatecall s t g₀ g₀' rest hs ht rel memEq c2 z
      refine ⟨r'.replaceStackAndIncrPC (stk.push x), surplus', skipped, ?_, ?_, ?_⟩
      · show X (g₂ + 1 + 1 + 1) nj t = X (g₂ + 1 + 1) nj (r'.replaceStackAndIncrPC (stk.push x))
        rw [X_run dt zt stepC]
        simp [H]
      · have := (replace_frameless (stk.push x) 1).preserve relr
        rwa [rstack] at this
      · show r'.gasAvailable.toNat ≤ t.gasAvailable.toNat
        exact le_trans cap cut_t

/-! Code reads of other accounts: equal unless the address is the owner. -/

theorem code_rel {owner : AccountAddress} {old new : ByteArray} {σ τ : AccountMap .EVM}
    (rel : MapsRelated owner old new σ τ) (a : AccountAddress) (hne : a ≠ owner) :
    (σ.find? a).option ByteArray.empty (·.code) = (τ.find? a).option ByteArray.empty (·.code) ∧
    (σ.find? a).option ⟨0⟩ Account.codeHash = (τ.find? a).option ⟨0⟩ Account.codeHash := by
  rcases related_find rel a with ⟨e, e'⟩ | ⟨x, x', e, e', h⟩
  · rw [e, e']; exact ⟨rfl, rfl⟩
  · rw [e, e']
    obtain ⟨-, -, -, -, c⟩ := h
    rw [if_neg hne] at c
    constructor <;> simp [Option.option, c, Account.codeHash, PersistentAccountState.codeHash]

/-- The state after EXTCODEHASH of `v`, with the hash `b`. -/
def hashPost (y : State) (v b : UInt256) (stk : Stack UInt256) : State :=
  ({ y with toState := y.toState.addAccessedAccount (AccountAddress.ofUInt256 v) } : State).replaceStackAndIncrPC
    (Stack.push stk b)

theorem hash_frameless (v b : UInt256) (stk : Stack UInt256) : Frameless (fun y => hashPost y v b stk) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem extcodehash_shape (arg : Option (UInt256 × Nat)) (y : State) (v : UInt256) (stk : Stack UInt256)
    (h : y.stack = v :: stk) :
    EvmYul.step (.EXTCODEHASH : Operation .EVM) arg y =
      .ok (hashPost y v (if EvmYul.State.dead y.accountMap (AccountAddress.ofUInt256 v) then ⟨0⟩
        else (y.accountMap.find? (AccountAddress.ofUInt256 v)).option ⟨0⟩ Account.codeHash) stk) := by
  change EVM.unaryStateOp EvmYul.State.extCodeHash y = _
  unfold EVM.unaryStateOp
  rw [h]
  simp only [Stack.pop, Id.run, EvmYul.State.extCodeHash, EvmYul.State.lookupAccount, hashPost]
  split <;> rfl

/-- EXTCODEHASH of an address other than the owner: the candidate pushes the same hash. -/
theorem extcodehash_step {owner old new surplus skipped s t} {oj nj : Array UInt256} {f : ℕ} {nx : State}
    {rest : List UInt256} (addr : ℕ)
    (rel : DeployedOffset owner old new surplus skipped s t)
    (jumps : ∀ x, oj.contains x = true → nj.contains x = true)
    (dt : (decode t.executionEnv.code t.pc).getD (.STOP, .none) = (.EXTCODEHASH, none))
    (z : ZOk oj .EXTCODEHASH s)
    (step : EVM.step (f + 1) (C' (gasCut s .EXTCODEHASH) .EXTCODEHASH) (some (.EXTCODEHASH, none))
      (gasCut s .EXTCODEHASH) = .ok nx)
    (hs : s.stack = UInt256.ofNat addr :: rest)
    (hne : AccountAddress.ofUInt256 (UInt256.ofNat addr) ≠ owner) (ho : 0 < old.size) (hn : 0 < new.size) :
    nx.pc = s.pc + UInt256.ofNat 1 ∧ (∃ x, nx.stack = x :: rest) ∧
    ∃ v', DeployedOffset owner old new surplus skipped nx v' ∧
      v'.gasAvailable.toNat ≤ t.gasAvailable.toNat ∧ ∀ g, X (g + 2) nj t = X (g + 1) nj v' := by
  have cut := rel_gasCut rel .EXTCODEHASH z.mem
  have costEq : C' (gasCut t .EXTCODEHASH) .EXTCODEHASH = C' (gasCut s .EXTCODEHASH) .EXTCODEHASH :=
    (congrArg (fun x => C' x .EXTCODEHASH) cut.frame).symm
  obtain ⟨zt, -⟩ := Z_transport rel costEq jumps z
  have rb := rel_bump cut _ z.cost
  have hs1 : (bump (gasCut s .EXTCODEHASH) (C' (gasCut s .EXTCODEHASH) .EXTCODEHASH)).stack =
      UInt256.ofNat addr :: rest := hs
  have hs2 : (bump (gasCut t .EXTCODEHASH) (C' (gasCut s .EXTCODEHASH) .EXTCODEHASH)).stack =
      UInt256.ofNat addr :: rest := by rw [← rel_stack rb]; exact hs1
  change EvmYul.step (.EXTCODEHASH : Operation .EVM) none
    (bump (gasCut s .EXTCODEHASH) (C' (gasCut s .EXTCODEHASH) .EXTCODEHASH)) = .ok nx at step
  rw [extcodehash_shape none _ _ rest hs1] at step
  injection step with step
  subst step
  obtain ⟨-, hv⟩ := code_rel rb.maps.1 (AccountAddress.ofUInt256 (UInt256.ofNat addr)) hne
  have hd := dead_rel rb.maps.1 ho hn (AccountAddress.ofUInt256 (UInt256.ofNat addr))
  generalize hH : (if EvmYul.State.dead
      (bump (gasCut s .EXTCODEHASH) (C' (gasCut s .EXTCODEHASH) .EXTCODEHASH)).accountMap
      (AccountAddress.ofUInt256 (UInt256.ofNat addr)) then (⟨0⟩ : UInt256)
    else ((bump (gasCut s .EXTCODEHASH) (C' (gasCut s .EXTCODEHASH) .EXTCODEHASH)).accountMap.find?
      (AccountAddress.ofUInt256 (UInt256.ofNat addr))).option ⟨0⟩ Account.codeHash) = HO
  refine ⟨rfl, ⟨HO, rfl⟩, hashPost (bump (gasCut t .EXTCODEHASH) (C' (gasCut s .EXTCODEHASH) .EXTCODEHASH))
    (UInt256.ofNat addr) HO rest, ?_, ?_, fun g => ?_⟩
  · exact (hash_frameless _ _ _).preserve rb
  · show (bump (gasCut t .EXTCODEHASH) _).gasAvailable.toNat ≤ t.gasAvailable.toNat
    have h2 : (gasCut t .EXTCODEHASH).gasAvailable.toNat ≤ t.gasAvailable.toNat := by
      change (t.gasAvailable - .ofNat (memoryExpansionCost t .EXTCODEHASH)).toNat ≤ _
      rw [word_sub_toNat _ _ (lt_of_le_of_lt zt.mem t.gasAvailable.val.isLt) zt.mem]; omega
    rw [bump_gas _ _ (by rw [← costEq]; exact zt.cost)]; omega
  · have sg : EVM.step (g + 1) (C' (gasCut t .EXTCODEHASH) .EXTCODEHASH) (some (.EXTCODEHASH, none))
        (gasCut t .EXTCODEHASH) =
        .ok (hashPost (bump (gasCut t .EXTCODEHASH) (C' (gasCut s .EXTCODEHASH) .EXTCODEHASH))
          (UInt256.ofNat addr) HO rest) := by
      change EvmYul.step (.EXTCODEHASH : Operation .EVM) none
        (bump (gasCut t .EXTCODEHASH) (C' (gasCut t .EXTCODEHASH) .EXTCODEHASH)) = _
      rw [costEq, extcodehash_shape none _ _ rest hs2]
      show Except.ok (hashPost _ _ _ rest) = Except.ok (hashPost _ _ HO rest)
      rw [← hH, hd, hv]
    rw [X_run dt zt sg]
    simp [H]

/-- The state after EXTCODECOPY from code `b`. -/
def extcopyPost (y : State) (acc mstart cstart size : UInt256) (stk : List UInt256) (b : ByteArray) : State :=
  ({ y with toSharedState := { y.toSharedState with
      memory := b.write cstart.toNat y.memory mstart.toNat size.toNat
      substate := y.substate.addAccessedAccount (AccountAddress.ofUInt256 acc)
      activeWords := .ofNat (MachineState.M y.activeWords.toNat mstart.toNat size.toNat) } } : State).replaceStackAndIncrPC stk

theorem extcopy_frameless (acc mstart cstart size : UInt256) (stk : List UInt256) (b : ByteArray) :
    Frameless (fun y => extcopyPost y acc mstart cstart size stk b) := by
  refine ⟨fun y => ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  simp only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas, extcopyPost, EVM.State.replaceStackAndIncrPC,
    EVM.State.incrPC]

theorem extcodecopy_shape (arg : Option (UInt256 × Nat)) (y : State) (acc mstart cstart size : UInt256)
    (stk : List UInt256) (h : y.stack = acc :: mstart :: cstart :: size :: stk) :
    EvmYul.step (.EXTCODECOPY : Operation .EVM) arg y =
      .ok (extcopyPost y acc mstart cstart size stk
        ((y.accountMap.find? (AccountAddress.ofUInt256 acc)).option ByteArray.empty (·.code))) := by
  change EVM.quaternaryCopyOp SharedState.extCodeCopy' y = _
  unfold EVM.quaternaryCopyOp
  rw [h]
  simp only [Stack.pop4, Id.run, SharedState.extCodeCopy', EvmYul.State.lookupAccount, extcopyPost]
  rfl

/-- EXTCODECOPY from an address other than the owner: the candidate copies the same bytes. -/
theorem extcodecopy_step {owner old new surplus skipped s t} {oj nj : Array UInt256} {f : ℕ} {nx : State}
    {mstart cstart size : UInt256} {rest : List UInt256} (addr : ℕ)
    (rel : DeployedOffset owner old new surplus skipped s t)
    (jumps : ∀ x, oj.contains x = true → nj.contains x = true)
    (dt : (decode t.executionEnv.code t.pc).getD (.STOP, .none) = (.EXTCODECOPY, none))
    (z : ZOk oj .EXTCODECOPY s)
    (step : EVM.step (f + 1) (C' (gasCut s .EXTCODECOPY) .EXTCODECOPY) (some (.EXTCODECOPY, none))
      (gasCut s .EXTCODECOPY) = .ok nx)
    (hs : s.stack = UInt256.ofNat addr :: mstart :: cstart :: size :: rest)
    (hne : AccountAddress.ofUInt256 (UInt256.ofNat addr) ≠ owner) :
    nx.pc = s.pc + UInt256.ofNat 1 ∧ nx.stack = rest ∧
    ∃ v', DeployedOffset owner old new surplus skipped nx v' ∧
      v'.gasAvailable.toNat ≤ t.gasAvailable.toNat ∧ ∀ g, X (g + 2) nj t = X (g + 1) nj v' := by
  have cut := rel_gasCut rel .EXTCODECOPY z.mem
  have costEq : C' (gasCut t .EXTCODECOPY) .EXTCODECOPY = C' (gasCut s .EXTCODECOPY) .EXTCODECOPY :=
    (congrArg (fun x => C' x .EXTCODECOPY) cut.frame).symm
  obtain ⟨zt, -⟩ := Z_transport rel costEq jumps z
  have rb := rel_bump cut _ z.cost
  have hs1 : (bump (gasCut s .EXTCODECOPY) (C' (gasCut s .EXTCODECOPY) .EXTCODECOPY)).stack =
      UInt256.ofNat addr :: mstart :: cstart :: size :: rest := hs
  have hs2 : (bump (gasCut t .EXTCODECOPY) (C' (gasCut s .EXTCODECOPY) .EXTCODECOPY)).stack =
      UInt256.ofNat addr :: mstart :: cstart :: size :: rest := by rw [← rel_stack rb]; exact hs1
  change EvmYul.step (.EXTCODECOPY : Operation .EVM) none
    (bump (gasCut s .EXTCODECOPY) (C' (gasCut s .EXTCODECOPY) .EXTCODECOPY)) = .ok nx at step
  rw [extcodecopy_shape none _ _ _ _ _ rest hs1] at step
  injection step with step
  subst step
  obtain ⟨hv, -⟩ := code_rel rb.maps.1 (AccountAddress.ofUInt256 (UInt256.ofNat addr)) hne
  generalize hB : (((bump (gasCut s .EXTCODECOPY) (C' (gasCut s .EXTCODECOPY) .EXTCODECOPY)).accountMap.find?
    (AccountAddress.ofUInt256 (UInt256.ofNat addr))).option ByteArray.empty (·.code)) = B
  refine ⟨rfl, rfl, extcopyPost (bump (gasCut t .EXTCODECOPY) (C' (gasCut s .EXTCODECOPY) .EXTCODECOPY))
    (UInt256.ofNat addr) mstart cstart size rest B, ?_, ?_, fun g => ?_⟩
  · exact (extcopy_frameless _ _ _ _ _ _).preserve rb
  · show (bump (gasCut t .EXTCODECOPY) _).gasAvailable.toNat ≤ t.gasAvailable.toNat
    have h2 : (gasCut t .EXTCODECOPY).gasAvailable.toNat ≤ t.gasAvailable.toNat := by
      change (t.gasAvailable - .ofNat (memoryExpansionCost t .EXTCODECOPY)).toNat ≤ _
      rw [word_sub_toNat _ _ (lt_of_le_of_lt zt.mem t.gasAvailable.val.isLt) zt.mem]; omega
    rw [bump_gas _ _ (by rw [← costEq]; exact zt.cost)]; omega
  · have sg : EVM.step (g + 1) (C' (gasCut t .EXTCODECOPY) .EXTCODECOPY) (some (.EXTCODECOPY, none))
        (gasCut t .EXTCODECOPY) =
        .ok (extcopyPost (bump (gasCut t .EXTCODECOPY) (C' (gasCut s .EXTCODECOPY) .EXTCODECOPY))
          (UInt256.ofNat addr) mstart cstart size rest B) := by
      change EvmYul.step (.EXTCODECOPY : Operation .EVM) none
        (bump (gasCut t .EXTCODECOPY) (C' (gasCut t .EXTCODECOPY) .EXTCODECOPY)) = _
      rw [costEq, extcodecopy_shape none _ _ _ _ _ rest hs2]
      show Except.ok (extcopyPost _ _ _ _ _ rest _) = Except.ok (extcopyPost _ _ _ _ _ rest B)
      rw [← hB, hv]
    rw [X_run dt zt sg]
    simp [H]

/-! The GAS step and byte-array sizes. -/

theorem step_gas (f c : ℕ) (arg : Option (UInt256 × Nat)) (u : State) :
    EVM.step (f + 1) c (some (.GAS, arg)) u =
      .ok ((bump u c).replaceStackAndIncrPC ((bump u c).stack.push (bump u c).gasAvailable)) := rfl

theorem cost_gas (s : State) : C' s .GAS = 2 := rfl

@[simp] theorem mem_gas (s : State) : memoryExpansionCost s .GAS = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

theorem gasCut_of_zero {s : State} {w : Operation .EVM} (h : memoryExpansionCost s w = 0) :
    gasCut s w = s := by
  simp [gasCut, h]

theorem decode_size {c : ByteArray} {pc : UInt256} {x : Operation .EVM × Option (UInt256 × Nat)}
    (h : decode c pc = some x) : 0 < c.size := by
  unfold decode at h
  cases hg : c.get? pc.toNat with
  | none => simp [hg, bind, Option.bind] at h
  | some b =>
    unfold ByteArray.get? at hg
    split at hg
    · omega
    · cases hg


#print axioms theta_call
#print axioms ccall_rel
#print axioms step_call_inv
#print axioms call_inv
#print axioms call_of
#print axioms call_rel
#print axioms call_core
#print axioms decode_size
#print axioms extcodehash_step
#print axioms extcodecopy_step

end GolfWhole
