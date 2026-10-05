import WholeCover
import XiEntry
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition GolfXiEntry

/-! Lifting whole-program refinement of `X` to the code-execution function Ξ. -/
namespace GolfWhole

/-- Ξ results of the original and the candidate: same kind and output; on success,
equal created accounts and substate, related account maps and no less gas. -/
def XiRelated (owner : AccountAddress) (old new : ByteArray) :
    ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate) →
    ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate) → Prop
  | .success (c, σ, g, A) o, .success (c', σ', g', A') o' =>
    o = o' ∧ c = c' ∧ A = A' ∧ g.toNat ≤ g'.toNat ∧ MapsRelated owner old new σ σ'
  | .revert g o, .revert g' o' => o = o' ∧ g.toNat ≤ g'.toNat
  | _, _ => False

theorem xi_unfold (fuel : Nat) (created : Batteries.RBSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (g : UInt256)
    (A : Substate) (I : ExecutionEnv .EVM) :
    Ξ (fuel + 1) created genesis blocks σ σ₀ g A I =
      (do
        let result ← X fuel (D_J I.code (UInt256.ofNat 0)) (fresh created genesis blocks σ σ₀ g A I)
        match result with
        | .success s o => Except.ok (ExecutionResult.success (project s) o)
        | .revert g o => Except.ok (ExecutionResult.revert g o)) := by
  unfold Ξ
  rfl

theorem xi_refines (owner : AccountAddress) (old new : ByteArray)
    (cert : ∀ (fuel : ℕ) (s t : State) (surplus skipped : ℕ) (r : ExecutionResult State),
      DeployedOffset owner old new surplus skipped s t → s.pc = UInt256.ofNat 0 →
      X fuel (D_J old (UInt256.ofNat 0)) s = .ok r →
      ∃ f r', X f (D_J new (UInt256.ofNat 0)) t = .ok r' ∧ OutcomeRelated owner old new r r')
    (fuel : Nat) (created : Batteries.RBSet AccountAddress compare) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (σ σ₀ τ τ₀ : AccountMap .EVM) (g : UInt256)
    (A : Substate) (I : ExecutionEnv .EVM)
    (current : MapsRelated owner old new σ τ)
    (original : MapsRelated owner old new σ₀ τ₀)
    (oldCurrent : ∃ a, σ.find? owner = some a ∧ a.code = old)
    (oldOriginal : ∃ a, σ₀.find? owner = some a ∧ a.code = old)
    (newCurrent : ∃ a, τ.find? owner = some a ∧ a.code = new)
    (newOriginal : ∃ a, τ₀.find? owner = some a ∧ a.code = new)
    (R : ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate))
    (run : Ξ fuel created genesis blocks σ σ₀ g A {I with codeOwner := owner, code := old} = .ok R) :
    ∃ f R', Ξ f created genesis blocks τ τ₀ g A {I with codeOwner := owner, code := new} = .ok R' ∧
      XiRelated owner old new R R' := by
  have rel := fresh_related owner old new created genesis blocks σ σ₀ τ τ₀ g A I current original
    oldCurrent oldOriginal newCurrent newOriginal
  cases fuel with
  | zero => unfold Ξ at run; cases run
  | succ fuel =>
  rw [xi_unfold] at run
  cases hx : X fuel (D_J old (UInt256.ofNat 0))
      (fresh created genesis blocks σ σ₀ g A {I with codeOwner := owner, code := old}) with
  | error e =>
    change (X fuel (D_J old (UInt256.ofNat 0)) _ >>= _) = _ at run
    rw [hx] at run; cases run
  | ok r =>
    change (X fuel (D_J old (UInt256.ofNat 0)) _ >>= _) = _ at run
    rw [hx] at run
    obtain ⟨f, r', run', related⟩ := cert fuel _ _ 0 0 r rel rfl hx
    have xi : ∀ R', (match r' with
        | .success s o => Except.ok (ExecutionResult.success (project s) o)
        | .revert gr o => Except.ok (ExecutionResult.revert gr o) :
          Except EVM.ExecutionException _) = Except.ok R' →
        Ξ (f + 1) created genesis blocks τ τ₀ g A {I with codeOwner := owner, code := new} = .ok R' := by
      intro R' h
      rw [xi_unfold]
      change (X f (D_J new (UInt256.ofNat 0)) _ >>= _) = _
      rw [run']
      exact h
    cases r with
    | success s o =>
      cases r' with
      | success s' o' =>
        obtain ⟨eo, surplus, skipped, h⟩ := related
        injection run with run
        subst run
        refine ⟨f + 1, .success (project s') o', xi _ rfl, eo, ?_, ?_, ?_, h.maps.1⟩
        · simpa only [eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
            congrArg (fun x : State => x.createdAccounts) h.frame
        · simpa only [eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
            congrArg (fun x : State => x.substate) h.frame
        · change s.gasAvailable.toNat ≤ s'.gasAvailable.toNat
          have := h.gas; omega
      | revert _ _ => exact False.elim related
    | revert gr o =>
      cases r' with
      | success _ _ => exact False.elim related
      | revert gr' o' =>
        injection run with run
        subst run
        exact ⟨f + 1, .revert gr' o', xi _ rfl, related⟩

#print axioms xi_refines

end GolfWhole
