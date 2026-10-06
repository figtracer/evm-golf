import WholeOps
import XiEntry
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition GolfXiEntry

/-! Lifting whole-program refinement of `X` to the code-execution function Ξ. -/
namespace GolfWhole

/-- The certificate's claim about `X` for original fuel below `N`: from related states at
pc 0 with empty stacks, every successful or reverting original run is matched by the
candidate with the same fuel or more. -/
def Cert (owner : AccountAddress) (old new : ByteArray) (N : ℕ) : Prop :=
  ∀ (fuel : ℕ), fuel < N → ∀ (s t : State) (surplus skipped : ℕ) (r : ExecutionResult State),
    DeployedOffset owner old new surplus skipped s t → s.pc = UInt256.ofNat 0 → s.stack = [] →
    X fuel (D_J old (UInt256.ofNat 0)) s = .ok r →
    ∀ fuel', fuel ≤ fuel' → ∃ r', X fuel' (D_J new (UInt256.ofNat 0)) t = .ok r' ∧
      OutcomeRelated owner old new t.gasAvailable.toNat r r'

/-- Ξ results of the original and the candidate, the candidate given gas `gC`: same kind
and output; on success equal created accounts and substate and related account maps that
keep the owner's code; the candidate keeps no less gas than the original and no more
than `gC`. -/
def XiRelated (owner : AccountAddress) (old new : ByteArray) (gC : UInt256) :
    ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate) →
    ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate) → Prop
  | .success (c, σ, g, A) o, .success (c', σ', g', A') o' =>
    o = o' ∧ c = c' ∧ A = A' ∧ g.toNat ≤ g'.toNat ∧ g'.toNat ≤ gC.toNat ∧
      MapsRelated owner old new σ σ' ∧
      (∃ a, σ.find? owner = some a ∧ a.code = old) ∧ (∃ a, σ'.find? owner = some a ∧ a.code = new)
  | .revert g o, .revert g' o' => o = o' ∧ g.toNat ≤ g'.toNat ∧ g'.toNat ≤ gC.toNat
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

theorem xi_refines (owner : AccountAddress) (old new : ByteArray) (N : ℕ)
    (cert : Cert owner old new N) (fuel : Nat) (hN : fuel ≤ N)
    (created : Batteries.RBSet AccountAddress compare) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (σ σ₀ τ τ₀ : AccountMap .EVM) (g gC : UInt256) (e : ℕ)
    (hg : gC.toNat = g.toNat + e) (A : Substate) (I : ExecutionEnv .EVM)
    (current : MapsRelated owner old new σ τ)
    (original : MapsRelated owner old new σ₀ τ₀)
    (oldCurrent : ∃ a, σ.find? owner = some a ∧ a.code = old)
    (oldOriginal : ∃ a, σ₀.find? owner = some a ∧ a.code = old)
    (newCurrent : ∃ a, τ.find? owner = some a ∧ a.code = new)
    (newOriginal : ∃ a, τ₀.find? owner = some a ∧ a.code = new)
    (R : ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate))
    (run : Ξ fuel created genesis blocks σ σ₀ g A {I with codeOwner := owner, code := old} = .ok R) :
    ∀ fuel', fuel ≤ fuel' →
      ∃ R', Ξ fuel' created genesis blocks τ τ₀ gC A {I with codeOwner := owner, code := new} = .ok R' ∧
        XiRelated owner old new gC R R' := by
  intro fuel' hf
  have rel := fresh_offset owner old new created genesis blocks σ σ₀ τ τ₀ g gC e hg A I current
    original oldCurrent oldOriginal newCurrent newOriginal
  cases fuel with
  | zero => unfold Ξ at run; cases run
  | succ fuel =>
  cases fuel' with
  | zero => omega
  | succ fuel' =>
  rw [xi_unfold] at run
  cases hx : X fuel (D_J old (UInt256.ofNat 0))
      (fresh created genesis blocks σ σ₀ g A {I with codeOwner := owner, code := old}) with
  | error e =>
    change (X fuel (D_J old (UInt256.ofNat 0)) _ >>= _) = _ at run
    rw [hx] at run; cases run
  | ok r =>
    change (X fuel (D_J old (UInt256.ofNat 0)) _ >>= _) = _ at run
    rw [hx] at run
    obtain ⟨r', run', related⟩ := cert fuel (by omega) _ _ e 0 r rel rfl rfl hx fuel' (by omega)
    have xi : ∀ R', (match r' with
        | .success s o => Except.ok (ExecutionResult.success (project s) o)
        | .revert gr o => Except.ok (ExecutionResult.revert gr o) :
          Except EVM.ExecutionException _) = Except.ok R' →
        Ξ (fuel' + 1) created genesis blocks τ τ₀ gC A {I with codeOwner := owner, code := new} = .ok R' := by
      intro R' h
      rw [xi_unfold]
      change (X fuel' (D_J new (UInt256.ofNat 0)) _ >>= _) = _
      rw [run']
      exact h
    cases r with
    | success s o =>
      cases r' with
      | success s' o' =>
        obtain ⟨eo, cap, surplus, skipped, h⟩ := related
        injection run with run
        subst run
        refine ⟨.success (project s') o', xi _ rfl, eo, ?_, ?_, ?_, cap, h.maps.1,
          h.maps.2.2.1.2.2.1, h.maps.2.2.2.2.2.1⟩
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
        exact ⟨.revert gr' o', xi _ rfl, related⟩

#print axioms xi_refines

end GolfWhole
