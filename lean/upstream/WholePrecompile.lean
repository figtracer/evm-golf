import WholeCall
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition GolfXiEntry

/-! The ecrecover precompile satisfies the callee summary above its gas threshold. -/
namespace GolfWhole

theorem toExecute_ecrecover (σ : AccountMap .EVM) : toExecute .EVM σ 1 = .Precompiled 1 := by
  unfold toExecute
  rw [if_pos (by decide)]

/-- Θ on the ecrecover precompile: the value transfer, then `Ξ_ECREC`, then the pinned
result selection. -/
theorem theta_ecrecover (fuel : ℕ) (bvh : List ByteArray) (created : Batteries.RBSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (depth : ℕ) (H : BlockHeader) (w : Bool) :
    Θ (fuel + 1) bvh created genesis blocks σ σ₀ A s o r (.Precompiled 1) g p v v' d depth H w =
      .ok (∅,
        if (Ξ_ECREC (transfer σ s r v) g A (thetaEnv bvh s o r default p v' d depth H w)).2.1 == ∅ then σ
        else (Ξ_ECREC (transfer σ s r v) g A (thetaEnv bvh s o r default p v' d depth H w)).2.1,
        (Ξ_ECREC (transfer σ s r v) g A (thetaEnv bvh s o r default p v' d depth H w)).2.2.1,
        if (Ξ_ECREC (transfer σ s r v) g A (thetaEnv bvh s o r default p v' d depth H w)).2.1 == ∅ then A
        else (Ξ_ECREC (transfer σ s r v) g A (thetaEnv bvh s o r default p v' d depth H w)).2.2.2.1,
        (Ξ_ECREC (transfer σ s r v) g A (thetaEnv bvh s o r default p v' d depth H w)).1,
        (Ξ_ECREC (transfer σ s r v) g A (thetaEnv bvh s o r default p v' d depth H w)).2.2.2.2) := by
  rw [Θ.eq_2]
  rfl

/-- With at least 3000 gas, ecrecover succeeds, keeps the map and charges exactly 3000. -/
theorem ecrec_enough (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (h : 3000 ≤ g.toNat) :
    Ξ_ECREC σ g A I = (true, σ, g - .ofNat 3000, A, (Ξ_ECREC σ g A I).2.2.2.2) := by
  unfold Ξ_ECREC
  rw [if_neg (by omega)]

/-- The ecrecover output depends only on the call data. -/
theorem ecrec_out (σ τ : AccountMap .EVM) (g g' : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (h : 3000 ≤ g.toNat) (h' : 3000 ≤ g'.toNat) :
    (Ξ_ECREC σ g A I).2.2.2.2 = (Ξ_ECREC τ g' A I).2.2.2.2 := by
  unfold Ξ_ECREC
  rw [if_neg (by omega), if_neg (by omega)]

/-- `CalleeSummary`'s conclusion for a call to the ecrecover precompile, whenever the original
gives it at least 3000 gas. -/
theorem ecrecover_summary (owner : AccountAddress) (old new : ByteArray) (fuel : ℕ)
    (bvh : List ByteArray) (created : Batteries.RBSet AccountAddress compare) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (σ σ₀ τ τ₀ : AccountMap .EVM) (A : Substate) (s o r : AccountAddress)
    (g gC p v v' : UInt256) (d : ByteArray) (depth : ℕ) (H : BlockHeader) (w : Bool)
    (cA : Batteries.RBSet AccountAddress compare) (σ' : AccountMap .EVM) (g' : UInt256) (A' : Substate)
    (z : Bool) (out : ByteArray)
    (current : MapsRelated owner old new σ τ)
    (oldCurrent : ∃ a, σ.find? owner = some a ∧ a.code = old)
    (hg : g.toNat ≤ gC.toNat) (enough : 3000 ≤ g.toNat)
    (run : Θ fuel bvh created genesis blocks σ σ₀ A s o r (toExecute .EVM σ 1) g p v v' d depth H w =
      .ok (cA, σ', g', A', z, out)) :
    (∃ a, σ'.find? owner = some a ∧ a.code = old) ∧
    ∀ fuel', fuel ≤ fuel' → ∃ τ' g'',
      Θ fuel' bvh created genesis blocks τ τ₀ A s o r (toExecute .EVM τ 1) gC p v v' d depth H w =
        .ok (cA, τ', g'', A', z, out) ∧
      MapsRelated owner old new σ' τ' ∧ g'.toNat ≤ g''.toNat ∧ g''.toNat ≤ gC.toNat := by
  cases fuel with
  | zero => rw [theta_zero] at run; cases run
  | succ fuel =>
  obtain ⟨rel1, own1⟩ := transfer_related owner old new σ τ s r v current oldCurrent
  rw [toExecute_ecrecover, theta_ecrecover,
    ecrec_enough (transfer σ s r v) g A (thetaEnv bvh s o r default p v' d depth H w) enough] at run
  dsimp only at run
  injection run with run
  simp only [Prod.mk.injEq] at run
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := run
  have eq := related_empty rel1
  have gs := word_sub_toNat g 3000 (by decide) enough
  have gcs := word_sub_toNat gC 3000 (by decide) (by omega)
  refine ⟨?_, fun fuel' hf => ?_⟩
  · split
    · exact oldCurrent
    · exact own1
  · cases fuel' with
    | zero => omega
    | succ fuel' =>
    rw [toExecute_ecrecover, theta_ecrecover,
      ecrec_enough (transfer τ s r v) gC A (thetaEnv bvh s o r default p v' d depth H w) (by omega)]
    dsimp only
    refine ⟨if (transfer τ s r v == ∅) = true then τ else transfer τ s r v, gC - .ofNat 3000, ?_, ?_,
      by rw [gs, gcs]; omega, by rw [gcs]; omega⟩
    · rw [ecrec_out (transfer σ s r v) (transfer τ s r v) g gC A _ enough (by omega)]
      simp only [ite_self]
    · rw [eq]
      split
      · exact current
      · exact rel1

#print axioms ecrecover_summary

end GolfWhole
