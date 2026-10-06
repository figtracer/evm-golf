import CountOffset
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset
namespace GolfXiEntry

-- Exactly the state constructor used by pinned canonical Ξ.
def fresh (created : Batteries.RBSet AccountAddress compare) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (g : UInt256)
    (A : Substate) (I : ExecutionEnv .EVM) : EVM.State :=
  { (default : EVM.State) with
    accountMap := σ
    σ₀ := σ₀
    executionEnv := I
    substate := A
    createdAccounts := created
    gasAvailable := g
    blocks := blocks
    genesisBlockHeader := genesis }

def project (s : EVM.State) :=
  (s.createdAccounts, s.accountMap, s.gasAvailable, s.substate)

theorem xi_of_success (fuel : Nat)
    (created : Batteries.RBSet AccountAddress compare) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (g : UInt256)
    (A : Substate) (I : ExecutionEnv .EVM) (final : EVM.State) (output : ByteArray)
    (run : X fuel (D_J I.code (UInt256.ofNat 0))
      (fresh created genesis blocks σ σ₀ g A I) = .ok (.success final output)) :
    Ξ (fuel+1) created genesis blocks σ σ₀ g A I =
      .ok (.success (project final) output) := by
  unfold Ξ
  change (do
    let result ← X fuel (D_J I.code (UInt256.ofNat 0))
      (fresh created genesis blocks σ σ₀ g A I)
    match result with
    | .success s o => Except.ok (ExecutionResult.success (project s) o)
    | .revert g o => Except.ok (ExecutionResult.revert g o)) = _
  rw [run]
  rfl

theorem fresh_related (owner : AccountAddress) (old new : ByteArray)
    (created : Batteries.RBSet AccountAddress compare) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (σ σ₀ τ τ₀ : AccountMap .EVM) (g : UInt256)
    (A : Substate) (I : ExecutionEnv .EVM)
    (current : MapsRelated owner old new σ τ)
    (original : MapsRelated owner old new σ₀ τ₀)
    (oldCurrent : ∃ a, σ.find? owner = some a ∧ a.code = old)
    (oldOriginal : ∃ a, σ₀.find? owner = some a ∧ a.code = old)
    (newCurrent : ∃ a, τ.find? owner = some a ∧ a.code = new)
    (newOriginal : ∃ a, τ₀.find? owner = some a ∧ a.code = new) :
    DeployedOffset owner old new 0 0
      (fresh created genesis blocks σ σ₀ g A {I with codeOwner := owner, code := old})
      (fresh created genesis blocks τ τ₀ g A {I with codeOwner := owner, code := new}) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change g.toNat = g.toNat+0
    rfl
  · exact ⟨current, original, ⟨rfl, rfl, oldCurrent, oldOriginal⟩,
      ⟨rfl, rfl, newCurrent, newOriginal⟩⟩

/-- Fresh frames whose gas differs by `e`. -/
theorem fresh_offset (owner : AccountAddress) (old new : ByteArray)
    (created : Batteries.RBSet AccountAddress compare) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (σ σ₀ τ τ₀ : AccountMap .EVM) (g gC : UInt256) (e : ℕ)
    (hg : gC.toNat = g.toNat + e) (A : Substate) (I : ExecutionEnv .EVM)
    (current : MapsRelated owner old new σ τ)
    (original : MapsRelated owner old new σ₀ τ₀)
    (oldCurrent : ∃ a, σ.find? owner = some a ∧ a.code = old)
    (oldOriginal : ∃ a, σ₀.find? owner = some a ∧ a.code = old)
    (newCurrent : ∃ a, τ.find? owner = some a ∧ a.code = new)
    (newOriginal : ∃ a, τ₀.find? owner = some a ∧ a.code = new) :
    DeployedOffset owner old new e 0
      (fresh created genesis blocks σ σ₀ g A {I with codeOwner := owner, code := old})
      (fresh created genesis blocks τ τ₀ gC A {I with codeOwner := owner, code := new}) :=
  ⟨rfl, rfl, hg, ⟨current, original, ⟨rfl, rfl, oldCurrent, oldOriginal⟩,
    ⟨rfl, rfl, newCurrent, newOriginal⟩⟩⟩

#print axioms xi_of_success
#print axioms fresh_related
#print axioms fresh_offset
end GolfXiEntry
