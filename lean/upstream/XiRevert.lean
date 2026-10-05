import XiEntry
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset
namespace GolfXiEntry

-- Ξ forwards a canonical revert's remaining gas and output without projecting
-- a successful state. Account rollback belongs to the enclosing Θ semantics.
theorem xi_of_revert (fuel : Nat)
    (created : Batteries.RBSet AccountAddress compare) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (g : UInt256)
    (A : Substate) (I : ExecutionEnv .EVM) (remaining : UInt256) (output : ByteArray)
    (run : X fuel (D_J I.code (UInt256.ofNat 0))
      (fresh created genesis blocks σ σ₀ g A I) = .ok (.revert remaining output)) :
    Ξ (fuel+1) created genesis blocks σ σ₀ g A I =
      .ok (.revert remaining output) := by
  unfold Ξ
  change (do
    let result ← X fuel (D_J I.code (UInt256.ofNat 0))
      (fresh created genesis blocks σ σ₀ g A I)
    match result with
    | .success s o => Except.ok (ExecutionResult.success (project s) o)
    | .revert g o => Except.ok (ExecutionResult.revert g o)) = _
  rw [run]
  rfl

#print axioms xi_of_revert
end GolfXiEntry
