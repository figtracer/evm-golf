import Transport

/-! Deployed-state relation permitting a natural execution-count difference.
    The existing exact-frame relation remains unchanged. -/
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM
namespace GolfCountOffset
open GolfUpstream

def eraseCount (s : EVM.State) : EVM.State := {s with execLength := 0}

structure DeployedOffset (owner : AccountAddress) (old new : ByteArray)
 (surplus skipped : Nat) (baseline candidate : EVM.State) : Prop where
 frame : eraseCount (deployedFrame baseline) = eraseCount (deployedFrame candidate)
 count : baseline.execLength = candidate.execLength + skipped
 gas : candidate.gasAvailable.toNat = baseline.gasAvailable.toNat + surplus
 maps : DeployedMaps owner old new baseline candidate

theorem of_exact {owner old new surplus s t}
 (h : DeployedFrameWithGas owner old new surplus s t) : DeployedOffset owner old new surplus 0 s t := by
 refine ⟨congrArg eraseCount h.frame,?_,h.gas,h.maps⟩
 have counts := congrArg EVM.State.execLength h.frame
 simpa [deployedFrame,eraseMaps,eraseCodeGas] using counts

theorem zero_to_exact {owner old new surplus s t}
 (h : DeployedOffset owner old new surplus 0 s t) : DeployedFrameWithGas owner old new surplus s t := by
 have counts : s.execLength = t.execLength := by simpa using h.count
 have restore := congrArg (fun u : EVM.State => {u with execLength := s.execLength}) h.frame
 refine ⟨?_,h.gas,h.maps⟩
 simpa [eraseCount,deployedFrame,eraseMaps,eraseCodeGas,counts] using restore

theorem step_sub (s : EVM.State) (fuel cost : Nat) (arg : Option (UInt256 × Nat))
 (a b : UInt256) (tail : List UInt256) (stack : s.stack = b::a::tail) :
 EVM.step (fuel+1) cost (some (.SUB,arg)) s = .ok (binaryPost s (UInt256.sub b a) tail cost) := by
 simp [EVM.step,stack,binaryPost,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,Stack.push]
 rfl

theorem step_and (s : EVM.State) (fuel cost : Nat) (arg : Option (UInt256 × Nat))
 (a b : UInt256) (tail : List UInt256) (stack : s.stack = b::a::tail) :
 EVM.step (fuel+1) cost (some (.AND,arg)) s = .ok (binaryPost s (b &&& a) tail cost) := by
 simp [EVM.step,stack,binaryPost,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,Stack.push]
 rfl

theorem step_not (s : EVM.State) (fuel cost : Nat) (arg : Option (UInt256 × Nat))
 (a : UInt256) (tail : List UInt256) (stack : s.stack = a::tail) :
 EVM.step (fuel+1) cost (some (.NOT,arg)) s = .ok (binaryPost s (UInt256.lnot a) tail cost) := by
 simp [EVM.step,stack,binaryPost,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,Stack.push]
 rfl

#print axioms of_exact
#print axioms zero_to_exact
#print axioms step_sub
#print axioms step_and
#print axioms step_not
end GolfCountOffset
