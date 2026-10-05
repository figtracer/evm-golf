import OffsetTransport
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition CanonicalMaskWindow
namespace CanonicalMemory

def charge (s : EVM.State) (cost : Nat) : EVM.State :=
 {s with gasAvailable := s.gasAvailable - UInt256.ofNat cost}

-- This is the canonical MachineState.mstore, not a separate memory evaluator.
def storePost (s : EVM.State) (address value : UInt256) (tail : List UInt256) (cost : Nat) : EVM.State :=
 let charged := charge s cost
 {charged with
  toMachineState := charged.toMachineState.mstore address value
  stack := tail
  pc := s.pc + UInt256.ofNat 1
  execLength := s.execLength + 1}

@[simp] theorem cost_mstore (s : EVM.State) : C' s .MSTORE = 3 := rfl

theorem step_mstore (s : EVM.State) (fuel cost : Nat) (arg : Option (UInt256 × Nat))
 (address value : UInt256) (tail : List UInt256) (stack : s.stack = address::value::tail) :
 EVM.step (fuel+1) cost (some (.MSTORE,arg)) s = .ok (storePost s address value tail cost) := by
 have specified : {s with stack := address::value::tail} = s := by rw [←stack]
 rw [←specified]
 rfl

theorem charge_preserves {owner old new surplus skipped s t}
 (related : DeployedOffset owner old new surplus skipped s t) (cost : Nat)
 (small : cost < UInt256.size) (enough : cost ≤ s.gasAvailable.toNat) :
 DeployedOffset owner old new surplus skipped (charge s cost) (charge t cost) := by
 refine ⟨?_,related.count,?_,related.maps⟩
 · simpa only [charge,eraseCount,deployedFrame,eraseMaps,eraseCodeGas] using related.frame
 · exact gas_preservation s.gasAvailable t.gasAvailable cost surplus small enough related.gas

theorem expansion_equal {owner old new surplus skipped s t}
 (related : DeployedOffset owner old new surplus skipped s t) :
 memoryExpansionCost s .MSTORE = memoryExpansionCost t .MSTORE := by
 have stack := offset_stack related
 have active := congrArg (fun st : EVM.State => st.activeWords) related.frame
 change s.activeWords = t.activeWords at active
 simp only [memoryExpansionCost,memoryExpansionCost.μᵢ',stack,active]

theorem store_preserves {owner old new surplus skipped s t}
 (related : DeployedOffset owner old new surplus skipped s t)
 (address value : UInt256) (tail : List UInt256) (cost : Nat)
 (small : cost < UInt256.size) (enough : cost ≤ s.gasAvailable.toNat) :
 DeployedOffset owner old new surplus skipped
   (storePost s address value tail cost) (storePost t address value tail cost) := by
 refine ⟨?_,?_,?_,related.maps⟩
 · have h := congrArg (fun st : EVM.State => storePost st address value tail cost) related.frame
   simpa only [storePost,charge,eraseCount,deployedFrame,eraseMaps,eraseCodeGas,
     MachineState.mstore,MachineState.writeWord,writeBytes] using
     congrArg (fun st : EVM.State => eraseCount (deployedFrame st)) h
 · change s.execLength+1 = (t.execLength+1)+skipped
   have := related.count
   omega
 · exact gas_preservation s.gasAvailable t.gasAvailable cost surplus small enough related.gas

-- Expansion is charged before the opcode, exactly as canonical X does.
theorem expansion_charge_bounds (s : EVM.State)
 (gas : memoryExpansionCost s .MSTORE + 3 ≤ s.gasAvailable.toNat) :
 memoryExpansionCost s .MSTORE < UInt256.size ∧
 3 ≤ (charge s (memoryExpansionCost s .MSTORE)).gasAvailable.toNat := by
 have wordBound : s.gasAvailable.toNat < UInt256.size := s.gasAvailable.val.isLt
 have small : memoryExpansionCost s .MSTORE < UInt256.size := by omega
 refine ⟨small,?_⟩
 change 3 ≤ (s.gasAvailable - UInt256.ofNat (memoryExpansionCost s .MSTORE)).toNat
 rw [word_sub_toNat _ _ small (by omega)]
 omega

#print axioms step_mstore
#print axioms charge_preserves
#print axioms expansion_equal
#print axioms store_preserves
#print axioms expansion_charge_bounds
end CanonicalMemory
