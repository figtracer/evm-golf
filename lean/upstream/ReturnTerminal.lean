import MemorySupport

/-!
Canonical RETURN terminal support at an already established internal boundary.
This reuses pinned EvmYul X/step, MachineState.evmReturn and readWithPadding.
It does not introduce an interpreter or claim whole-contract equivalence.
-/
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition
namespace CanonicalReturn
open CanonicalMemory

-- Match canonical step's opcode charge, binary MachineState dispatch, and PC/count update.
-- evmReturn writes H_return and activeWords; it does not overwrite returnData.
def returnPost (s : EVM.State) (address size : UInt256)
    (tail : List UInt256) (cost : Nat) : EVM.State :=
  let charged := charge s cost
  { charged with
    toMachineState := charged.toMachineState.evmReturn address size
    stack := tail
    pc := s.pc + UInt256.ofNat 1
    execLength := s.execLength + 1 }

@[simp] theorem cost_return (s : EVM.State) : C' s .RETURN = 0 := rfl

theorem step_return (s : EVM.State) (fuel cost : Nat)
    (arg : Option (UInt256 × Nat)) (address size : UInt256)
    (tail : List UInt256) (stack : s.stack = address :: size :: tail) :
    EVM.step (fuel + 1) cost (some (.RETURN, arg)) s =
      .ok (returnPost s address size tail cost) := by
  have specified : { s with stack := address :: size :: tail } = s := by rw [←stack]
  rw [←specified]
  rfl

-- Dynamic expansion is charged by X before step, not folded into opcode cost zero.
def terminalReturn (s : EVM.State) (address size : UInt256)
    (tail : List UInt256) : EVM.State :=
  returnPost (charge s (memoryExpansionCost s .RETURN)) address size tail 0

theorem return_expansion_equal {owner old new surplus skipped s t}
    (related : DeployedOffset owner old new surplus skipped s t) :
    memoryExpansionCost s .RETURN = memoryExpansionCost t .RETURN := by
  have stack := offset_stack related
  have active := congrArg (fun st : EVM.State => st.activeWords) related.frame
  change s.activeWords = t.activeWords at active
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', stack, active]

theorem return_bytes_equal {owner old new surplus skipped s t}
    (related : DeployedOffset owner old new surplus skipped s t)
    (address size : UInt256) :
    s.memory.readWithPadding address.toNat size.toNat =
      t.memory.readWithPadding address.toNat size.toNat := by
  have memory := congrArg (fun st : EVM.State => st.memory) related.frame
  change s.memory = t.memory at memory
  rw [memory]

theorem returnPost_preserves {owner old new surplus skipped s t}
    (related : DeployedOffset owner old new surplus skipped s t)
    (address size : UInt256) (tail : List UInt256) (cost : Nat)
    (small : cost < UInt256.size) (enough : cost ≤ s.gasAvailable.toNat) :
    DeployedOffset owner old new surplus skipped
      (returnPost s address size tail cost) (returnPost t address size tail cost) := by
  refine ⟨?_, ?_, ?_, related.maps⟩
  · have h := congrArg (fun st : EVM.State => returnPost st address size tail cost) related.frame
    simpa only [returnPost, charge, eraseCount, deployedFrame, eraseMaps,
      eraseCodeGas, MachineState.evmReturn] using
      congrArg (fun st : EVM.State => eraseCount (deployedFrame st)) h
  · change s.execLength + 1 = (t.execLength + 1) + skipped
    have := related.count
    omega
  · exact gas_preservation s.gasAvailable t.gasAvailable cost surplus small enough related.gas

theorem terminalReturn_gas (s : EVM.State) (address size : UInt256)
    (tail : List UInt256)
    (enough : memoryExpansionCost s .RETURN ≤ s.gasAvailable.toNat) :
    (terminalReturn s address size tail).gasAvailable.toNat =
      s.gasAvailable.toNat - memoryExpansionCost s .RETURN := by
  have wordBound : s.gasAvailable.toNat < UInt256.size := s.gasAvailable.val.isLt
  have small : memoryExpansionCost s .RETURN < UInt256.size := by omega
  change ((s.gasAvailable - UInt256.ofNat (memoryExpansionCost s .RETURN)) -
    UInt256.ofNat 0).toNat = _
  rw [word_sub_zero, word_sub_toNat _ _ small enough]

theorem terminalReturn_count (s : EVM.State) (address size : UInt256)
    (tail : List UInt256) :
    (terminalReturn s address size tail).execLength = s.execLength + 1 := rfl

theorem terminalReturn_output (s : EVM.State) (address size : UInt256)
    (tail : List UInt256) :
    (terminalReturn s address size tail).H_return =
      s.memory.readWithPadding address.toNat size.toNat := rfl

theorem terminalReturn_returnData (s : EVM.State) (address size : UInt256)
    (tail : List UInt256) :
    (terminalReturn s address size tail).returnData = s.returnData := rfl

/-- Terminal success under canonical X, not merely successful single-step evaluation.
`readable` excludes readWithPadding's pinned host-size panic branch. The equality
itself is phrased with the canonical reader, rather than an invented byte model.
The full incoming stack bound is deliberately stronger than X's post-pop check. -/
theorem X_return (s : EVM.State) (fuel : Nat) (jumps : Array UInt256)
    (address size : UInt256) (tail : List UInt256)
    (decoded : decode s.executionEnv.code s.pc = some (.RETURN, none))
    (stack : s.stack = address :: size :: tail)
    (gas : memoryExpansionCost s .RETURN ≤ s.gasAvailable.toNat)
    (physical : s.stack.length ≤ 1024)
    (_readable : size.toNat < 2^64) :
    X (fuel + 2) jumps s = .ok (.success
      (terminalReturn s address size tail)
      (s.memory.readWithPadding address.toNat size.toNat)) := by
  have noExpansion : ¬s.gasAvailable.toNat < memoryExpansionCost s .RETURN :=
    Nat.not_lt.mpr gas
  have noInputs : ¬s.stack.length < 2 := by simp [stack]
  have noOutputs : ¬1024 < s.stack.length - 2 := by omega
  conv_lhs => unfold X
  simp only [decoded]
  simp [noExpansion, cost_return, Operation.isCreate, δ, α, noInputs, noOutputs]
  change (do
    let next ← EVM.step (fuel + 1) 0 (some (.RETURN, none))
      (charge s (memoryExpansionCost s .RETURN))
    pure (ExecutionResult.success next next.H_return)) = _
  rw [step_return (charge s (memoryExpansionCost s .RETURN)) fuel 0 none
    address size tail stack]
  rfl

/-- At a RETURN boundary, the deployed offset relation transports the canonical
terminal success, identical returned bytes, and the unchanged gas/count offsets.
Source and target may use different code images, jump arrays, and sufficient fuels. -/
theorem return_pair {owner old new surplus skipped s t}
    (related : DeployedOffset owner old new surplus skipped s t)
    (address size : UInt256) (tail : List UInt256)
    (sourceFuel targetFuel : Nat) (oldJumps newJumps : Array UInt256)
    (sourceDecode : decode s.executionEnv.code s.pc = some (.RETURN, none))
    (targetDecode : decode t.executionEnv.code t.pc = some (.RETURN, none))
    (stack : s.stack = address :: size :: tail)
    (gas : memoryExpansionCost s .RETURN ≤ s.gasAvailable.toNat)
    (physical : s.stack.length ≤ 1024)
    (readable : size.toNat < 2^64) :
    X (sourceFuel + 2) oldJumps s = .ok (.success
      (terminalReturn s address size tail)
      (s.memory.readWithPadding address.toNat size.toNat)) ∧
    X (targetFuel + 2) newJumps t = .ok (.success
      (terminalReturn t address size tail)
      (s.memory.readWithPadding address.toNat size.toNat)) ∧
    DeployedOffset owner old new surplus skipped
      (terminalReturn s address size tail) (terminalReturn t address size tail) := by
  have sameExpansion := return_expansion_equal related
  have targetGas : memoryExpansionCost t .RETURN ≤ t.gasAvailable.toNat := by
    rw [←sameExpansion]
    have := related.gas
    omega
  have targetStack : t.stack = address :: size :: tail :=
    (offset_stack related).symm.trans stack
  have targetPhysical : t.stack.length ≤ 1024 := by
    rw [←offset_stack related]
    exact physical
  have wordBound : s.gasAvailable.toNat < UInt256.size := s.gasAvailable.val.isLt
  have small : memoryExpansionCost s .RETURN < UInt256.size := by omega
  have charged := charge_preserves related (memoryExpansionCost s .RETURN) small gas
  have nextRelated := returnPost_preserves charged address size tail 0 (by decide) (by omega)
  refine ⟨X_return s sourceFuel oldJumps address size tail sourceDecode stack gas physical readable,
    ?_, ?_⟩
  · rw [return_bytes_equal related address size]
    exact X_return t targetFuel newJumps address size tail targetDecode targetStack
      targetGas targetPhysical readable
  · simpa only [terminalReturn, ←sameExpansion] using nextRelated

#print axioms cost_return
#print axioms step_return
#print axioms return_expansion_equal
#print axioms return_bytes_equal
#print axioms returnPost_preserves
#print axioms terminalReturn_gas
#print axioms terminalReturn_count
#print axioms terminalReturn_output
#print axioms terminalReturn_returnData
#print axioms X_return
#print axioms return_pair
end CanonicalReturn
