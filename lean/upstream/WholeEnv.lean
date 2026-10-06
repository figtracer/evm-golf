import WholeStorage
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unnecessarySeqFocus false
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition

/-! Balances, returned data and block environment reads. -/
namespace GolfWhole

theorem same_basefee : Same .BASEFEE :=
  env_same EvmYul.basefee (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    (fun _ => by simp [H])

theorem same_prevrandao : Same .PREVRANDAO :=
  env_same EvmYul.prevRandao (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    (fun _ => by simp [H])

theorem same_blobbasefee : Same .BLOBBASEFEE :=
  env_same EvmYul.ExecutionEnv.getBlobGasprice (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ => rfl) (fun _ => by simp [H])

theorem same_blobhash : Same .BLOBHASH :=
  same_popn (EVM.unaryExecutionEnvOp blobhash) Stack.pop
    (fun ⟨stk, a⟩ y => y.replaceStackAndIncrPC (stk.push (blobhash y.executionEnv a)))
    (fun _ _ _ _ => rfl)
    (fun y => by unfold EVM.unaryExecutionEnvOp; cases y.stack.pop <;> rfl)
    (fun ⟨_, _⟩ => frameless_rfl) (fun ⟨_, _⟩ _ => rfl)
    (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => by simp [H])

theorem returndatacopy_frameless (a b c : UInt256) (stk : Stack UInt256) :
    Frameless (fun x : State =>
      ({ x with toMachineState := x.toMachineState.returndatacopy a b c } : State).replaceStackAndIncrPC stk) := by
  refine ⟨fun x => ?_, fun x => by simp only [MachineState.returndatacopy, writeBytes]; rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  have m : (E x).toMachineState = { x.toMachineState with gasAvailable := UInt256.ofNat 0 } := rfl
  show E (({ x with toMachineState := x.toMachineState.returndatacopy a b c } : State).replaceStackAndIncrPC stk) =
    E (({ E x with toMachineState := (E x).toMachineState.returndatacopy a b c } : State).replaceStackAndIncrPC stk)
  rw [m]
  simp only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas, EVM.State.replaceStackAndIncrPC,
    EVM.State.incrPC, MachineState.returndatacopy, writeBytes]

theorem same_returndatacopy : Same .RETURNDATACOPY :=
  same_popn (EvmYul.step (.RETURNDATACOPY : Operation .EVM) none) Stack.pop3
    (fun ⟨stk, a, b, c⟩ y =>
      ({ y with toMachineState := y.toMachineState.returndatacopy a b c } : State).replaceStackAndIncrPC stk)
    (fun _ _ _ _ => rfl)
    (fun y => by
      change (match y.stack.pop3 with
        | some ⟨stack', μ₀, μ₁, μ₂⟩ =>
          Except.ok (({ y with toMachineState := y.toMachineState.returndatacopy μ₀ μ₁ μ₂ } : State).replaceStackAndIncrPC stack')
        | _ => .error .StackUnderflow : Except EVM.ExecutionException State) = _
      cases y.stack.pop3 <;> rfl)
    (fun ⟨_, a, b, c⟩ => returndatacopy_frameless a b c _) (fun ⟨_, _, _, _⟩ _ => rfl)
    (fun _ _ h => by
      simp only [C', h, show Operation.Env .RETURNDATACOPY ∈ InstructionGasGroups.Wcopy from by decide,
        if_true])
    (fun _ => rfl) (fun _ => by simp [H])

theorem balance_value {owner old new surplus skipped u u'}
    (h : DeployedOffset owner old new surplus skipped u u') (k : UInt256) :
    (EvmYul.State.balance u'.toState k).2 = (EvmYul.State.balance u.toState k).2 := by
  have m := h.maps.1 (AccountAddress.ofUInt256 k)
  simp only [EvmYul.State.balance]
  change Option.elim (u'.accountMap.find? _) _ _ = Option.elim (u.accountMap.find? _) _ _
  revert m
  cases u.accountMap.find? (AccountAddress.ofUInt256 k) <;>
    cases u'.accountMap.find? (AccountAddress.ofUInt256 k) <;>
    simp [AccountsRelated] <;> intros <;> simp_all

theorem balance_preserves (arg : Option (UInt256 × Nat)) :
    Preserves (EvmYul.step (.BALANCE : Operation .EVM) arg) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  have e : ∀ y : State, EvmYul.step (.BALANCE : Operation .EVM) arg y =
      (match y.stack.pop with
        | some ⟨s, μ₀⟩ =>
          Except.ok (({ y with toState := (EvmYul.State.balance y.toState μ₀).1 } : State).replaceStackAndIncrPC
            (s.push (EvmYul.State.balance y.toState μ₀).2))
        | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := fun _ => rfl
  rw [e] at run ⊢
  rw [←st]
  cases hp : u.stack.pop with
  | none => rw [hp] at run; cases run
  | some p =>
    obtain ⟨stk, a⟩ := p
    rw [hp] at run
    injection run with run
    subst run
    refine ⟨_, rfl, ?_⟩
    rw [balance_value h]
    exact Frameless.preserve
      (F := fun x => ({ x with toState := (EvmYul.State.balance x.toState a).1 } : State).replaceStackAndIncrPC
        (stk.push (EvmYul.State.balance u.toState a).2))
      ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩ h

theorem same_balance : Same .BALANCE :=
  same_rel (fun arg => EvmYul.step (.BALANCE : Operation .EVM) arg) (fun _ _ _ _ => rfl) balance_preserves
    (fun h => (congrArg (fun x => C' x .BALANCE) h.frame).symm)
    (fun arg u v run => by
      have e : EvmYul.step (.BALANCE : Operation .EVM) arg u =
          (match u.stack.pop with
            | some ⟨s, μ₀⟩ =>
              Except.ok (({ u with toState := (EvmYul.State.balance u.toState μ₀).1 } : State).replaceStackAndIncrPC
                (s.push (EvmYul.State.balance u.toState μ₀).2))
            | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := rfl
      simp only [] at run
      rw [e] at run
      cases hp : u.stack.pop with
      | none => rw [hp] at run; cases run
      | some p => obtain ⟨_, _⟩ := p; rw [hp] at run; injection run with run; subst run; rfl)
    (fun arg u v run => by
      have e : EvmYul.step (.BALANCE : Operation .EVM) arg u =
          (match u.stack.pop with
            | some ⟨s, μ₀⟩ =>
              Except.ok (({ u with toState := (EvmYul.State.balance u.toState μ₀).1 } : State).replaceStackAndIncrPC
                (s.push (EvmYul.State.balance u.toState μ₀).2))
            | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := rfl
      simp only [] at run
      rw [e] at run
      cases hp : u.stack.pop with
      | none => rw [hp] at run; cases run
      | some p => obtain ⟨_, _⟩ := p; rw [hp] at run; injection run with run; subst run; rfl)
    (fun _ => by simp [H])

theorem selfbalance_value {owner old new surplus skipped u u'}
    (h : DeployedOffset owner old new surplus skipped u u') :
    EvmYul.State.selfbalance u'.toState = EvmYul.State.selfbalance u.toState := by
  obtain ⟨o, o'⟩ := owner_eq h
  have m := h.maps.1 owner
  simp only [EvmYul.State.selfbalance]
  change Option.elim (u'.accountMap.find? u'.executionEnv.codeOwner) _ _ =
    Option.elim (u.accountMap.find? u.executionEnv.codeOwner) _ _
  rw [o, o']
  revert m
  cases u.accountMap.find? owner <;> cases u'.accountMap.find? owner <;>
    simp [AccountsRelated] <;> intros <;> simp_all

theorem selfbalance_preserves : Preserves (EVM.stateOp EvmYul.State.selfbalance) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  unfold EVM.stateOp at run ⊢
  injection run with run
  subst run
  refine ⟨_, rfl, ?_⟩
  rw [selfbalance_value h, ←st]
  exact (replace_frameless (u.stack.push (EvmYul.State.selfbalance u.toState)) 1).preserve h

theorem same_selfbalance : Same .SELFBALANCE :=
  same_of (fun _ => EVM.stateOp EvmYul.State.selfbalance) (fun _ _ _ _ => rfl)
    (fun _ => selfbalance_preserves) (fun _ _ _ => rfl)
    (fun arg u v run => by unfold EVM.stateOp at run; injection run with run; subst run; rfl)
    (fun arg u v run => by unfold EVM.stateOp at run; injection run with run; subst run; rfl)
    (fun _ => by simp [H])

/-! Code-size reads, congruent when both images have the same size. -/

theorem codesize_at {old new : ByteArray} (h : old.size = new.size) : CongruentAt old new .CODESIZE := by
  refine ⟨fun _ _ _ _ _ => rfl, fun _ => rfl, ?_, ?_⟩
  swap
  · intro f c arg u v enough step
    change EVM.executionEnvOp (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.code) (bump u c) = .ok v at step
    unfold EVM.executionEnvOp at step
    injection step with step
    subst step
    show (bump u c).gasAvailable.toNat ≤ u.gasAvailable.toNat
    rw [bump_gas u c enough]; exact Nat.sub_le _ _
  intro owner surplus skipped u u' v f g c arg rel enough step
  have rb := rel_bump rel c enough
  change EVM.executionEnvOp (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.code) (bump u c) = .ok v at step
  unfold EVM.executionEnvOp at step
  injection step with step
  subst step
  refine ⟨_, rfl, ?_⟩
  have cu : (bump u c).executionEnv.code = old := rel.maps.2.2.1.2.1
  have cu' : (bump u' c).executionEnv.code = new := rel.maps.2.2.2.2.1
  have st := rel_stack rb
  show DeployedOffset owner old new surplus skipped
    ((bump u c).replaceStackAndIncrPC ((bump u c).stack.push (.ofNat (bump u c).executionEnv.code.size)))
    ((bump u' c).replaceStackAndIncrPC ((bump u' c).stack.push (.ofNat (bump u' c).executionEnv.code.size)))
  rw [cu, cu', ← h, ← st]
  exact (replace_frameless _ 1).preserve rb

theorem codesize_adv : Advances .CODESIZE :=
  fun _ _ _ u v run => env_pc (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.code) (bump u _) v run

theorem codesize_run : Running .CODESIZE := fun _ => by simp [H]

theorem extcodesize_value {owner old new surplus skipped u u'} (size : old.size = new.size)
    (h : DeployedOffset owner old new surplus skipped u u') (k : UInt256) :
    (EvmYul.State.extCodeSize u'.toState k).2 = (EvmYul.State.extCodeSize u.toState k).2 := by
  have m := h.maps.1 (AccountAddress.ofUInt256 k)
  simp only [EvmYul.State.extCodeSize, EvmYul.State.lookupAccount]
  revert m
  cases u.accountMap.find? (AccountAddress.ofUInt256 k) <;>
    cases u'.accountMap.find? (AccountAddress.ofUInt256 k) <;>
    simp only [AccountsRelated, Option.option, imp_self, IsEmpty.forall_iff] <;> intro m
  rename_i a a'
  obtain ⟨-, -, -, -, c⟩ := m
  split at c
  · show UInt256.ofNat a'.code.size = UInt256.ofNat a.code.size
    rw [c.1, c.2, size]
  · show UInt256.ofNat a'.code.size = UInt256.ofNat a.code.size
    rw [c]

theorem extcodesize_at {old new : ByteArray} (size : old.size = new.size) :
    CongruentAt old new .EXTCODESIZE := by
  refine ⟨fun _ _ _ _ _ => rfl, fun h => (congrArg (fun x => C' x .EXTCODESIZE) h.frame).symm, ?_, ?_⟩
  swap
  · intro f c arg u v enough step
    have e : EVM.step (f + 1) c (some (.EXTCODESIZE, arg)) u =
        (match (bump u c).stack.pop with
          | some ⟨s, μ₀⟩ =>
            Except.ok (({ bump u c with toState := (EvmYul.State.extCodeSize (bump u c).toState μ₀).1 } : State).replaceStackAndIncrPC
              (s.push (EvmYul.State.extCodeSize (bump u c).toState μ₀).2))
          | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := rfl
    rw [e] at step
    cases hp : (bump u c).stack.pop with
    | none => rw [hp] at step; cases step
    | some p =>
      obtain ⟨_, _⟩ := p
      rw [hp] at step
      injection step with step
      subst step
      show (bump u c).gasAvailable.toNat ≤ u.gasAvailable.toNat
      rw [bump_gas u c enough]; exact Nat.sub_le _ _
  intro owner surplus skipped u u' v f g c arg rel enough step
  have rb := rel_bump rel c enough
  have st := rel_stack rb
  have e : ∀ y : State, EVM.step (f + 1) c (some (.EXTCODESIZE, arg)) y =
      (match (bump y c).stack.pop with
        | some ⟨s, μ₀⟩ =>
          Except.ok (({ bump y c with toState := (EvmYul.State.extCodeSize (bump y c).toState μ₀).1 } : State).replaceStackAndIncrPC
            (s.push (EvmYul.State.extCodeSize (bump y c).toState μ₀).2))
        | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := fun _ => rfl
  have e' : ∀ y : State, EVM.step (g + 1) c (some (.EXTCODESIZE, arg)) y =
      (match (bump y c).stack.pop with
        | some ⟨s, μ₀⟩ =>
          Except.ok (({ bump y c with toState := (EvmYul.State.extCodeSize (bump y c).toState μ₀).1 } : State).replaceStackAndIncrPC
            (s.push (EvmYul.State.extCodeSize (bump y c).toState μ₀).2))
        | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := fun _ => rfl
  rw [e] at step
  rw [e', ← st]
  cases hp : (bump u c).stack.pop with
  | none => rw [hp] at step; cases step
  | some p =>
    obtain ⟨stk, a⟩ := p
    rw [hp] at step
    injection step with step
    subst step
    refine ⟨_, rfl, ?_⟩
    rw [extcodesize_value size rb]
    exact Frameless.preserve
      (F := fun x => ({ x with toState := (EvmYul.State.extCodeSize x.toState a).1 } : State).replaceStackAndIncrPC
        (stk.push (EvmYul.State.extCodeSize (bump u c).toState a).2))
      ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩ rb

theorem extcodesize_adv : Advances .EXTCODESIZE := by
  intro f c arg u v run
  change (match (bump u c).stack.pop with
        | some ⟨s, μ₀⟩ =>
          Except.ok (({ bump u c with toState := (EvmYul.State.extCodeSize (bump u c).toState μ₀).1 } : State).replaceStackAndIncrPC
            (s.push (EvmYul.State.extCodeSize (bump u c).toState μ₀).2))
        | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) = _ at run
  cases hp : (bump u c).stack.pop with
  | none => rw [hp] at run; cases run
  | some p => obtain ⟨_, _⟩ := p; rw [hp] at run; injection run with run; subst run; rfl

theorem extcodesize_run : Running .EXTCODESIZE := fun _ => by simp [H]

/-- Point obligations for an opcode at one pair of images. -/
def SameAt (old new : ByteArray) (op : Operation .EVM) : Prop :=
  CongruentAt old new op ∧ Advances op ∧ Running op

theorem Same.at {op : Operation .EVM} (h : Same op) {old new : ByteArray} : SameAt old new op :=
  ⟨h.1.at, h.2.1, h.2.2⟩

theorem codesize_same {old new : ByteArray} (h : old.size = new.size) : SameAt old new .CODESIZE :=
  ⟨codesize_at h, codesize_adv, codesize_run⟩

theorem extcodesize_same {old new : ByteArray} (h : old.size = new.size) :
    SameAt old new .EXTCODESIZE :=
  ⟨extcodesize_at h, extcodesize_adv, extcodesize_run⟩

#print axioms codesize_same
#print axioms extcodesize_same
#print axioms same_blobhash
#print axioms same_returndatacopy
#print axioms same_balance
#print axioms same_selfbalance

end GolfWhole
