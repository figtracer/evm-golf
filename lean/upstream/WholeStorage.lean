import WholeProgram
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unnecessarySeqFocus false
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition

/-! Storage, transient storage, logs, hashing and remaining memory reads. -/
namespace GolfWhole

theorem owner_related {owner old new surplus skipped u u'}
    (h : DeployedOffset owner old new surplus skipped u u') :
    (u.accountMap.find? owner).map (fun a => (a.storage, a.tstorage)) =
      (u'.accountMap.find? owner).map (fun a => (a.storage, a.tstorage)) ∧
    (u.σ₀.find? owner).map (fun a => a.storage) = (u'.σ₀.find? owner).map (fun a => a.storage) := by
  have m := h.maps.1 owner
  have o := h.maps.2.1 owner
  constructor
  · revert m
    cases u.accountMap.find? owner <;> cases u'.accountMap.find? owner <;>
      simp [AccountsRelated] <;> intros <;> simp_all
  · revert o
    cases u.σ₀.find? owner <;> cases u'.σ₀.find? owner <;>
      simp [AccountsRelated] <;> intros <;> simp_all

theorem owner_eq {owner old new surplus skipped u u'}
    (h : DeployedOffset owner old new surplus skipped u u') :
    u.executionEnv.codeOwner = owner ∧ u'.executionEnv.codeOwner = owner :=
  ⟨h.maps.2.2.1.1, h.maps.2.2.2.1⟩

theorem sload_value {owner old new surplus skipped u u'}
    (h : DeployedOffset owner old new surplus skipped u u') (k : UInt256) :
    (EvmYul.State.sload u'.toState k).2 = (EvmYul.State.sload u.toState k).2 := by
  obtain ⟨o, o'⟩ := owner_eq h
  have r := (owner_related h).1
  simp only [EvmYul.State.sload, EvmYul.State.lookupAccount]
  change Option.option _ _ (u'.accountMap.find? u'.executionEnv.codeOwner) =
    Option.option _ _ (u.accountMap.find? u.executionEnv.codeOwner)
  rw [o, o']
  revert r
  cases u.accountMap.find? owner <;> cases u'.accountMap.find? owner <;>
    simp [Option.option, Account.lookupStorage] <;> intros <;> simp_all

theorem tload_value {owner old new surplus skipped u u'}
    (h : DeployedOffset owner old new surplus skipped u u') (k : UInt256) :
    (EvmYul.State.tload u'.toState k).2 = (EvmYul.State.tload u.toState k).2 := by
  obtain ⟨o, o'⟩ := owner_eq h
  have r := (owner_related h).1
  simp only [EvmYul.State.tload, EvmYul.State.lookupAccount]
  change Option.option _ _ (u'.accountMap.find? u'.executionEnv.codeOwner) =
    Option.option _ _ (u.accountMap.find? u.executionEnv.codeOwner)
  rw [o, o']
  revert r
  cases u.accountMap.find? owner <;> cases u'.accountMap.find? owner <;>
    simp [Option.option, Account.lookupTransientStorage] <;> intros <;> simp_all

theorem sload_preserves (arg : Option (UInt256 × Nat)) :
    Preserves (EvmYul.step (.SLOAD : Operation .EVM) arg) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  have e : ∀ y : State, EvmYul.step (.SLOAD : Operation .EVM) arg y =
      (match y.stack.pop with
        | some ⟨s, μ₀⟩ =>
          Except.ok (({ y with toState := (EvmYul.State.sload y.toState μ₀).1 } : State).replaceStackAndIncrPC
            (s.push (EvmYul.State.sload y.toState μ₀).2))
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
    rw [sload_value h]
    exact Frameless.preserve
      (F := fun x => ({ x with toState := (EvmYul.State.sload x.toState a).1 } : State).replaceStackAndIncrPC
        (stk.push (EvmYul.State.sload u.toState a).2))
      ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩ h

theorem tload_preserves (arg : Option (UInt256 × Nat)) :
    Preserves (EvmYul.step (.TLOAD : Operation .EVM) arg) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  have e : ∀ y : State, EvmYul.step (.TLOAD : Operation .EVM) arg y =
      (match y.stack.pop with
        | some ⟨s, μ₀⟩ =>
          Except.ok (({ y with toState := (EvmYul.State.tload y.toState μ₀).1 } : State).replaceStackAndIncrPC
            (s.push (EvmYul.State.tload y.toState μ₀).2))
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
    rw [tload_value h]
    exact Frameless.preserve
      (F := fun x => ({ x with toState := (EvmYul.State.tload x.toState a).1 } : State).replaceStackAndIncrPC
        (stk.push (EvmYul.State.tload u.toState a).2))
      ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩ h


theorem sstore_substate (x y : EvmYul.State .EVM) (a b : UInt256) (o : AccountAddress)
    (hx : x.executionEnv.codeOwner = o) (hy : y.executionEnv.codeOwner = o)
    (hsub : x.substate = y.substate)
    (hst : (x.accountMap.find? o).map (fun a => (a.storage, a.tstorage)) =
      (y.accountMap.find? o).map (fun a => (a.storage, a.tstorage)))
    (h0 : (x.σ₀.find? o).map (fun a => a.storage) = (y.σ₀.find? o).map (fun a => a.storage)) :
    (EvmYul.State.sstore x a b).substate = (EvmYul.State.sstore y a b).substate := by
  unfold EvmYul.State.sstore EvmYul.State.lookupAccount
  simp only [hx, hy]
  revert hst h0
  cases h1 : x.σ₀.find? o <;> cases h2 : y.σ₀.find? o <;>
    cases h3 : x.accountMap.find? o <;> cases h4 : y.accountMap.find? o <;>
    simp [Option.option, Batteries.RBMap.find!, EvmYul.State.addAccessedStorageKey,
      EvmYul.State.setAccount, hsub, h1, h2, h3, h4] <;> intros <;> simp_all


theorem sstore_accounts (x : EvmYul.State .EVM) (a b : UInt256) (o : AccountAddress)
    (hx : x.executionEnv.codeOwner = o) :
    (EvmYul.State.sstore x a b).accountMap = (match x.accountMap.find? o with
      | none => x.accountMap
      | some acc => x.accountMap.insert o (acc.updateStorage a b)) ∧
    (EvmYul.State.sstore x a b).σ₀ = x.σ₀ ∧
    (EvmYul.State.sstore x a b).executionEnv = x.executionEnv := by
  unfold EvmYul.State.sstore EvmYul.State.lookupAccount
  simp only [hx]
  cases x.accountMap.find? o <;>
    simp [Option.option, EvmYul.State.addAccessedStorageKey, EvmYul.State.setAccount]

theorem update_related (owner addr : AccountAddress) (old new : ByteArray) (acc acc' : Account .EVM)
    (a b : UInt256) (h : AccountsRelated owner addr old new acc acc') :
    AccountsRelated owner addr old new (acc.updateStorage a b) (acc'.updateStorage a b) := by
  unfold AccountsRelated at h ⊢
  obtain ⟨n, bal, st, ts, c⟩ := h
  unfold Account.updateStorage
  split <;> simp_all

theorem maps_insert (owner : AccountAddress) (old new : ByteArray) (m m' : AccountMap .EVM)
    (A A' : Account .EVM) (rel : MapsRelated owner old new m m')
    (hA : AccountsRelated owner owner old new A A') :
    MapsRelated owner old new (m.insert owner A) (m'.insert owner A') := by
  intro addr
  rw [Batteries.RBMap.find?_insert, Batteries.RBMap.find?_insert]
  by_cases e : compare addr owner = .eq
  · rw [if_pos e, if_pos e]
    have : addr = owner := compare_eq_iff_eq.mp e
    subst this
    exact hA
  · rw [if_neg e, if_neg e]
    exact rel addr


theorem sstore_shape (x : EvmYul.State .EVM) (a b : UInt256) :
    EvmYul.State.sstore x a b = { x with
      accountMap := (EvmYul.State.sstore x a b).accountMap
      substate := (EvmYul.State.sstore x a b).substate } := by
  unfold EvmYul.State.sstore EvmYul.State.lookupAccount
  cases h : x.accountMap.find? x.executionEnv.codeOwner <;>
    simp [h, Option.option, EvmYul.State.addAccessedStorageKey, EvmYul.State.setAccount]

theorem linked_insert (owner : AccountAddress) (code : ByteArray) (s : State)
    (m : AccountMap .EVM) (acc : Account .EVM) (a b : UInt256)
    (link : Linked owner code s) (found : s.accountMap.find? owner = some acc)
    (hm : m = s.accountMap.insert owner (acc.updateStorage a b)) (t : State)
    (ht : t.accountMap = m) (h0 : t.σ₀ = s.σ₀) (he : t.executionEnv = s.executionEnv) :
    Linked owner code t := by
  obtain ⟨o, c, ⟨a1, f1, c1⟩, ⟨a2, f2, c2⟩⟩ := link
  rw [found] at f1
  cases f1
  refine ⟨by rw [he]; exact o, by rw [he]; exact c, ⟨acc.updateStorage a b, ?_, ?_⟩, ⟨a2, by rw [h0]; exact f2, c2⟩⟩
  · rw [ht, hm, Batteries.RBMap.find?_insert, if_pos (compare_eq_iff_eq.mpr rfl)]
  · unfold Account.updateStorage; split <;> exact c1

theorem sstore_preserves (arg : Option (UInt256 × Nat)) :
    Preserves (EvmYul.step (.SSTORE : Operation .EVM) arg) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  obtain ⟨o, o'⟩ := owner_eq h
  have e : ∀ y : State, EvmYul.step (.SSTORE : Operation .EVM) arg y =
      (match y.stack.pop2 with
        | some ⟨s, μ₀, μ₁⟩ =>
          Except.ok (({ y with toState := EvmYul.State.sstore y.toState μ₀ μ₁ } : State).replaceStackAndIncrPC s)
        | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := fun _ => rfl
  rw [e] at run ⊢
  rw [←st]
  cases hp : u.stack.pop2 with
  | none => rw [hp] at run; cases run
  | some p =>
    obtain ⟨stk, a, b⟩ := p
    rw [hp] at run
    injection run with run
    subst run
    refine ⟨_, rfl, ?_⟩
    have sub : u.substate = u'.substate := by
      simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
        congrArg (fun x : State => x.substate) h.frame
    have S := sstore_substate u.toState u'.toState a b owner o o' sub
      (owner_related h).1 (owner_related h).2
    have G : Frameless (fun x => ({ x with toState := { x.toState with
        substate := (EvmYul.State.sstore u.toState a b).substate } } : State).replaceStackAndIncrPC stk) :=
      ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
    have g := G.preserve h
    have A := sstore_accounts u.toState a b owner o
    have A' := sstore_accounts u'.toState a b owner o'
    refine ⟨?_, g.count, g.gas, ?_⟩
    · have l : E (({ u with toState := EvmYul.State.sstore u.toState a b } : State).replaceStackAndIncrPC stk) =
          E (({ u with toState := { u.toState with
            substate := (EvmYul.State.sstore u.toState a b).substate } } : State).replaceStackAndIncrPC stk) := by
        rw [sstore_shape u.toState a b]; rfl
      have r : E (({ u' with toState := EvmYul.State.sstore u'.toState a b } : State).replaceStackAndIncrPC stk) =
          E (({ u' with toState := { u'.toState with
            substate := (EvmYul.State.sstore u.toState a b).substate } } : State).replaceStackAndIncrPC stk) := by
        rw [sstore_shape u'.toState a b, ←S]; rfl
      exact l.trans (g.frame.trans r.symm)
    · have m := h.maps
      have rel := m.1 owner
      refine ⟨?_, ?_, ?_, ?_⟩
      · change MapsRelated owner old new (EvmYul.State.sstore u.toState a b).accountMap
          (EvmYul.State.sstore u'.toState a b).accountMap
        rw [A.1, A'.1]
        revert rel
        cases f : u.accountMap.find? owner <;> cases f' : u'.accountMap.find? owner <;>
          simp only [] <;> intro rel
        · exact m.1
        · exact False.elim rel
        · exact False.elim rel
        · exact maps_insert owner old new _ _ _ _ m.1 (update_related _ _ _ _ _ _ a b rel)
      · change MapsRelated owner old new (EvmYul.State.sstore u.toState a b).σ₀
          (EvmYul.State.sstore u'.toState a b).σ₀
        rw [A.2.1, A'.2.1]; exact m.2.1
      · obtain ⟨_, _, ⟨acc, f, _⟩, _⟩ := m.2.2.1
        have A1 : (EvmYul.State.sstore u.toState a b).accountMap =
            u.accountMap.insert owner (acc.updateStorage a b) := by
          rw [A.1]; simp only [f]
        exact linked_insert owner old u _ acc a b m.2.2.1 f rfl _ A1 A.2.1 A.2.2
      · obtain ⟨_, _, ⟨acc, f, _⟩, _⟩ := m.2.2.2
        have A1 : (EvmYul.State.sstore u'.toState a b).accountMap =
            u'.accountMap.insert owner (acc.updateStorage a b) := by
          rw [A'.1]; simp only [f]
        exact linked_insert owner new u' _ acc a b m.2.2.2 f rfl _ A1 A'.2.1 A'.2.2


theorem popn_preserves {β : Type} (T : State → Except EVM.ExecutionException State)
    (pop : Stack UInt256 → Option β) (G : β → State → State)
    (hT : ∀ y, T y = match pop y.stack with
      | some p => .ok (G p y)
      | none => .error .StackUnderflow)
    (hG : ∀ p, Frameless (G p)) : Preserves T := by
  intro owner old new surplus skipped u u' v h run
  rw [hT] at run ⊢
  rw [←rel_stack h]
  cases hp : pop u.stack with
  | none => rw [hp] at run; cases run
  | some p =>
    rw [hp] at run
    injection run with run
    subst run
    exact ⟨_, rfl, (hG p).preserve h⟩

theorem popn_pc {β : Type} (T : State → Except EVM.ExecutionException State)
    (pop : Stack UInt256 → Option β) (G : β → State → State)
    (hT : ∀ y, T y = match pop y.stack with
      | some p => .ok (G p y)
      | none => .error .StackUnderflow)
    (hpc : ∀ p y, (G p y).pc = y.pc + UInt256.ofNat 1) (u v : State) (run : T u = .ok v) :
    v.pc = u.pc + UInt256.ofNat 1 := by
  rw [hT] at run
  cases hp : pop u.stack with
  | none => rw [hp] at run; cases run
  | some p => rw [hp] at run; injection run with run; subst run; exact hpc p u

theorem popn_gas {β : Type} (T : State → Except EVM.ExecutionException State)
    (pop : Stack UInt256 → Option β) (G : β → State → State)
    (hT : ∀ y, T y = match pop y.stack with
      | some p => .ok (G p y)
      | none => .error .StackUnderflow)
    (hG : ∀ p, Frameless (G p)) (u v : State) (run : T u = .ok v) : v.gasAvailable = u.gasAvailable := by
  rw [hT] at run
  cases hp : pop u.stack with
  | none => rw [hp] at run; cases run
  | some p => rw [hp] at run; injection run with run; subst run; exact (hG p).gas u

/-- A popping instruction whose post-state map ignores code, gas, maps and counts. -/
theorem same_popn {op : Operation .EVM} {β : Type} (T : State → Except EVM.ExecutionException State)
    (pop : Stack UInt256 → Option β) (G : β → State → State)
    (hstep : ∀ f c arg u, EVM.step (f + 1) c (some (op, arg)) u = T (bump u c))
    (hT : ∀ y, T y = match pop y.stack with
      | some p => .ok (G p y)
      | none => .error .StackUnderflow)
    (hG : ∀ p, Frameless (G p)) (hpc : ∀ p y, (G p y).pc = y.pc + UInt256.ofNat 1)
    (hcost : ∀ s t : State, s.stack = t.stack → C' t op = C' s op)
    (adv : ∀ arg, advance op arg = 1) (run : Running op) : Same op :=
  same_of (fun _ => T) hstep (fun _ => popn_preserves T pop G hT hG) hcost
    (fun _ u v h => popn_gas T pop G hT hG u v h)
    (fun arg u v h => by rw [adv]; exact popn_pc T pop G hT hpc u v h) run

macro "frameless_rfl" : term =>
  `(⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩)

theorem same_log0 : Same .LOG0 :=
  same_popn EVM.log0Op Stack.pop2
    (fun ⟨stk, a, b⟩ y =>
      ({ y with toSharedState := SharedState.logOp a b #[] y.toSharedState } : State).replaceStackAndIncrPC stk)
    (fun _ _ _ _ => rfl) (fun y => by unfold EVM.log0Op; cases y.stack.pop2 <;> rfl)
    (fun ⟨_, _, _⟩ => frameless_rfl) (fun ⟨_, _, _⟩ _ => rfl)
    (fun _ _ h => by simp only [C', h]) (fun _ => rfl) (fun _ => by simp [H])


theorem same_log1 : Same .LOG1 :=
  same_popn EVM.log1Op Stack.pop3
    (fun ⟨stk, a, b, c⟩ y =>
      ({ y with toSharedState := SharedState.logOp a b #[c] y.toSharedState } : State).replaceStackAndIncrPC stk)
    (fun _ _ _ _ => rfl) (fun y => by unfold EVM.log1Op; cases y.stack.pop3 <;> rfl)
    (fun ⟨_, _, _, _⟩ => frameless_rfl) (fun ⟨_, _, _, _⟩ _ => rfl)
    (fun _ _ h => by simp only [C', h]) (fun _ => rfl) (fun _ => by simp [H])

theorem same_log2 : Same .LOG2 :=
  same_popn EVM.log2Op Stack.pop4
    (fun ⟨stk, a, b, c, d⟩ y =>
      ({ y with toSharedState := SharedState.logOp a b #[c, d] y.toSharedState } : State).replaceStackAndIncrPC stk)
    (fun _ _ _ _ => rfl) (fun y => by unfold EVM.log2Op; cases y.stack.pop4 <;> rfl)
    (fun ⟨_, _, _, _, _⟩ => frameless_rfl) (fun ⟨_, _, _, _, _⟩ _ => rfl)
    (fun _ _ h => by simp only [C', h]) (fun _ => rfl) (fun _ => by simp [H])

theorem same_log3 : Same .LOG3 :=
  same_popn EVM.log3Op Stack.pop5
    (fun ⟨stk, a, b, c, d, e⟩ y =>
      ({ y with toSharedState := SharedState.logOp a b #[c, d, e] y.toSharedState } : State).replaceStackAndIncrPC stk)
    (fun _ _ _ _ => rfl) (fun y => by unfold EVM.log3Op; cases y.stack.pop5 <;> rfl)
    (fun ⟨_, _, _, _, _, _⟩ => frameless_rfl) (fun ⟨_, _, _, _, _, _⟩ _ => rfl)
    (fun _ _ h => by simp only [C', h]) (fun _ => rfl) (fun _ => by simp [H])

theorem same_log4 : Same .LOG4 :=
  same_popn EVM.log4Op Stack.pop6
    (fun ⟨stk, a, b, c, d, e, f⟩ y =>
      ({ y with toSharedState := SharedState.logOp a b #[c, d, e, f] y.toSharedState } : State).replaceStackAndIncrPC stk)
    (fun _ _ _ _ => rfl) (fun y => by unfold EVM.log4Op; cases y.stack.pop6 <;> rfl)
    (fun ⟨_, _, _, _, _, _, _⟩ => frameless_rfl) (fun ⟨_, _, _, _, _, _, _⟩ _ => rfl)
    (fun _ _ h => by simp only [C', h]) (fun _ => rfl) (fun _ => by simp [H])

theorem same_keccak256 : Same .KECCAK256 :=
  same_popn (EVM.binaryMachineStateOp' MachineState.keccak256) Stack.pop2
    (fun ⟨stk, a, b⟩ y =>
      ({ y with toMachineState := (y.toMachineState.keccak256 a b).2 } : State).replaceStackAndIncrPC
        (stk.push (y.toMachineState.keccak256 a b).1))
    (fun _ _ _ _ => rfl)
    (fun y => by unfold EVM.binaryMachineStateOp'; cases y.stack.pop2 <;> rfl)
    (fun ⟨_, _, _⟩ => frameless_rfl) (fun ⟨_, _, _⟩ _ => rfl)
    (fun _ _ h => by simp only [C', h]) (fun _ => rfl) (fun _ => by simp [H])

theorem same_calldatacopy : Same .CALLDATACOPY :=
  same_popn (EVM.ternaryCopyOp SharedState.calldatacopy) Stack.pop3
    (fun ⟨stk, a, b, c⟩ y =>
      ({ y with toSharedState := y.toSharedState.calldatacopy a b c } : State).replaceStackAndIncrPC stk)
    (fun _ _ _ _ => rfl)
    (fun y => by unfold EVM.ternaryCopyOp; cases y.stack.pop3 <;> rfl)
    (fun ⟨_, _, _, _⟩ => frameless_rfl) (fun ⟨_, _, _, _⟩ _ => rfl)
    (fun _ _ h => by
      simp only [C', h, show Operation.Env .CALLDATACOPY ∈ InstructionGasGroups.Wcopy from by decide,
        if_true])
    (fun _ => rfl) (fun _ => by simp [H])

theorem same_msize : Same .MSIZE :=
  same_popn (EVM.machineStateOp MachineState.msize) some
    (fun stk y => y.replaceStackAndIncrPC (stk.push y.toMachineState.msize))
    (fun _ _ _ _ => rfl) (fun _ => rfl) (fun _ => frameless_rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => by simp [H])

theorem same_returndatasize : Same .RETURNDATASIZE :=
  same_popn (EVM.machineStateOp MachineState.returndatasize) some
    (fun stk y => y.replaceStackAndIncrPC (stk.push y.toMachineState.returndatasize))
    (fun _ _ _ _ => rfl) (fun _ => rfl) (fun _ => frameless_rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => by simp [H])


theorem same_rel {op : Operation .EVM}
    (T : Option (UInt256 × Nat) → State → Except EVM.ExecutionException State)
    (hstep : ∀ f c arg u, EVM.step (f + 1) c (some (op, arg)) u = T arg (bump u c))
    (hT : ∀ arg, Preserves (T arg))
    (hcost : ∀ {owner old new surplus skipped s t},
      DeployedOffset owner old new surplus skipped s t → C' t op = C' s op)
    (hgas : ∀ arg u v, T arg u = .ok v → v.gasAvailable = u.gasAvailable)
    (hpc : ∀ arg u v, T arg u = .ok v → v.pc = u.pc + UInt256.ofNat (advance op arg))
    (run : Running op) : Same op := by
  refine ⟨⟨fun f g c arg u => by rw [hstep, hstep], hcost, ?_, ?_⟩, advances_of T hstep hpc, run⟩
  · intro owner old new surplus skipped u u' v f g c arg h enough step
    rw [hstep] at step
    obtain ⟨v', step', rel⟩ := hT arg (rel_bump h c enough) step
    exact ⟨v', by rw [hstep]; exact step', rel⟩
  · intro f c arg u v enough run
    rw [hstep] at run
    rw [hgas arg _ v run, bump_gas u c enough]
    exact Nat.sub_le _ _

theorem csstore_rel {owner old new surplus skipped s t}
    (h : DeployedOffset owner old new surplus skipped s t) : C' t .SSTORE = C' s .SSTORE := by
  obtain ⟨o, o'⟩ := owner_eq h
  have st := rel_stack h
  have sub : s.substate = t.substate := by
    simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
      congrArg (fun x : State => x.substate) h.frame
  have r := owner_related h
  simp only [C', Csstore]
  rw [o, o', st, sub]
  revert r
  cases h1 : s.σ₀.find? owner <;> cases h2 : t.σ₀.find? owner <;>
    cases h3 : s.accountMap.find? owner <;> cases h4 : t.accountMap.find? owner <;>
    simp [Batteries.RBMap.find!, h3, h4] <;> intros <;> simp_all

theorem same_sload : Same .SLOAD :=
  same_rel (fun arg => EvmYul.step (.SLOAD : Operation .EVM) arg) (fun _ _ _ _ => rfl) sload_preserves
    (fun h => (congrArg (fun x => C' x .SLOAD) h.frame).symm)
    (fun arg u v run => by
      have e : EvmYul.step (.SLOAD : Operation .EVM) arg u =
          (match u.stack.pop with
            | some ⟨s, μ₀⟩ =>
              Except.ok (({ u with toState := (EvmYul.State.sload u.toState μ₀).1 } : State).replaceStackAndIncrPC
                (s.push (EvmYul.State.sload u.toState μ₀).2))
            | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := rfl
      simp only [] at run
      rw [e] at run
      cases hp : u.stack.pop with
      | none => rw [hp] at run; cases run
      | some p => obtain ⟨_, _⟩ := p; rw [hp] at run; injection run with run; subst run; rfl)
    (fun arg u v run => by
      have e : EvmYul.step (.SLOAD : Operation .EVM) arg u =
          (match u.stack.pop with
            | some ⟨s, μ₀⟩ =>
              Except.ok (({ u with toState := (EvmYul.State.sload u.toState μ₀).1 } : State).replaceStackAndIncrPC
                (s.push (EvmYul.State.sload u.toState μ₀).2))
            | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := rfl
      simp only [] at run
      rw [e] at run
      cases hp : u.stack.pop with
      | none => rw [hp] at run; cases run
      | some p => obtain ⟨_, _⟩ := p; rw [hp] at run; injection run with run; subst run; rfl)
    (fun _ => by simp [H])

theorem same_tload : Same .TLOAD :=
  same_rel (fun arg => EvmYul.step (.TLOAD : Operation .EVM) arg) (fun _ _ _ _ => rfl) tload_preserves
    (fun _ => rfl)
    (fun arg u v run => by
      have e : EvmYul.step (.TLOAD : Operation .EVM) arg u =
          (match u.stack.pop with
            | some ⟨s, μ₀⟩ =>
              Except.ok (({ u with toState := (EvmYul.State.tload u.toState μ₀).1 } : State).replaceStackAndIncrPC
                (s.push (EvmYul.State.tload u.toState μ₀).2))
            | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := rfl
      simp only [] at run
      rw [e] at run
      cases hp : u.stack.pop with
      | none => rw [hp] at run; cases run
      | some p => obtain ⟨_, _⟩ := p; rw [hp] at run; injection run with run; subst run; rfl)
    (fun arg u v run => by
      have e : EvmYul.step (.TLOAD : Operation .EVM) arg u =
          (match u.stack.pop with
            | some ⟨s, μ₀⟩ =>
              Except.ok (({ u with toState := (EvmYul.State.tload u.toState μ₀).1 } : State).replaceStackAndIncrPC
                (s.push (EvmYul.State.tload u.toState μ₀).2))
            | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := rfl
      simp only [] at run
      rw [e] at run
      cases hp : u.stack.pop with
      | none => rw [hp] at run; cases run
      | some p => obtain ⟨_, _⟩ := p; rw [hp] at run; injection run with run; subst run; rfl)
    (fun _ => by simp [H])

theorem same_sstore : Same .SSTORE :=
  same_rel (fun arg => EvmYul.step (.SSTORE : Operation .EVM) arg) (fun _ _ _ _ => rfl) sstore_preserves
    csstore_rel
    (fun arg u v run => by
      have e : EvmYul.step (.SSTORE : Operation .EVM) arg u =
          (match u.stack.pop2 with
            | some ⟨s, μ₀, μ₁⟩ =>
              Except.ok (({ u with toState := EvmYul.State.sstore u.toState μ₀ μ₁ } : State).replaceStackAndIncrPC s)
            | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := rfl
      simp only [] at run
      rw [e] at run
      cases hp : u.stack.pop2 with
      | none => rw [hp] at run; cases run
      | some p => obtain ⟨_, _, _⟩ := p; rw [hp] at run; injection run with run; subst run; rfl)
    (fun arg u v run => by
      have e : EvmYul.step (.SSTORE : Operation .EVM) arg u =
          (match u.stack.pop2 with
            | some ⟨s, μ₀, μ₁⟩ =>
              Except.ok (({ u with toState := EvmYul.State.sstore u.toState μ₀ μ₁ } : State).replaceStackAndIncrPC s)
            | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := rfl
      simp only [] at run
      rw [e] at run
      cases hp : u.stack.pop2 with
      | none => rw [hp] at run; cases run
      | some p => obtain ⟨_, _, _⟩ := p; rw [hp] at run; injection run with run; subst run; rfl)
    (fun _ => by simp [H])

theorem same_timestamp : Same .TIMESTAMP :=
  same_popn (EVM.stateOp EvmYul.State.timeStamp) some
    (fun stk y => y.replaceStackAndIncrPC (stk.push (EvmYul.State.timeStamp y.toState)))
    (fun _ _ _ _ => rfl) (fun _ => rfl) (fun _ => frameless_rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => by simp [H])

theorem same_number : Same .NUMBER :=
  same_popn (EVM.stateOp EvmYul.State.number) some
    (fun stk y => y.replaceStackAndIncrPC (stk.push (EvmYul.State.number y.toState)))
    (fun _ _ _ _ => rfl) (fun _ => rfl) (fun _ => frameless_rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => by simp [H])

theorem same_gaslimit : Same .GASLIMIT :=
  same_popn (EVM.stateOp EvmYul.State.gasLimit) some
    (fun stk y => y.replaceStackAndIncrPC (stk.push (EvmYul.State.gasLimit y.toState)))
    (fun _ _ _ _ => rfl) (fun _ => rfl) (fun _ => frameless_rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => by simp [H])

theorem same_chainid : Same .CHAINID :=
  same_popn (EVM.stateOp EvmYul.State.chainId) some
    (fun stk y => y.replaceStackAndIncrPC (stk.push (EvmYul.State.chainId y.toState)))
    (fun _ _ _ _ => rfl) (fun _ => rfl) (fun _ => frameless_rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => by simp [H])

theorem same_coinbase : Same .COINBASE :=
  same_popn (EVM.stateOp (.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase)) some
    (fun stk y => y.replaceStackAndIncrPC (stk.push ((.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase) y.toState)))
    (fun _ _ _ _ => rfl) (fun _ => rfl) (fun _ => frameless_rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => by simp [H])

theorem tstore_accounts (x : EvmYul.State .EVM) (a b : UInt256) (o : AccountAddress)
    (hx : x.executionEnv.codeOwner = o) :
    EvmYul.State.tstore x a b = { x with accountMap := (match x.accountMap.find? o with
      | none => x.accountMap
      | some acc => x.accountMap.insert o (acc.updateTransientStorage a b)) } := by
  unfold EvmYul.State.tstore EvmYul.State.lookupAccount
  simp only [hx]
  cases x.accountMap.find? o <;> simp [Option.option, EvmYul.State.updateAccount]

theorem tupdate_related (owner addr : AccountAddress) (old new : ByteArray) (acc acc' : Account .EVM)
    (a b : UInt256) (h : AccountsRelated owner addr old new acc acc') :
    AccountsRelated owner addr old new (acc.updateTransientStorage a b)
      (acc'.updateTransientStorage a b) := by
  unfold AccountsRelated at h ⊢
  obtain ⟨n, bal, st, ts, c⟩ := h
  unfold Account.updateTransientStorage
  split <;> simp_all

theorem tlinked (owner : AccountAddress) (code : ByteArray) (s t : State) (a b : UInt256)
    (link : Linked owner code s)
    (ht : t.toState = EvmYul.State.tstore s.toState a b) (o : s.executionEnv.codeOwner = owner) :
    Linked owner code t := by
  obtain ⟨lo, c, ⟨a1, f1, c1⟩, ⟨a2, f2, c2⟩⟩ := link
  have e := tstore_accounts s.toState a b owner o
  have hm : t.accountMap = s.accountMap.insert owner (a1.updateTransientStorage a b) := by
    have := congrArg EvmYul.State.accountMap ht
    rw [e] at this
    change t.accountMap = _ at this
    rw [this]; simp only [f1]
  have h0 : t.σ₀ = s.σ₀ := by
    have := congrArg EvmYul.State.σ₀ ht; rw [e] at this; exact this
  have he : t.executionEnv = s.executionEnv := by
    have := congrArg EvmYul.State.executionEnv ht; rw [e] at this; exact this
  refine ⟨by rw [he]; exact lo, by rw [he]; exact c, ⟨a1.updateTransientStorage a b, ?_, ?_⟩,
    ⟨a2, by rw [h0]; exact f2, c2⟩⟩
  · rw [hm, Batteries.RBMap.find?_insert, if_pos (compare_eq_iff_eq.mpr rfl)]
  · unfold Account.updateTransientStorage; split <;> exact c1

theorem tstore_preserves (arg : Option (UInt256 × Nat)) :
    Preserves (EvmYul.step (.TSTORE : Operation .EVM) arg) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  obtain ⟨o, o'⟩ := owner_eq h
  have e : ∀ y : State, EvmYul.step (.TSTORE : Operation .EVM) arg y =
      (match y.stack.pop2 with
        | some ⟨s, μ₀, μ₁⟩ =>
          Except.ok (({ y with toState := EvmYul.State.tstore y.toState μ₀ μ₁ } : State).replaceStackAndIncrPC s)
        | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := fun _ => rfl
  rw [e] at run ⊢
  rw [←st]
  cases hp : u.stack.pop2 with
  | none => rw [hp] at run; cases run
  | some p =>
    obtain ⟨stk, a, b⟩ := p
    rw [hp] at run
    injection run with run
    subst run
    refine ⟨_, rfl, ?_⟩
    have A := tstore_accounts u.toState a b owner o
    have A' := tstore_accounts u'.toState a b owner o'
    have G : Frameless (fun x => (x : State).replaceStackAndIncrPC stk) := frameless_rfl
    have g := G.preserve h
    refine ⟨?_, g.count, g.gas, ?_⟩
    · have l : E (({ u with toState := EvmYul.State.tstore u.toState a b } : State).replaceStackAndIncrPC stk) =
          E (u.replaceStackAndIncrPC stk) := by rw [A]; rfl
      have r : E (({ u' with toState := EvmYul.State.tstore u'.toState a b } : State).replaceStackAndIncrPC stk) =
          E (u'.replaceStackAndIncrPC stk) := by rw [A']; rfl
      exact l.trans (g.frame.trans r.symm)
    · have m := h.maps
      have rel := m.1 owner
      refine ⟨?_, ?_, tlinked owner old u _ a b m.2.2.1 rfl o, tlinked owner new u' _ a b m.2.2.2 rfl o'⟩
      · change MapsRelated owner old new (EvmYul.State.tstore u.toState a b).accountMap
          (EvmYul.State.tstore u'.toState a b).accountMap
        rw [A, A']
        revert rel
        cases f : u.accountMap.find? owner <;> cases f' : u'.accountMap.find? owner <;>
          simp only [] <;> intro rel
        · exact m.1
        · exact False.elim rel
        · exact False.elim rel
        · exact maps_insert owner old new _ _ _ _ m.1 (tupdate_related _ _ _ _ _ _ a b rel)
      · change MapsRelated owner old new (EvmYul.State.tstore u.toState a b).σ₀
          (EvmYul.State.tstore u'.toState a b).σ₀
        rw [A, A']; exact m.2.1

theorem same_tstore : Same .TSTORE :=
  same_rel (fun arg => EvmYul.step (.TSTORE : Operation .EVM) arg) (fun _ _ _ _ => rfl) tstore_preserves
    (fun _ => rfl)
    (fun arg u v run => by
      have e : EvmYul.step (.TSTORE : Operation .EVM) arg u =
          (match u.stack.pop2 with
            | some ⟨s, μ₀, μ₁⟩ =>
              Except.ok (({ u with toState := EvmYul.State.tstore u.toState μ₀ μ₁ } : State).replaceStackAndIncrPC s)
            | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := rfl
      simp only [] at run
      rw [e] at run
      cases hp : u.stack.pop2 with
      | none => rw [hp] at run; cases run
      | some p => obtain ⟨_, _, _⟩ := p; rw [hp] at run; injection run with run; subst run; rfl)
    (fun arg u v run => by
      have e : EvmYul.step (.TSTORE : Operation .EVM) arg u =
          (match u.stack.pop2 with
            | some ⟨s, μ₀, μ₁⟩ =>
              Except.ok (({ u with toState := EvmYul.State.tstore u.toState μ₀ μ₁ } : State).replaceStackAndIncrPC s)
            | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := rfl
      simp only [] at run
      rw [e] at run
      cases hp : u.stack.pop2 with
      | none => rw [hp] at run; cases run
      | some p => obtain ⟨_, _, _⟩ := p; rw [hp] at run; injection run with run; subst run; rfl)
    (fun _ => by simp [H])

theorem mcopy_frameless (a b c : UInt256) (stk : Stack UInt256) :
    Frameless (fun x : State =>
      ({ x with toMachineState := x.toMachineState.mcopy a b c } : State).replaceStackAndIncrPC stk) := by
  refine ⟨fun x => ?_, fun x => by simp only [MachineState.mcopy, writeBytes]; rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  have m : (E x).toMachineState = { x.toMachineState with gasAvailable := UInt256.ofNat 0 } := rfl
  show E (({ x with toMachineState := x.toMachineState.mcopy a b c } : State).replaceStackAndIncrPC stk) =
    E (({ E x with toMachineState := (E x).toMachineState.mcopy a b c } : State).replaceStackAndIncrPC stk)
  rw [m]
  simp only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas, EVM.State.replaceStackAndIncrPC,
    EVM.State.incrPC, MachineState.mcopy, writeBytes]

theorem same_mcopy : Same .MCOPY :=
  same_popn (EVM.ternaryMachineStateOp MachineState.mcopy) Stack.pop3
    (fun ⟨stk, a, b, c⟩ y =>
      ({ y with toMachineState := y.toMachineState.mcopy a b c } : State).replaceStackAndIncrPC stk)
    (fun _ _ _ _ => rfl)
    (fun y => by unfold EVM.ternaryMachineStateOp; cases y.stack.pop3 <;> rfl)
    (fun ⟨_, a, b, c⟩ => mcopy_frameless a b c _) (fun ⟨_, _, _, _⟩ _ => rfl)
    (fun _ _ h => by
      simp only [C', h, show Operation.StackMemFlow .MCOPY ∈ InstructionGasGroups.Wcopy from by decide,
        if_true])
    (fun _ => rfl) (fun _ => by simp [H])

theorem same_blockhash : Same .BLOCKHASH :=
  same_popn (EVM.unaryStateOp (fun s v => (s, EvmYul.State.blockHash s v))) Stack.pop
    (fun ⟨stk, a⟩ y => y.replaceStackAndIncrPC (stk.push (EvmYul.State.blockHash y.toState a)))
    (fun _ _ _ _ => rfl)
    (fun y => by unfold EVM.unaryStateOp; cases y.stack.pop <;> rfl)
    (fun ⟨_, _⟩ => frameless_rfl) (fun ⟨_, _⟩ _ => rfl)
    (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => by simp [H])

/-! SELFDESTRUCT: a halting instruction that moves the owner's balance. -/

/-- The account map after SELFDESTRUCT by `ia` to `r`, as the pinned semantics computes it. -/
def destructMap (σ : AccountMap .EVM) (ia r : AccountAddress) (created : Bool) : AccountMap .EVM :=
  match σ.find? ia with
  | none => σ
  | some a =>
    match σ.find? r with
    | none =>
      if (a.balance == ⟨0⟩) = true then σ
      else (σ.insert r { (default : Account .EVM) with balance := a.balance }).insert ia { a with balance := ⟨0⟩ }
    | some b =>
      if r ≠ ia then (σ.insert r { b with balance := b.balance + a.balance }).insert ia { a with balance := ⟨0⟩ }
      else if created then (σ.insert r { b with balance := ⟨0⟩ }).insert ia { a with balance := ⟨0⟩ }
      else σ

/-- The substate after SELFDESTRUCT. -/
def destructSub (A : Substate) (ia r : AccountAddress) (created : Bool) : Substate :=
  if created then
    { A with selfDestructSet := A.selfDestructSet.insert ia, accessedAccounts := A.accessedAccounts.insert r }
  else { A with accessedAccounts := A.accessedAccounts.insert r }

/-- The state after SELFDESTRUCT. -/
def destructPost (u : State) (a : UInt256) (stk : List UInt256) : State :=
  ({ u with
    accountMap := destructMap u.accountMap u.executionEnv.codeOwner (AccountAddress.ofUInt256 a)
      (u.createdAccounts.contains u.executionEnv.codeOwner)
    substate := destructSub u.substate u.executionEnv.codeOwner (AccountAddress.ofUInt256 a)
      (u.createdAccounts.contains u.executionEnv.codeOwner) } : State).replaceStackAndIncrPC stk

theorem selfdestruct_shape (arg : Option (UInt256 × Nat)) (u : State) (a : UInt256) (stk : List UInt256)
    (h : u.stack = a :: stk) :
    EvmYul.step (.SELFDESTRUCT : Operation .EVM) arg u = .ok (destructPost u a stk) := by
  unfold EvmYul.step
  simp only [h, Stack.pop, Id.run]
  unfold destructPost destructMap destructSub
  split <;> rename_i hc <;> simp only [hc, if_true, if_false, EvmYul.State.lookupAccount] <;> rfl

theorem destruct_related {owner : AccountAddress} {old new : ByteArray} {σ τ : AccountMap .EVM}
    (rel : MapsRelated owner old new σ τ) (r : AccountAddress) (created : Bool)
    (oldσ : ∃ a, σ.find? owner = some a ∧ a.code = old) :
    MapsRelated owner old new (destructMap σ owner r created) (destructMap τ owner r created) ∧
    (∃ a, (destructMap σ owner r created).find? owner = some a ∧ a.code = old) := by
  unfold destructMap
  rcases related_find rel owner with ⟨e, e'⟩ | ⟨a, a', e, e', h⟩
  · obtain ⟨x, hx, -⟩ := oldσ
    rw [e] at hx; cases hx
  · obtain ⟨n, b, sto, ts, c⟩ := h
    rw [if_pos rfl] at c
    rcases related_find rel r with ⟨f, f'⟩ | ⟨d, d', f, f', hd⟩
    · simp only [e, e', f, f', b]
      have ne : r ≠ owner := by intro hr; subst hr; rw [e] at f; cases f
      split
      · exact ⟨rel, oldσ⟩
      · refine ⟨maps_insert_at owner owner old new _ _ _ _
          (maps_insert_at owner r old new σ τ _ _ rel ⟨rfl, rfl, rfl, rfl, by rw [if_neg ne]⟩)
          ⟨n, rfl, sto, ts, by rw [if_pos rfl]; exact c⟩, ?_⟩
        rw [Batteries.RBMap.find?_insert, if_pos (compare_eq_iff_eq.mpr rfl)]
        exact ⟨_, rfl, c.1⟩
    · simp only [e, e', f, f']
      obtain ⟨nd, bd, sd, td, cd⟩ := hd
      by_cases hr : r = owner
      · subst hr
        simp only [ne_eq, not_true_eq_false, if_false]
        rw [if_pos rfl] at cd
        split
        · refine ⟨maps_insert_at r r old new _ _ _ _
            (maps_insert_at r r old new σ τ _ _ rel ⟨nd, rfl, sd, td, by rw [if_pos rfl]; exact cd⟩)
            ⟨n, rfl, sto, ts, by rw [if_pos rfl]; exact c⟩, ?_⟩
          rw [Batteries.RBMap.find?_insert, if_pos (compare_eq_iff_eq.mpr rfl)]
          exact ⟨_, rfl, c.1⟩
        · exact ⟨rel, oldσ⟩
      · simp only [ne_eq, hr, not_false_eq_true, if_true]
        rw [if_neg hr] at cd
        refine ⟨maps_insert_at owner owner old new _ _ _ _
          (maps_insert_at owner r old new σ τ _ _ rel ⟨nd, by simp only [bd, b], sd, td, by rw [if_neg hr]; exact cd⟩)
          ⟨n, rfl, sto, ts, by rw [if_pos rfl]; exact c⟩, ?_⟩
        rw [Batteries.RBMap.find?_insert, if_pos (compare_eq_iff_eq.mpr rfl)]
        exact ⟨_, rfl, c.1⟩

theorem destruct_linked {owner : AccountAddress} {code : ByteArray} {σ : AccountMap .EVM}
    (r : AccountAddress) (created : Bool) (h : ∃ a, σ.find? owner = some a ∧ a.code = code) :
    ∃ a, (destructMap σ owner r created).find? owner = some a ∧ a.code = code := by
  have rel : MapsRelated owner code code σ σ := by
    intro addr
    cases e : σ.find? addr with
    | none => trivial
    | some a => exact ⟨rfl, rfl, rfl, rfl, by split <;> simp_all⟩
  exact (destruct_related rel r created h).2

theorem cost_selfdestruct (y : State) : C' y .SELFDESTRUCT =
    GasConstants.Gselfdestruct +
      (if y.substate.accessedAccounts.contains (AccountAddress.ofUInt256 y.stack[0]!) then 0
        else GasConstants.Gcoldaccountaccess) +
      (if EvmYul.State.dead y.accountMap (AccountAddress.ofUInt256 y.stack[0]!) ∧
          (y.accountMap.find? y.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ≠ ⟨0⟩ then
        GasConstants.Gnewaccount else 0) := rfl

theorem cselfdestruct_rel {owner old new surplus skipped s t} (ho : 0 < old.size) (hn : 0 < new.size)
    (h : DeployedOffset owner old new surplus skipped s t) : C' t .SELFDESTRUCT = C' s .SELFDESTRUCT := by
  obtain ⟨o, o'⟩ := owner_eq h
  have st := rel_stack h
  have sub : s.substate = t.substate := by
    simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
      congrArg (fun x : State => x.substate) h.frame
  rw [cost_selfdestruct, cost_selfdestruct, o, o', st, sub, dead_rel h.maps.1 ho hn]
  rcases related_find h.maps.1 owner with ⟨e, e'⟩ | ⟨a, a', e, e', ha⟩
  · rw [e, e']
  · rw [e, e']
    obtain ⟨-, b, -, -, -⟩ := ha
    simp only [Option.option, b]

theorem selfdestruct_nil (arg : Option (UInt256 × Nat)) (u : State) (h : u.stack = []) :
    EvmYul.step (.SELFDESTRUCT : Operation .EVM) arg u = .error .StackUnderflow := by
  unfold EvmYul.step
  simp [h, Stack.pop, Id.run]

theorem selfdestruct_at {old new : ByteArray} (ho : 0 < old.size) (hn : 0 < new.size) :
    CongruentAt old new .SELFDESTRUCT := by
  refine ⟨fun _ _ _ _ _ => rfl, fun rel => cselfdestruct_rel ho hn rel, ?_, ?_⟩
  · intro owner surplus skipped u u' v f g c arg rel enough step
    have rb := rel_bump rel c enough
    change EvmYul.step (.SELFDESTRUCT : Operation .EVM) arg (bump u c) = .ok v at step
    obtain ⟨a, stk, hs⟩ : ∃ a stk, (bump u c).stack = a :: stk := by
      cases hs : (bump u c).stack with
      | nil => rw [selfdestruct_nil arg _ hs] at step; cases step
      | cons a stk => exact ⟨a, stk, rfl⟩
    rw [selfdestruct_shape arg _ a stk hs] at step
    injection step with step
    subst step
    have hs' : (bump u' c).stack = a :: stk := by rw [← rel_stack rb]; exact hs
    refine ⟨destructPost (bump u' c) a stk, ?_, ?_⟩
    · change EvmYul.step (.SELFDESTRUCT : Operation .EVM) arg (bump u' c) = _
      rw [selfdestruct_shape arg _ a stk hs']
    · obtain ⟨o, o'⟩ := owner_eq rb
      have cr : (bump u c).createdAccounts = (bump u' c).createdAccounts := by
        simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
          congrArg (fun x : State => x.createdAccounts) rb.frame
      have sub : (bump u c).substate = (bump u' c).substate := by
        simpa only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
          congrArg (fun x : State => x.substate) rb.frame
      have m := rb.maps
      refine ⟨?_, rb.count, rb.gas, ?_⟩
      · show E (destructPost (bump u c) a stk) = E (destructPost (bump u' c) a stk)
        have key : ∀ (y : State) (A : Substate) (σ : AccountMap .EVM),
            E (({ y with accountMap := σ, substate := A } : State).replaceStackAndIncrPC stk) =
              E (({ E y with accountMap := σ, substate := A } : State).replaceStackAndIncrPC stk) := by
          intro y A σ
          simp only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas, EVM.State.replaceStackAndIncrPC,
            EVM.State.incrPC]
        unfold destructPost
        rw [key, key (bump u' c), show E (bump u c) = E (bump u' c) from rb.frame, o, o', ← cr, ← sub]
        simp only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas, EVM.State.replaceStackAndIncrPC,
          EVM.State.incrPC]
      · obtain ⟨d1, d2⟩ := destruct_related m.1 (AccountAddress.ofUInt256 a)
          ((bump u c).createdAccounts.contains owner) m.2.2.1.2.2.1
        have d3 := destruct_linked (σ := (bump u' c).accountMap) (AccountAddress.ofUInt256 a)
          ((bump u c).createdAccounts.contains owner) m.2.2.2.2.2.1
        refine ⟨?_, m.2.1, ⟨o, m.2.2.1.2.1, ?_, m.2.2.1.2.2.2⟩, ⟨o', m.2.2.2.2.1, ?_, m.2.2.2.2.2.2⟩⟩
        · show MapsRelated owner old new
            (destructMap (bump u c).accountMap (bump u c).executionEnv.codeOwner (AccountAddress.ofUInt256 a)
              ((bump u c).createdAccounts.contains (bump u c).executionEnv.codeOwner))
            (destructMap (bump u' c).accountMap (bump u' c).executionEnv.codeOwner (AccountAddress.ofUInt256 a)
              ((bump u' c).createdAccounts.contains (bump u' c).executionEnv.codeOwner))
          rw [o, o', ← cr]; exact d1
        · show ∃ x, (destructMap (bump u c).accountMap (bump u c).executionEnv.codeOwner (AccountAddress.ofUInt256 a)
            ((bump u c).createdAccounts.contains (bump u c).executionEnv.codeOwner)).find? owner = some x ∧ x.code = old
          rw [o]; exact d2
        · show ∃ x, (destructMap (bump u' c).accountMap (bump u' c).executionEnv.codeOwner (AccountAddress.ofUInt256 a)
            ((bump u' c).createdAccounts.contains (bump u' c).executionEnv.codeOwner)).find? owner = some x ∧ x.code = new
          rw [o', ← cr]; exact d3
  · intro f c arg u v enough step
    change EvmYul.step (.SELFDESTRUCT : Operation .EVM) arg (bump u c) = .ok v at step
    obtain ⟨a, stk, hs⟩ : ∃ a stk, (bump u c).stack = a :: stk := by
      cases hs : (bump u c).stack with
      | nil => rw [selfdestruct_nil arg _ hs] at step; cases step
      | cons a stk => exact ⟨a, stk, rfl⟩
    rw [selfdestruct_shape arg _ a stk hs] at step
    injection step with step
    subst step
    show (bump u c).gasAvailable.toNat ≤ u.gasAvailable.toNat
    rw [bump_gas u c enough]; exact Nat.sub_le _ _

#print axioms selfdestruct_at
#print axioms same_mcopy
#print axioms same_blockhash
#print axioms same_tstore
#print axioms same_sload
#print axioms same_sstore
#print axioms same_tload
#print axioms same_log0
#print axioms same_log4
#print axioms same_keccak256

end GolfWhole
