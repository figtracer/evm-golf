import WholeFacts
import WholeEnv
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition

/-! Stack shapes of instructions outside windows: the slots below the inputs stay
unchanged, so facts about them survive. -/
namespace GolfWhole

theorem sh_push {k : Nat} {st stk : List UInt256} (xs : List UInt256) (e : st = xs ++ stk)
    (len : xs.length = k) (x : UInt256) : Shape k [top] st (x :: stk) :=
  ⟨[x], by rw [e, ← len, List.drop_left]; rfl, rfl, top_holds x, trivial⟩

theorem sh_none {k : Nat} {st stk : List UInt256} (xs : List UInt256) (e : st = xs ++ stk)
    (len : xs.length = k) : Shape k [] st stk :=
  ⟨[], by rw [e, ← len, List.drop_left]; rfl, rfl, trivial⟩

theorem sh_bits {st : List UInt256} {n : Nat} (x : UInt256) (hx : x.val.val < 2 ^ n) :
    Shape 0 [⟨n, none⟩] st (x :: st) :=
  ⟨[x], rfl, rfl, ⟨hx, fun _ h => by cases h⟩, trivial⟩

theorem pop1_eq {st stk : List UInt256} {a : UInt256} (h : Stack.pop st = some (stk, a)) :
    st = [a] ++ stk := by
  match st, h with
  | _ :: _, h => simp only [Stack.pop, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl

theorem pop2_eq {st stk : List UInt256} {a b : UInt256} (h : Stack.pop2 st = some (stk, a, b)) :
    st = [a, b] ++ stk := by
  match st, h with
  | _ :: _ :: _, h =>
    simp only [Stack.pop2, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h; rfl

theorem pop3_eq {st stk : List UInt256} {a b c : UInt256} (h : Stack.pop3 st = some (stk, a, b, c)) :
    st = [a, b, c] ++ stk := by
  match st, h with
  | _ :: _ :: _ :: _, h =>
    simp only [Stack.pop3, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl

theorem pop4_eq {st stk : List UInt256} {a b c d : UInt256}
    (h : Stack.pop4 st = some (stk, a, b, c, d)) : st = [a, b, c, d] ++ stk := by
  match st, h with
  | _ :: _ :: _ :: _ :: _, h =>
    simp only [Stack.pop4, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h; rfl

theorem pop5_eq {st stk : List UInt256} {a b c d e : UInt256}
    (h : Stack.pop5 st = some (stk, a, b, c, d, e)) : st = [a, b, c, d, e] ++ stk := by
  match st, h with
  | _ :: _ :: _ :: _ :: _ :: _, h =>
    simp only [Stack.pop5, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; rfl

theorem pop6_eq {st stk : List UInt256} {a b c d e g : UInt256}
    (h : Stack.pop6 st = some (stk, a, b, c, d, e, g)) : st = [a, b, c, d, e, g] ++ stk := by
  match st, h with
  | _ :: _ :: _ :: _ :: _ :: _ :: _, h =>
    simp only [Stack.pop6, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; rfl

theorem bump_stack (u : State) (c : ℕ) : (bump u c).stack = u.stack := rfl

theorem addr_lt (a : AccountAddress) : (UInt256.ofNat a.val).val.val < 2 ^ 160 := by
  have h : a.val < 2 ^ 160 := a.isLt
  show (Fin.ofNat UInt256.size a.val).val < _
  simp only [Fin.ofNat]
  rw [Nat.mod_eq_of_lt (lt_trans h (by decide))]
  exact h

/-- Environment reads push one value. -/
theorem eff_env {op : Operation .EVM} (g : ExecutionEnv .EVM → UInt256)
    (hstep : ∀ f c arg u, EVM.step (f + 1) c (some (op, arg)) u = EVM.executionEnvOp g (bump u c))
    (arg : Option (UInt256 × Nat)) : Eff op arg (Shape 0 [top]) := by
  intro f u v _ step
  rw [hstep] at step
  unfold EVM.executionEnvOp at step
  injection step with step; subst step
  exact sh_push [] rfl rfl _

theorem eff_addr {op : Operation .EVM} (g : ExecutionEnv .EVM → AccountAddress)
    (hstep : ∀ f c arg u, EVM.step (f + 1) c (some (op, arg)) u =
      EVM.executionEnvOp (.ofNat ∘ Fin.val ∘ g) (bump u c))
    (arg : Option (UInt256 × Nat)) : Eff op arg (Shape 0 [⟨160, none⟩]) := by
  intro f u v _ step
  rw [hstep] at step
  unfold EVM.executionEnvOp at step
  injection step with step; subst step
  exact sh_bits _ (addr_lt _)

theorem eff_state {op : Operation .EVM} (g : EvmYul.State .EVM → UInt256)
    (hstep : ∀ f c arg u, EVM.step (f + 1) c (some (op, arg)) u = EVM.stateOp g (bump u c))
    (arg : Option (UInt256 × Nat)) : Eff op arg (Shape 0 [top]) := by
  intro f u v _ step
  rw [hstep] at step
  unfold EVM.stateOp at step
  injection step with step; subst step
  exact sh_push [] rfl rfl _

theorem eff_machine0 {op : Operation .EVM} (g : MachineState → UInt256)
    (hstep : ∀ f c arg u, EVM.step (f + 1) c (some (op, arg)) u = EVM.machineStateOp g (bump u c))
    (arg : Option (UInt256 × Nat)) : Eff op arg (Shape 0 [top]) := by
  intro f u v _ step
  rw [hstep] at step
  unfold EVM.machineStateOp at step
  injection step with step; subst step
  exact sh_push [] rfl rfl _

theorem eff_bin {op : Operation .EVM} (g : Primop.Binary)
    (hstep : ∀ f c arg u, EVM.step (f + 1) c (some (op, arg)) u = EVM.execBinOp g (bump u c))
    (arg : Option (UInt256 × Nat)) : Eff op arg (Shape 2 [top]) := by
  intro f u v _ step
  rw [hstep] at step
  unfold EVM.execBinOp at step
  cases hp : (bump u (C' u op)).stack.pop2 with
  | none => rw [hp] at step; cases step
  | some p =>
    obtain ⟨stk, a, b⟩ := p; rw [hp] at step; injection step with step; subst step
    exact sh_push _ (pop2_eq hp) rfl _

theorem eff_tri {op : Operation .EVM} (g : Primop.Ternary)
    (hstep : ∀ f c arg u, EVM.step (f + 1) c (some (op, arg)) u = EVM.execTriOp g (bump u c))
    (arg : Option (UInt256 × Nat)) : Eff op arg (Shape 3 [top]) := by
  intro f u v _ step
  rw [hstep] at step
  unfold EVM.execTriOp at step
  cases hp : (bump u (C' u op)).stack.pop3 with
  | none => rw [hp] at step; cases step
  | some p =>
    obtain ⟨stk, a, b, c⟩ := p; rw [hp] at step; injection step with step; subst step
    exact sh_push _ (pop3_eq hp) rfl _

theorem eff_mach2 {op : Operation .EVM} (g : MachineState → UInt256 → UInt256 → MachineState)
    (hstep : ∀ f c arg u, EVM.step (f + 1) c (some (op, arg)) u = EVM.binaryMachineStateOp g (bump u c))
    (arg : Option (UInt256 × Nat)) : Eff op arg (Shape 2 []) := by
  intro f u v _ step
  rw [hstep] at step
  unfold EVM.binaryMachineStateOp at step
  cases hp : (bump u (C' u op)).stack.pop2 with
  | none => rw [hp] at step; cases step
  | some p =>
    obtain ⟨stk, a, b⟩ := p; rw [hp] at step; injection step with step; subst step
    exact sh_none _ (pop2_eq hp) rfl

theorem eff_keccak256 (arg : Option (UInt256 × Nat)) : Eff .KECCAK256 arg (Shape 2 [top]) := by
  intro f u v _ step
  change EVM.binaryMachineStateOp' MachineState.keccak256 (bump u _) = _ at step
  unfold EVM.binaryMachineStateOp' at step
  cases hp : (bump u (C' u .KECCAK256)).stack.pop2 with
  | none => rw [hp] at step; cases step
  | some p =>
    obtain ⟨stk, a, b⟩ := p; rw [hp] at step; injection step with step; subst step
    exact sh_push _ (pop2_eq hp) rfl _

theorem eff_calldatacopy (arg : Option (UInt256 × Nat)) : Eff .CALLDATACOPY arg (Shape 3 []) := by
  intro f u v _ step
  change EVM.ternaryCopyOp SharedState.calldatacopy (bump u _) = _ at step
  unfold EVM.ternaryCopyOp at step
  cases hp : (bump u (C' u .CALLDATACOPY)).stack.pop3 with
  | none => rw [hp] at step; cases step
  | some p =>
    obtain ⟨stk, a, b, c⟩ := p; rw [hp] at step; injection step with step; subst step
    exact sh_none _ (pop3_eq hp) rfl

theorem eff_mcopy (arg : Option (UInt256 × Nat)) : Eff .MCOPY arg (Shape 3 []) := by
  intro f u v _ step
  change EVM.ternaryMachineStateOp MachineState.mcopy (bump u _) = _ at step
  unfold EVM.ternaryMachineStateOp at step
  cases hp : (bump u (C' u .MCOPY)).stack.pop3 with
  | none => rw [hp] at step; cases step
  | some p =>
    obtain ⟨stk, a, b, c⟩ := p; rw [hp] at step; injection step with step; subst step
    exact sh_none _ (pop3_eq hp) rfl

theorem eff_log0 (arg : Option (UInt256 × Nat)) : Eff .LOG0 arg (Shape 2 []) := by
  intro f u v _ step
  change EVM.log0Op (bump u _) = _ at step
  unfold EVM.log0Op at step
  cases hp : (bump u (C' u .LOG0)).stack.pop2 with
  | none => rw [hp] at step; cases step
  | some p =>
    obtain ⟨stk, a, b⟩ := p; rw [hp] at step; injection step with step; subst step
    exact sh_none _ (pop2_eq hp) rfl

theorem eff_log1 (arg : Option (UInt256 × Nat)) : Eff .LOG1 arg (Shape 3 []) := by
  intro f u v _ step
  change EVM.log1Op (bump u _) = _ at step
  unfold EVM.log1Op at step
  cases hp : (bump u (C' u .LOG1)).stack.pop3 with
  | none => rw [hp] at step; cases step
  | some p =>
    obtain ⟨stk, a, b, c⟩ := p; rw [hp] at step; injection step with step; subst step
    exact sh_none _ (pop3_eq hp) rfl

theorem eff_log2 (arg : Option (UInt256 × Nat)) : Eff .LOG2 arg (Shape 4 []) := by
  intro f u v _ step
  change EVM.log2Op (bump u _) = _ at step
  unfold EVM.log2Op at step
  cases hp : (bump u (C' u .LOG2)).stack.pop4 with
  | none => rw [hp] at step; cases step
  | some p =>
    obtain ⟨stk, a, b, c, d⟩ := p; rw [hp] at step; injection step with step; subst step
    exact sh_none _ (pop4_eq hp) rfl

theorem eff_log3 (arg : Option (UInt256 × Nat)) : Eff .LOG3 arg (Shape 5 []) := by
  intro f u v _ step
  change EVM.log3Op (bump u _) = _ at step
  unfold EVM.log3Op at step
  cases hp : (bump u (C' u .LOG3)).stack.pop5 with
  | none => rw [hp] at step; cases step
  | some p =>
    obtain ⟨stk, a, b, c, d, e⟩ := p; rw [hp] at step; injection step with step; subst step
    exact sh_none _ (pop5_eq hp) rfl

theorem eff_log4 (arg : Option (UInt256 × Nat)) : Eff .LOG4 arg (Shape 6 []) := by
  intro f u v _ step
  change EVM.log4Op (bump u _) = _ at step
  unfold EVM.log4Op at step
  cases hp : (bump u (C' u .LOG4)).stack.pop6 with
  | none => rw [hp] at step; cases step
  | some p =>
    obtain ⟨stk, a, b, c, d, e⟩ := p; rw [hp] at step; injection step with step; subst step
    exact sh_none _ (pop6_eq hp) rfl

theorem eff_blockhash (arg : Option (UInt256 × Nat)) : Eff .BLOCKHASH arg (Shape 1 [top]) := by
  intro f u v _ step
  change EVM.unaryStateOp (fun s v => (s, EvmYul.State.blockHash s v)) (bump u _) = _ at step
  unfold EVM.unaryStateOp at step
  cases hp : (bump u (C' u .BLOCKHASH)).stack.pop with
  | none => rw [hp] at step; cases step
  | some p =>
    obtain ⟨stk, a⟩ := p; rw [hp] at step; injection step with step; subst step
    exact sh_push _ (pop1_eq hp) rfl _

theorem eff_blobhash (arg : Option (UInt256 × Nat)) : Eff .BLOBHASH arg (Shape 1 [top]) := by
  intro f u v _ step
  change EVM.unaryExecutionEnvOp blobhash (bump u _) = _ at step
  unfold EVM.unaryExecutionEnvOp at step
  cases hp : (bump u (C' u .BLOBHASH)).stack.pop with
  | none => rw [hp] at step; cases step
  | some p =>
    obtain ⟨stk, a⟩ := p; rw [hp] at step; injection step with step; subst step
    exact sh_push _ (pop1_eq hp) rfl _

/-- One input, one output, through `EvmYul.step`. -/
theorem eff_un1 {op : Operation .EVM} (G : State → UInt256 → State) (val : State → UInt256 → UInt256)
    (hstep : ∀ f c arg u, EVM.step (f + 1) c (some (op, arg)) u =
      (match (bump u c).stack.pop with
        | some ⟨s, μ₀⟩ => Except.ok ((G (bump u c) μ₀).replaceStackAndIncrPC (s.push (val (bump u c) μ₀)))
        | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State))
    (arg : Option (UInt256 × Nat)) : Eff op arg (Shape 1 [top]) := by
  intro f u v _ step
  rw [hstep] at step
  cases hp : (bump u (C' u op)).stack.pop with
  | none => rw [hp] at step; cases step
  | some p =>
    obtain ⟨stk, a⟩ := p; rw [hp] at step; injection step with step; subst step
    exact sh_push _ (pop1_eq hp) rfl _

/-- Two inputs, no output, through `EvmYul.step`. -/
theorem eff_store2 {op : Operation .EVM} (G : State → UInt256 → UInt256 → State)
    (hstep : ∀ f c arg u, EVM.step (f + 1) c (some (op, arg)) u =
      (match (bump u c).stack.pop2 with
        | some ⟨s, μ₀, μ₁⟩ => Except.ok ((G (bump u c) μ₀ μ₁).replaceStackAndIncrPC s)
        | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State))
    (arg : Option (UInt256 × Nat)) : Eff op arg (Shape 2 []) := by
  intro f u v _ step
  rw [hstep] at step
  cases hp : (bump u (C' u op)).stack.pop2 with
  | none => rw [hp] at step; cases step
  | some p =>
    obtain ⟨stk, a, b⟩ := p; rw [hp] at step; injection step with step; subst step
    exact sh_none _ (pop2_eq hp) rfl

theorem eff_mload (arg : Option (UInt256 × Nat)) : Eff .MLOAD arg (Shape 1 [top]) :=
  eff_un1 (fun y μ₀ => { y with toMachineState := (y.toMachineState.mload μ₀).2 })
    (fun y μ₀ => (y.toMachineState.mload μ₀).1) (fun _ _ _ _ => rfl) arg
theorem eff_calldataload (arg : Option (UInt256 × Nat)) : Eff .CALLDATALOAD arg (Shape 1 [top]) :=
  eff_un1 (fun y _ => y) (fun y μ₀ => EvmYul.State.calldataload y.toState μ₀) (fun _ _ _ _ => rfl) arg
theorem eff_sload (arg : Option (UInt256 × Nat)) : Eff .SLOAD arg (Shape 1 [top]) :=
  eff_un1 (fun y μ₀ => { y with toState := (EvmYul.State.sload y.toState μ₀).1 })
    (fun y μ₀ => (EvmYul.State.sload y.toState μ₀).2) (fun _ _ _ _ => rfl) arg
theorem eff_tload (arg : Option (UInt256 × Nat)) : Eff .TLOAD arg (Shape 1 [top]) :=
  eff_un1 (fun y μ₀ => { y with toState := (EvmYul.State.tload y.toState μ₀).1 })
    (fun y μ₀ => (EvmYul.State.tload y.toState μ₀).2) (fun _ _ _ _ => rfl) arg
theorem eff_balance (arg : Option (UInt256 × Nat)) : Eff .BALANCE arg (Shape 1 [top]) :=
  eff_un1 (fun y μ₀ => { y with toState := (EvmYul.State.balance y.toState μ₀).1 })
    (fun y μ₀ => (EvmYul.State.balance y.toState μ₀).2) (fun _ _ _ _ => rfl) arg
theorem eff_extcodesize (arg : Option (UInt256 × Nat)) : Eff .EXTCODESIZE arg (Shape 1 [top]) :=
  eff_un1 (fun y μ₀ => { y with toState := (EvmYul.State.extCodeSize y.toState μ₀).1 })
    (fun y μ₀ => (EvmYul.State.extCodeSize y.toState μ₀).2) (fun _ _ _ _ => rfl) arg
theorem eff_sstore (arg : Option (UInt256 × Nat)) : Eff .SSTORE arg (Shape 2 []) :=
  eff_store2 (fun y μ₀ μ₁ => { y with toState := EvmYul.State.sstore y.toState μ₀ μ₁ })
    (fun _ _ _ _ => rfl) arg
theorem eff_tstore (arg : Option (UInt256 × Nat)) : Eff .TSTORE arg (Shape 2 []) :=
  eff_store2 (fun y μ₀ μ₁ => { y with toState := EvmYul.State.tstore y.toState μ₀ μ₁ })
    (fun _ _ _ _ => rfl) arg

theorem eff_returndatacopy (arg : Option (UInt256 × Nat)) : Eff .RETURNDATACOPY arg (Shape 3 []) := by
  intro f u v _ step
  change (match (bump u (C' u .RETURNDATACOPY)).stack.pop3 with
    | some ⟨stack', μ₀, μ₁, μ₂⟩ =>
      Except.ok (({ bump u (C' u .RETURNDATACOPY) with
        toMachineState := (bump u (C' u .RETURNDATACOPY)).toMachineState.returndatacopy μ₀ μ₁ μ₂ } : State).replaceStackAndIncrPC stack')
    | _ => .error .StackUnderflow : Except EVM.ExecutionException State) = _ at step
  cases hp : (bump u (C' u .RETURNDATACOPY)).stack.pop3 with
  | none => rw [hp] at step; cases step
  | some p =>
    obtain ⟨stk, a, b, c⟩ := p; rw [hp] at step; injection step with step; subst step
    exact sh_none _ (pop3_eq hp) rfl

theorem eff_jumpdest (arg : Option (UInt256 × Nat)) : Eff .JUMPDEST arg (Shape 0 []) := by
  intro f u v _ step
  change Except.ok (bump u _).incrPC = .ok v at step
  injection step with step; subst step
  exact sh_none [] rfl rfl

theorem eff_exp (arg) : Eff .EXP arg (Shape 2 [top]) := eff_bin UInt256.exp (fun _ _ _ _ => rfl) arg
theorem eff_addmod (arg) : Eff .ADDMOD arg (Shape 3 [top]) := eff_tri UInt256.addMod (fun _ _ _ _ => rfl) arg
theorem eff_mulmod (arg) : Eff .MULMOD arg (Shape 3 [top]) := eff_tri UInt256.mulMod (fun _ _ _ _ => rfl) arg
theorem eff_mstore (arg) : Eff .MSTORE arg (Shape 2 []) :=
  eff_mach2 MachineState.mstore (fun _ _ _ _ => rfl) arg
theorem eff_mstore8 (arg) : Eff .MSTORE8 arg (Shape 2 []) :=
  eff_mach2 MachineState.mstore8 (fun _ _ _ _ => rfl) arg
theorem eff_callvalue (arg) : Eff .CALLVALUE arg (Shape 0 [top]) :=
  eff_env ExecutionEnv.weiValue (fun _ _ _ _ => rfl) arg
theorem eff_calldatasize (arg) : Eff .CALLDATASIZE arg (Shape 0 [top]) :=
  eff_env (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.calldata) (fun _ _ _ _ => rfl) arg
theorem eff_gasprice (arg) : Eff .GASPRICE arg (Shape 0 [top]) :=
  eff_env (.ofNat ∘ ExecutionEnv.gasPrice) (fun _ _ _ _ => rfl) arg
theorem eff_basefee (arg) : Eff .BASEFEE arg (Shape 0 [top]) :=
  eff_env EvmYul.basefee (fun _ _ _ _ => rfl) arg
theorem eff_prevrandao (arg) : Eff .PREVRANDAO arg (Shape 0 [top]) :=
  eff_env EvmYul.prevRandao (fun _ _ _ _ => rfl) arg
theorem eff_blobbasefee (arg) : Eff .BLOBBASEFEE arg (Shape 0 [top]) :=
  eff_env EvmYul.ExecutionEnv.getBlobGasprice (fun _ _ _ _ => rfl) arg
theorem eff_codesize (arg) : Eff .CODESIZE arg (Shape 0 [top]) :=
  eff_env (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.code) (fun _ _ _ _ => rfl) arg
theorem eff_caller (arg) : Eff .CALLER arg (Shape 0 [⟨160, none⟩]) :=
  eff_addr ExecutionEnv.source (fun _ _ _ _ => rfl) arg
theorem eff_origin (arg) : Eff .ORIGIN arg (Shape 0 [⟨160, none⟩]) :=
  eff_addr ExecutionEnv.sender (fun _ _ _ _ => rfl) arg
theorem eff_address (arg) : Eff .ADDRESS arg (Shape 0 [⟨160, none⟩]) :=
  eff_addr ExecutionEnv.codeOwner (fun _ _ _ _ => rfl) arg
theorem eff_timestamp (arg) : Eff .TIMESTAMP arg (Shape 0 [top]) :=
  eff_state EvmYul.State.timeStamp (fun _ _ _ _ => rfl) arg
theorem eff_number (arg) : Eff .NUMBER arg (Shape 0 [top]) :=
  eff_state EvmYul.State.number (fun _ _ _ _ => rfl) arg
theorem eff_gaslimit (arg) : Eff .GASLIMIT arg (Shape 0 [top]) :=
  eff_state EvmYul.State.gasLimit (fun _ _ _ _ => rfl) arg
theorem eff_chainid (arg) : Eff .CHAINID arg (Shape 0 [top]) :=
  eff_state EvmYul.State.chainId (fun _ _ _ _ => rfl) arg
theorem eff_coinbase (arg) : Eff .COINBASE arg (Shape 0 [top]) :=
  eff_state (.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase) (fun _ _ _ _ => rfl) arg
theorem eff_selfbalance (arg) : Eff .SELFBALANCE arg (Shape 0 [top]) :=
  eff_state EvmYul.State.selfbalance (fun _ _ _ _ => rfl) arg
theorem eff_msize (arg) : Eff .MSIZE arg (Shape 0 [top]) :=
  eff_machine0 MachineState.msize (fun _ _ _ _ => rfl) arg
theorem eff_returndatasize (arg) : Eff .RETURNDATASIZE arg (Shape 0 [top]) :=
  eff_machine0 MachineState.returndatasize (fun _ _ _ _ => rfl) arg

#print axioms eff_sload
#print axioms eff_sstore
#print axioms eff_caller
#print axioms eff_log4
#print axioms eff_returndatacopy
#print axioms eff_jumpdest
#print axioms eff_keccak256

end GolfWhole
