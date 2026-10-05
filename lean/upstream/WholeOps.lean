import WholeUnfold
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition

/-! Opcode congruence: the same instruction maps related states to related states. -/
namespace GolfWhole

theorem rel_stack {owner old new surplus skipped s t}
    (h : DeployedOffset owner old new surplus skipped s t) : s.stack = t.stack := offset_stack h

theorem rel_returnData {owner old new surplus skipped s t}
    (h : DeployedOffset owner old new surplus skipped s t) : s.returnData = t.returnData := by
  simpa only [eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
    congrArg (fun u : EVM.State => u.returnData) h.frame

theorem rel_perm {owner old new surplus skipped s t}
    (h : DeployedOffset owner old new surplus skipped s t) :
    s.executionEnv.perm = t.executionEnv.perm := by
  simpa only [eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
    congrArg (fun u : EVM.State => u.executionEnv.perm) h.frame

theorem rel_mem {owner old new surplus skipped s t}
    (h : DeployedOffset owner old new surplus skipped s t) (w : Operation .EVM) :
    memoryExpansionCost s w = memoryExpansionCost t w := by
  have hs : memoryExpansionCost (eraseCount (deployedFrame s)) w = memoryExpansionCost s w := rfl
  have ht : memoryExpansionCost (eraseCount (deployedFrame t)) w = memoryExpansionCost t w := rfl
  rw [←hs, ←ht, h.frame]

theorem rel_gasCut {owner old new surplus skipped s t}
    (h : DeployedOffset owner old new surplus skipped s t) (w : Operation .EVM)
    (enough : memoryExpansionCost s w ≤ s.gasAvailable.toNat) :
    DeployedOffset owner old new surplus skipped (gasCut s w) (gasCut t w) := by
  have m := rel_mem h w
  refine ⟨?_, h.count, ?_, h.maps⟩
  · have hh := congrArg (fun u : EVM.State => { u with gasAvailable := UInt256.ofNat 0 }) h.frame
    simpa [eraseCount, deployedFrame, eraseMaps, eraseCodeGas, gasCut] using hh
  · change (t.gasAvailable - UInt256.ofNat (memoryExpansionCost t w)).toNat =
      (s.gasAvailable - UInt256.ofNat (memoryExpansionCost s w)).toNat + surplus
    rw [←m]
    exact gas_preservation _ _ _ _ (by
      have : s.gasAvailable.toNat < UInt256.size := s.gasAvailable.val.isLt
      omega) enough h.gas

theorem notIn_transport {oj nj : Array UInt256} (v : Option UInt256)
    (jumps : ∀ x, oj.contains x = true → nj.contains x = true)
    (h : X.notIn v oj = false) : X.notIn v nj = false := by
  cases v with
  | none => simp [X.notIn, X.belongs] at h
  | some x =>
    simp only [X.notIn, X.belongs, Bool.not_eq_false'] at h ⊢
    exact jumps x h

theorem Z_transport {owner old new surplus skipped s t} {oj nj : Array UInt256}
    {w : Operation .EVM}
    (h : DeployedOffset owner old new surplus skipped s t)
    (cost : C' (gasCut t w) w = C' (gasCut s w) w)
    (jumps : ∀ x, oj.contains x = true → nj.contains x = true)
    (z : ZOk oj w s) :
    ZOk nj w t ∧ DeployedOffset owner old new surplus skipped (gasCut s w) (gasCut t w) := by
  have m := rel_mem h w
  have st := rel_stack h
  have cut := rel_gasCut h w z.mem
  have gs := h.gas
  have gc := cut.gas
  have zc := z.cost
  have zs := z.sstore
  refine ⟨⟨?_, ?_, z.defined, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, cut⟩
  · have := z.mem; omega
  · rw [cost]; omega
  · rw [←st]; exact z.inputs
  · rintro ⟨hw, hn⟩
    apply z.jump
    refine ⟨hw, ?_⟩
    cases e : X.notIn s.stack[0]? oj
    · rw [st] at e; rw [notIn_transport _ jumps e] at hn; cases hn
    · rfl
  · rintro ⟨hw, hz, hn⟩
    apply z.jumpi
    refine ⟨hw, by rw [st]; exact hz, ?_⟩
    cases e : X.notIn s.stack[0]? oj
    · rw [st] at e; rw [notIn_transport _ jumps e] at hn; cases hn
    · rfl
  · rw [←st, ←rel_returnData h]; exact z.returndata
  · rw [←st]; exact z.outputs
  · rw [←st, ←rel_perm h]; exact z.static
  · rintro ⟨hw, hg⟩; exact zs ⟨hw, by omega⟩
  · rw [←st]; exact z.create



theorem getD_of {c : ByteArray} {p : UInt256} {x : Operation .EVM × Option (UInt256 × Nat)}
    (h : decode c p = some x) : (decode c p).getD (.STOP, .none) = x := by rw [h]; rfl

theorem X_inv {f : ℕ} {j : Array UInt256} {s : State} {op : Operation .EVM}
    {arg : Option (UInt256 × Nat)} {r : ExecutionResult State}
    (decoded : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (op, arg))
    (ok : X (f + 1) j s = .ok r) :
    ZOk j op s ∧ ∃ n, EVM.step f (C' (gasCut s op) op) (some (op, arg)) (gasCut s op) = .ok n ∧
      (match H n.toMachineState op with
       | none => X f j n = .ok r
       | some o => r = if op == .REVERT then .revert n.gasAvailable o else .success n o) := by
  rw [X_succ, decoded] at ok
  cases hz : Z j op s with
  | error e => rw [hz] at ok; cases ok
  | ok p =>
    obtain ⟨s', c⟩ := p
    obtain ⟨zok, rfl, rfl⟩ := Z_inv hz
    rw [hz] at ok
    refine ⟨zok, ?_⟩
    cases hstep : EVM.step f (C' (gasCut s op) op) (some (op, arg)) (gasCut s op) with
    | error e => simp [hstep, bind, Except.bind] at ok
    | ok n =>
      refine ⟨n, rfl, ?_⟩
      cases hH : H n.toMachineState op with
      | none => simpa [hstep, hH, bind, Except.bind] using ok
      | some o =>
        simp only [hstep, hH, bind, Except.bind] at ok
        split at ok <;> (injection ok with ok; rw [←ok]; simp_all)

theorem X_run {f : ℕ} {j : Array UInt256} {t : State} {op : Operation .EVM}
    {arg : Option (UInt256 × Nat)} {n : State}
    (decoded : (decode t.executionEnv.code t.pc).getD (.STOP, .none) = (op, arg))
    (z : ZOk j op t)
    (step : EVM.step f (C' (gasCut t op) op) (some (op, arg)) (gasCut t op) = .ok n) :
    X (f + 1) j t =
      (match H n.toMachineState op with
       | none => X f j n
       | some o => .ok (if op == .REVERT then .revert n.gasAvailable o else .success n o)) := by
  rw [X_succ, decoded]
  rw [Z_of z]
  simp only [step, bind, Except.bind]
  cases H n.toMachineState op with
  | none => rfl
  | some o => by_cases e : op = .REVERT <;> simp [e]

def advance : Operation .EVM → Option (UInt256 × Nat) → Nat
  | .Push p, arg => if p = .PUSH0 then 1 else match arg with
    | some (_, w) => w + 1
    | none => 1
  | _, _ => 1

/-- Same opcode in both programs maps related states to related states. -/
structure Congruent (op : Operation .EVM) : Prop where
  fuel : ∀ (f g c : ℕ) (arg : Option (UInt256 × Nat)) (u : State),
    EVM.step (f + 1) c (some (op, arg)) u = EVM.step (g + 1) c (some (op, arg)) u
  cost : ∀ {owner old new surplus skipped s t},
    DeployedOffset owner old new surplus skipped s t → C' t op = C' s op
  step : ∀ {owner old new surplus skipped u u' v} (f g c : ℕ) (arg : Option (UInt256 × Nat)),
    DeployedOffset owner old new surplus skipped u u' → c ≤ u.gasAvailable.toNat →
    EVM.step (f + 1) c (some (op, arg)) u = .ok v →
    ∃ v', EVM.step (g + 1) c (some (op, arg)) u' = .ok v' ∧
      DeployedOffset owner old new surplus skipped v v'

def Advances (op : Operation .EVM) : Prop :=
  ∀ (f c : ℕ) (arg : Option (UInt256 × Nat)) (u v : State),
    EVM.step (f + 1) c (some (op, arg)) u = .ok v → v.pc = u.pc + UInt256.ofNat (advance op arg)

def Running (op : Operation .EVM) : Prop := ∀ μ, H μ op = none

def Halting (op : Operation .EVM) : Prop := op = .STOP ∨ op = .RETURN ∨ op = .REVERT

/-- A proved multi-instruction rewrite: from related states at `pc`, a successful
source run reaches a covered point after fewer steps, while the candidate reaches
a related state after a fixed number of interpreter iterations. -/
def Segment (owner : AccountAddress) (old new : ByteArray) (oj nj : Array UInt256)
    (P : UInt256 → Prop) (pc : UInt256) : Prop :=
  ∀ (fuel : ℕ) (s t : State) (surplus skipped : ℕ) (r : ExecutionResult State),
    DeployedOffset owner old new surplus skipped s t → s.pc = pc → X fuel oj s = .ok r →
    ∃ (f : ℕ) (s' t' : State) (surplus' skipped' k : ℕ), f < fuel ∧ X f oj s' = .ok r ∧ P s'.pc ∧
      DeployedOffset owner old new surplus' skipped' s' t' ∧ ∀ g, X (g + 1 + k) nj t = X (g + 1) nj t'

/-- Obligations at one synchronization point. -/
inductive Point (old new : ByteArray) (oj : Array UInt256) (P : UInt256 → Prop) :
    UInt256 → Prop where
  | same (pc : UInt256) (op : Operation .EVM) (arg : Option (UInt256 × Nat))
      (c : Congruent op) (a : Advances op) (run : Running op)
      (o : decode old pc = some (op, arg)) (n : decode new pc = some (op, arg))
      (next : P (pc + UInt256.ofNat (advance op arg))) : Point old new oj P pc
  | halt (pc : UInt256) (op : Operation .EVM) (arg : Option (UInt256 × Nat))
      (c : Congruent op) (h : Halting op)
      (o : (decode old pc).getD (.STOP, .none) = (op, arg))
      (n : (decode new pc).getD (.STOP, .none) = (op, arg)) :
      Point old new oj P pc
  | invalid (pc : UInt256) (o : decode old pc = some (.INVALID, none)) : Point old new oj P pc
  | segment (pc : UInt256)
      (h : ∀ owner nj, (∀ x, oj.contains x = true → nj.contains x = true) →
        Segment owner old new oj nj P pc) : Point old new oj P pc
  | jump (pc : UInt256)
      (o : decode old pc = some (.JUMP, none)) (n : decode new pc = some (.JUMP, none))
      (targets : ∀ x, oj.contains x = true → P x) : Point old new oj P pc
  | jumpi (pc : UInt256)
      (o : decode old pc = some (.JUMPI, none)) (n : decode new pc = some (.JUMPI, none))
      (next : P (pc + UInt256.ofNat 1))
      (targets : ∀ x, oj.contains x = true → P x) : Point old new oj P pc
  | power (pc : UInt256) (p : Operation.POp) (w k : Nat) (nz : p ≠ .PUSH0) (range : k < 256)
      (o : MulPowerAt old pc p w k) (n : ShiftPowerAt new pc p w k)
      (next : P (pc + UInt256.ofNat (w + 1) + UInt256.ofNat 1)) : Point old new oj P pc

def bump (u : State) (c : ℕ) : State :=
  { u with execLength := u.execLength + 1, gasAvailable := u.gasAvailable - UInt256.ofNat c }

def E (x : State) : State := eraseCount (deployedFrame x)

theorem rel_bump {owner old new surplus skipped u u'}
    (h : DeployedOffset owner old new surplus skipped u u') (c : ℕ)
    (enough : c ≤ u.gasAvailable.toNat) :
    DeployedOffset owner old new surplus skipped (bump u c) (bump u' c) := by
  refine ⟨?_, ?_, ?_, h.maps⟩
  · have hh := congrArg (fun x : State => { x with gasAvailable := UInt256.ofNat 0 }) h.frame
    simpa [eraseCount, deployedFrame, eraseMaps, eraseCodeGas, bump] using hh
  · change u.execLength + 1 = (u'.execLength + 1) + skipped
    have := h.count; omega
  · exact gas_preservation _ _ _ _ (by
      have : u.gasAvailable.toNat < UInt256.size := u.gasAvailable.val.isLt
      omega) enough h.gas

/-- A state map that ignores code, gas, account maps and counts. -/
structure Frameless (F : State → State) : Prop where
  erase : ∀ x, E (F x) = E (F (E x))
  gas : ∀ x, (F x).gasAvailable = x.gasAvailable
  count : ∀ x, (F x).execLength = x.execLength
  accounts : ∀ x, (F x).accountMap = x.accountMap
  original : ∀ x, (F x).σ₀ = x.σ₀
  env : ∀ x, (F x).executionEnv = x.executionEnv

theorem Frameless.preserve {F : State → State} (hF : Frameless F)
    {owner old new surplus skipped u u'}
    (h : DeployedOffset owner old new surplus skipped u u') :
    DeployedOffset owner old new surplus skipped (F u) (F u') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change E (F u) = E (F u')
    rw [hF.erase u, hF.erase u']
    exact congrArg (fun x => E (F x)) h.frame
  · rw [hF.count, hF.count]; exact h.count
  · rw [hF.gas, hF.gas]; exact h.gas
  · have m := h.maps
    unfold DeployedMaps Linked at m ⊢
    rw [hF.accounts, hF.accounts, hF.original, hF.original, hF.env, hF.env]
    exact m

def Preserves (T : State → Except EVM.ExecutionException State) : Prop :=
  ∀ {owner old new surplus skipped u u' v},
    DeployedOffset owner old new surplus skipped u u' → T u = .ok v →
    ∃ v', T u' = .ok v' ∧ DeployedOffset owner old new surplus skipped v v'

theorem replace_frameless (stk : Stack UInt256) (d : ℕ) :
    Frameless (fun x => x.replaceStackAndIncrPC stk d) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem binop_preserves (f : Primop.Binary) : Preserves (EVM.execBinOp f) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  unfold EVM.execBinOp at run ⊢
  rw [←st]
  cases hp : u.stack.pop2 with
  | none => rw [hp] at run; cases run
  | some p =>
    obtain ⟨stk, a, b⟩ := p
    rw [hp] at run
    injection run with run
    subst run
    exact ⟨_, rfl, (replace_frameless (stk.push (f a b)) 1).preserve h⟩



theorem unop_preserves (f : Primop.Unary) : Preserves (EVM.execUnOp f) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  unfold EVM.execUnOp at run ⊢
  rw [←st]
  cases hp : u.stack.pop with
  | none => rw [hp] at run; cases run
  | some p =>
    obtain ⟨stk, a⟩ := p
    rw [hp] at run
    injection run with run
    subst run
    exact ⟨_, rfl, (replace_frameless (stk.push (f a)) 1).preserve h⟩

theorem triop_preserves (f : Primop.Ternary) : Preserves (EVM.execTriOp f) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  unfold EVM.execTriOp at run ⊢
  rw [←st]
  cases hp : u.stack.pop3 with
  | none => rw [hp] at run; cases run
  | some p =>
    obtain ⟨stk, a, b, c⟩ := p
    rw [hp] at run
    injection run with run
    subst run
    exact ⟨_, rfl, (replace_frameless (stk.push (f a b c)) 1).preserve h⟩

theorem dup_preserves (n : ℕ) : Preserves (EvmYul.dup n) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  unfold EvmYul.dup at run ⊢
  rw [←st]
  dsimp only at run ⊢
  split at run
  · injection run with run
    subst run
    exact ⟨_, by rw [if_pos (by assumption)], (replace_frameless _ 1).preserve h⟩
  · cases run

theorem swap_preserves (n : ℕ) : Preserves (EvmYul.swap n) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  unfold EvmYul.swap at run ⊢
  rw [←st]
  dsimp only at run ⊢
  split at run
  · injection run with run
    subst run
    exact ⟨_, by rw [if_pos (by assumption)], (replace_frameless _ 1).preserve h⟩
  · cases run

theorem jump_preserves (arg : Option (UInt256 × Nat)) : Preserves (EvmYul.step .JUMP arg) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  have e : ∀ y : State, EvmYul.step .JUMP arg y =
      (match y.stack.pop with
        | some ⟨stack, μ₀⟩ => Except.ok { y with pc := μ₀, stack := stack }
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
    exact ⟨_, rfl, Frameless.preserve
      (F := fun x => { x with pc := a, stack := stk })
      ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩ h⟩

theorem jumpi_preserves (arg : Option (UInt256 × Nat)) : Preserves (EvmYul.step .JUMPI arg) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  have pc := offset_pc h
  have e : ∀ y : State, EvmYul.step .JUMPI arg y =
      (match y.stack.pop2 with
        | some ⟨stack, μ₀, μ₁⟩ =>
          Except.ok { y with pc := if μ₁ != ⟨0⟩ then μ₀ else y.pc + ⟨1⟩, stack := stack }
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
    exact ⟨_, rfl, Frameless.preserve
      (F := fun x => { x with pc := if b != ⟨0⟩ then a else x.pc + ⟨1⟩, stack := stk })
      ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩ h⟩

theorem jumpdest_preserves (arg : Option (UInt256 × Nat)) :
    Preserves (EvmYul.step .JUMPDEST arg) := by
  intro owner old new surplus skipped u u' v h run
  change Except.ok u.incrPC = .ok v at run
  injection run with run
  subst run
  exact ⟨_, rfl, Frameless.preserve (F := fun x => x.incrPC)
    ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩ h⟩

theorem pc_preserves (arg : Option (UInt256 × Nat)) : Preserves (EvmYul.step .PC arg) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  have pc := offset_pc h
  change Except.ok (u.replaceStackAndIncrPC (u.stack.push u.pc)) = .ok v at run
  injection run with run
  subst run
  refine ⟨_, rfl, ?_⟩
  change DeployedOffset _ _ _ _ _ (u.replaceStackAndIncrPC (u.stack.push u.pc))
    (u'.replaceStackAndIncrPC (u'.stack.push u'.pc))
  rw [←st, ←pc]
  exact (replace_frameless _ 1).preserve h

theorem push_preserves (p : Operation.POp) (nz : p ≠ .PUSH0) (arg : Option (UInt256 × Nat)) :
    Preserves (EvmYul.step (.Push p) arg) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  cases arg with
  | none => cases p <;> first | exact False.elim (nz rfl) | cases run
  | some q =>
    obtain ⟨x, w⟩ := q
    have e : ∀ y : State, EvmYul.step (.Push p) (some (x, w)) y =
        .ok (y.replaceStackAndIncrPC (y.stack.push x) (w + 1)) := by
      intro y; cases p <;> first | exact False.elim (nz rfl) | rfl
    rw [e] at run ⊢
    injection run with run
    subst run
    refine ⟨_, rfl, ?_⟩
    rw [←st]
    exact (replace_frameless _ _).preserve h

theorem push0_preserves (arg : Option (UInt256 × Nat)) :
    Preserves (EvmYul.step (.Push .PUSH0) arg) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  change Except.ok (u.replaceStackAndIncrPC (u.stack.push ⟨0⟩)) = .ok v at run
  injection run with run
  subst run
  refine ⟨_, rfl, ?_⟩
  change DeployedOffset _ _ _ _ _ _ (u'.replaceStackAndIncrPC (u'.stack.push ⟨0⟩))
  rw [←st]
  exact (replace_frameless _ 1).preserve h



theorem pop_preserves (arg : Option (UInt256 × Nat)) : Preserves (EvmYul.step (.POP : Operation .EVM) arg) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  have e : ∀ y : State, EvmYul.step (.POP : Operation .EVM) arg y =
      (match y.stack.pop with
        | some ⟨s, _⟩ => Except.ok (y.replaceStackAndIncrPC s)
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
    exact ⟨_, rfl, (replace_frameless stk 1).preserve h⟩

def MachineFrameless (op : MachineState → UInt256 → UInt256 → MachineState) : Prop :=
  ∀ a b stk, Frameless (fun x =>
    ({ x with toMachineState := op x.toMachineState a b } : State).replaceStackAndIncrPC stk)

theorem machine_preserves (op : MachineState → UInt256 → UInt256 → MachineState)
    (free : MachineFrameless op) : Preserves (EVM.binaryMachineStateOp op) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  unfold EVM.binaryMachineStateOp at run ⊢
  rw [←st]
  cases hp : u.stack.pop2 with
  | none => rw [hp] at run; cases run
  | some p =>
    obtain ⟨stk, a, b⟩ := p
    rw [hp] at run
    injection run with run
    subst run
    exact ⟨_, rfl, (free a b stk).preserve h⟩

def GasBlind (op : MachineState → UInt256 → UInt256 → MachineState) : Prop :=
  ∀ μ a b g, (op { μ with gasAvailable := g } a b).activeWords = (op μ a b).activeWords ∧
    (op { μ with gasAvailable := g } a b).memory = (op μ a b).memory ∧
    (op { μ with gasAvailable := g } a b).returnData = (op μ a b).returnData ∧
    (op { μ with gasAvailable := g } a b).H_return = (op μ a b).H_return ∧
    (op μ a b).gasAvailable = μ.gasAvailable
theorem machine_frameless (op : MachineState → UInt256 → UInt256 → MachineState) (blind : GasBlind op) :
    MachineFrameless op := by
  intro a b stk
  refine ⟨fun x => ?_, fun x => (blind x.toMachineState a b (UInt256.ofNat 0)).2.2.2.2, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := blind x.toMachineState a b (UInt256.ofNat 0)
  have m : (E x).toMachineState = { x.toMachineState with gasAvailable := UInt256.ofNat 0 } := rfl
  show E (({ x with toMachineState := op x.toMachineState a b } : State).replaceStackAndIncrPC stk) =
      E (({ E x with toMachineState := op (E x).toMachineState a b } : State).replaceStackAndIncrPC stk)
  rw [m]
  simp only [E, eraseCount, deployedFrame, eraseMaps, eraseCodeGas, EVM.State.replaceStackAndIncrPC,
    EVM.State.incrPC, h1, h2, h3, h4]

theorem mstore_free : MachineFrameless MachineState.mstore := machine_frameless _ fun _ _ _ _ =>
  ⟨rfl, rfl, rfl, rfl, by simp only [MachineState.mstore, MachineState.writeWord, writeBytes]⟩
theorem mstore8_free : MachineFrameless MachineState.mstore8 := machine_frameless _ fun _ _ _ _ =>
  ⟨rfl, rfl, rfl, rfl, by simp only [MachineState.mstore8, writeBytes]⟩
theorem return_free : MachineFrameless MachineState.evmReturn := machine_frameless _ fun _ _ _ _ =>
  ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem revert_free : MachineFrameless MachineState.evmRevert := machine_frameless _ fun _ _ _ _ =>
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem mload_preserves (arg : Option (UInt256 × Nat)) : Preserves (EvmYul.step (.MLOAD : Operation .EVM) arg) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  have e : ∀ y : State, EvmYul.step (.MLOAD : Operation .EVM) arg y =
      (match y.stack.pop with
        | some ⟨s, μ₀⟩ =>
          Except.ok (({ y with toMachineState := (y.toMachineState.mload μ₀).2 } : State).replaceStackAndIncrPC
            (s.push (y.toMachineState.mload μ₀).1))
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
    have value : (u'.toMachineState.mload a).1 = (u.toMachineState.mload a).1 := by
      have hu : (u.toMachineState.mload a).1 = ((E u).toMachineState.mload a).1 := rfl
      have hu' : (u'.toMachineState.mload a).1 = ((E u').toMachineState.mload a).1 := rfl
      rw [hu, hu', show E u = E u' from h.frame]
    refine ⟨_, rfl, ?_⟩
    rw [value]
    exact Frameless.preserve
      (F := fun x => ({ x with toMachineState := (x.toMachineState.mload a).2 } : State).replaceStackAndIncrPC
        (stk.push (u.toMachineState.mload a).1))
      ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩ h

/-- An environment read that does not see the code. -/
def CodeFree (op : ExecutionEnv .EVM → UInt256) : Prop :=
  ∀ I c, op { I with code := c } = op I

theorem env_preserves (op : ExecutionEnv .EVM → UInt256) (free : CodeFree op) :
    Preserves (EVM.executionEnvOp op) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  unfold EVM.executionEnvOp at run ⊢
  injection run with run
  subst run
  have value : op u'.executionEnv = op u.executionEnv := by
    have hu : op u.executionEnv = op (E u).executionEnv := (free _ _).symm
    have hu' : op u'.executionEnv = op (E u').executionEnv := (free _ _).symm
    rw [hu, hu', show E u = E u' from h.frame]
  refine ⟨_, rfl, ?_⟩
  change DeployedOffset _ _ _ _ _ _ (u'.replaceStackAndIncrPC (u'.stack.push (op u'.executionEnv)))
  rw [value, ←st]
  exact (replace_frameless _ 1).preserve h

theorem calldataload_preserves (arg : Option (UInt256 × Nat)) :
    Preserves (EvmYul.step (.CALLDATALOAD : Operation .EVM) arg) := by
  intro owner old new surplus skipped u u' v h run
  have st := rel_stack h
  have e : ∀ y : State, EvmYul.step (.CALLDATALOAD : Operation .EVM) arg y =
      (match y.stack.pop with
        | some ⟨s, μ₀⟩ =>
          Except.ok (y.replaceStackAndIncrPC (s.push (EvmYul.State.calldataload y.toState μ₀)))
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
    have value : EvmYul.State.calldataload u'.toState a = EvmYul.State.calldataload u.toState a := by
      have hu : EvmYul.State.calldataload u.toState a = EvmYul.State.calldataload (E u).toState a := rfl
      have hu' : EvmYul.State.calldataload u'.toState a = EvmYul.State.calldataload (E u').toState a := rfl
      rw [hu, hu', show E u = E u' from h.frame]
    refine ⟨_, rfl, ?_⟩
    rw [value]
    exact (replace_frameless _ 1).preserve h



theorem congruent_of {op : Operation .EVM}
    (T : Option (UInt256 × Nat) → State → Except EVM.ExecutionException State)
    (hstep : ∀ f c arg u, EVM.step (f + 1) c (some (op, arg)) u = T arg (bump u c))
    (hT : ∀ arg, Preserves (T arg))
    (hcost : ∀ s t : State, s.stack = t.stack → C' t op = C' s op) : Congruent op := by
  refine ⟨fun f g c arg u => by rw [hstep, hstep], fun h => hcost _ _ (rel_stack h), ?_⟩
  intro owner old new surplus skipped u u' v f g c arg h enough run
  rw [hstep] at run
  obtain ⟨v', run', rel⟩ := hT arg (rel_bump h c enough) run
  exact ⟨v', by rw [hstep]; exact run', rel⟩



theorem advances_of {op : Operation .EVM}
    (T : Option (UInt256 × Nat) → State → Except EVM.ExecutionException State)
    (hstep : ∀ f c arg u, EVM.step (f + 1) c (some (op, arg)) u = T arg (bump u c))
    (hpc : ∀ arg u v, T arg u = .ok v → v.pc = u.pc + UInt256.ofNat (advance op arg)) :
    Advances op := by
  intro f c arg u v run
  rw [hstep] at run
  exact hpc arg (bump u c) v run

theorem binop_pc (f : Primop.Binary) (u v : State) (run : EVM.execBinOp f u = .ok v) :
    v.pc = u.pc + UInt256.ofNat 1 := by
  unfold EVM.execBinOp at run
  cases hp : u.stack.pop2 with
  | none => rw [hp] at run; cases run
  | some p => obtain ⟨_, _, _⟩ := p; rw [hp] at run; injection run with run; subst run; rfl

theorem unop_pc (f : Primop.Unary) (u v : State) (run : EVM.execUnOp f u = .ok v) :
    v.pc = u.pc + UInt256.ofNat 1 := by
  unfold EVM.execUnOp at run
  cases hp : u.stack.pop with
  | none => rw [hp] at run; cases run
  | some p => obtain ⟨_, _⟩ := p; rw [hp] at run; injection run with run; subst run; rfl

theorem triop_pc (f : Primop.Ternary) (u v : State) (run : EVM.execTriOp f u = .ok v) :
    v.pc = u.pc + UInt256.ofNat 1 := by
  unfold EVM.execTriOp at run
  cases hp : u.stack.pop3 with
  | none => rw [hp] at run; cases run
  | some p => obtain ⟨_, _, _, _⟩ := p; rw [hp] at run; injection run with run; subst run; rfl

theorem dup_pc (n : ℕ) (u v : State) (run : EvmYul.dup n u = .ok v) :
    v.pc = u.pc + UInt256.ofNat 1 := by
  unfold EvmYul.dup at run
  dsimp only at run
  split at run
  · injection run with run; subst run; rfl
  · cases run

theorem swap_pc (n : ℕ) (u v : State) (run : EvmYul.swap n u = .ok v) :
    v.pc = u.pc + UInt256.ofNat 1 := by
  unfold EvmYul.swap at run
  dsimp only at run
  split at run
  · injection run with run; subst run; rfl
  · cases run

theorem machine_pc (op : MachineState → UInt256 → UInt256 → MachineState) (u v : State)
    (run : EVM.binaryMachineStateOp op u = .ok v) : v.pc = u.pc + UInt256.ofNat 1 := by
  unfold EVM.binaryMachineStateOp at run
  cases hp : u.stack.pop2 with
  | none => rw [hp] at run; cases run
  | some p => obtain ⟨_, _, _⟩ := p; rw [hp] at run; injection run with run; subst run; rfl

theorem env_pc (op : ExecutionEnv .EVM → UInt256) (u v : State)
    (run : EVM.executionEnvOp op u = .ok v) : v.pc = u.pc + UInt256.ofNat 1 := by
  unfold EVM.executionEnvOp at run
  injection run with run; subst run; rfl

theorem pop_pc (arg : Option (UInt256 × Nat)) (u v : State)
    (run : EvmYul.step (.POP : Operation .EVM) arg u = .ok v) : v.pc = u.pc + UInt256.ofNat 1 := by
  have e : EvmYul.step (.POP : Operation .EVM) arg u =
      (match u.stack.pop with
        | some ⟨s, _⟩ => Except.ok (u.replaceStackAndIncrPC s)
        | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := rfl
  rw [e] at run
  cases hp : u.stack.pop with
  | none => rw [hp] at run; cases run
  | some p => obtain ⟨_, _⟩ := p; rw [hp] at run; injection run with run; subst run; rfl

theorem mload_pc (arg : Option (UInt256 × Nat)) (u v : State)
    (run : EvmYul.step (.MLOAD : Operation .EVM) arg u = .ok v) : v.pc = u.pc + UInt256.ofNat 1 := by
  have e : EvmYul.step (.MLOAD : Operation .EVM) arg u =
      (match u.stack.pop with
        | some ⟨s, μ₀⟩ =>
          Except.ok (({ u with toMachineState := (u.toMachineState.mload μ₀).2 } : State).replaceStackAndIncrPC
            (s.push (u.toMachineState.mload μ₀).1))
        | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := rfl
  rw [e] at run
  cases hp : u.stack.pop with
  | none => rw [hp] at run; cases run
  | some p => obtain ⟨_, _⟩ := p; rw [hp] at run; injection run with run; subst run; rfl

theorem calldataload_pc (arg : Option (UInt256 × Nat)) (u v : State)
    (run : EvmYul.step (.CALLDATALOAD : Operation .EVM) arg u = .ok v) :
    v.pc = u.pc + UInt256.ofNat 1 := by
  have e : EvmYul.step (.CALLDATALOAD : Operation .EVM) arg u =
      (match u.stack.pop with
        | some ⟨s, μ₀⟩ =>
          Except.ok (u.replaceStackAndIncrPC (s.push (EvmYul.State.calldataload u.toState μ₀)))
        | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := rfl
  rw [e] at run
  cases hp : u.stack.pop with
  | none => rw [hp] at run; cases run
  | some p => obtain ⟨_, _⟩ := p; rw [hp] at run; injection run with run; subst run; rfl

theorem push_pc (p : Operation.POp) (nz : p ≠ .PUSH0) (arg : Option (UInt256 × Nat)) (u v : State)
    (run : EvmYul.step (.Push p) arg u = .ok v) :
    v.pc = u.pc + UInt256.ofNat (advance (.Push p) arg) := by
  cases arg with
  | none => cases p <;> first | exact False.elim (nz rfl) | cases run
  | some q =>
    obtain ⟨x, w⟩ := q
    have e : EvmYul.step (.Push p) (some (x, w)) u =
        .ok (u.replaceStackAndIncrPC (u.stack.push x) (w + 1)) := by
      cases p <;> first | exact False.elim (nz rfl) | rfl
    rw [e] at run
    injection run with run; subst run
    change u.pc + UInt256.ofNat (w + 1) = _
    simp [advance, nz]

theorem jump_pc (arg : Option (UInt256 × Nat)) (f c : ℕ) (u v : State)
    (run : EVM.step (f + 1) c (some (.JUMP, arg)) u = .ok v) :
    ∃ tail, u.stack = v.pc :: tail := by
  have e : EVM.step (f + 1) c (some (.JUMP, arg)) u =
      (match (bump u c).stack.pop with
        | some ⟨stack, μ₀⟩ => Except.ok { bump u c with pc := μ₀, stack := stack }
        | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := rfl
  rw [e] at run
  cases hs : u.stack with
  | nil => simp [bump, hs, Stack.pop] at run
  | cons x tail =>
    have hp : (bump u c).stack.pop = some (tail, x) := by simp [bump, hs, Stack.pop]
    rw [hp] at run
    injection run with run
    subst run
    exact ⟨tail, rfl⟩

theorem jumpi_pc (arg : Option (UInt256 × Nat)) (f c : ℕ) (u v : State)
    (run : EVM.step (f + 1) c (some (.JUMPI, arg)) u = .ok v) :
    ∃ x b tail, u.stack = x :: b :: tail ∧ v.pc = if b != ⟨0⟩ then x else u.pc + ⟨1⟩ := by
  have e : EVM.step (f + 1) c (some (.JUMPI, arg)) u =
      (match (bump u c).stack.pop2 with
        | some ⟨stack, μ₀, μ₁⟩ =>
          Except.ok { bump u c with pc := if μ₁ != ⟨0⟩ then μ₀ else (bump u c).pc + ⟨1⟩, stack := stack }
        | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) := rfl
  rw [e] at run
  match hs : u.stack with
  | [] => simp [bump, hs, Stack.pop2] at run
  | [_] => simp [bump, hs, Stack.pop2] at run
  | x :: b :: tail =>
    have hp : (bump u c).stack.pop2 = some (tail, x, b) := by simp [bump, hs, Stack.pop2]
    rw [hp] at run
    injection run with run
    subst run
    exact ⟨x, b, tail, rfl, rfl⟩

theorem push0_pc (arg : Option (UInt256 × Nat)) (u v : State)
    (run : EvmYul.step (.Push .PUSH0) arg u = .ok v) :
    v.pc = u.pc + UInt256.ofNat (advance (.Push .PUSH0) arg) := by
  change Except.ok (u.replaceStackAndIncrPC (u.stack.push ⟨0⟩)) = .ok v at run
  injection run with run; subst run
  change u.pc + UInt256.ofNat 1 = _
  simp [advance]

#print axioms X_inv
#print axioms X_run
#print axioms Z_transport
#print axioms congruent_of
#print axioms advances_of
#print axioms machine_frameless

end GolfWhole
