import WholeOps
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition

/-! Whole-program refinement from per-instruction obligations. -/
namespace GolfWhole

theorem H_rel {owner old new surplus skipped n n'}
    (h : DeployedOffset owner old new surplus skipped n n') (w : Operation .EVM) :
    H n.toMachineState w = H n'.toMachineState w := by
  have e : n.H_return = n'.H_return := by
    simpa only [eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using
      congrArg (fun u : State => u.H_return) h.frame
  unfold H
  rw [e]

theorem jump_running : Running .JUMP := fun _ => by simp [H]
theorem jumpi_running : Running .JUMPI := fun _ => by simp [H]

theorem jump_congruent : Congruent .JUMP :=
  congruent_of (fun arg => EvmYul.step .JUMP arg) (fun _ _ _ _ => rfl) jump_preserves (fun _ _ _ => rfl)
theorem jumpi_congruent : Congruent .JUMPI :=
  congruent_of (fun arg => EvmYul.step .JUMPI arg) (fun _ _ _ _ => rfl) jumpi_preserves (fun _ _ _ => rfl)

theorem step_zero (c : ℕ) (i : Option (Operation .EVM × Option (UInt256 × Nat))) (u : State) :
    EVM.step 0 c i u = .error .OutOfFuel := rfl

/-- Candidate side of one congruent instruction: the candidate takes the same
step from the related state, for any residual fuel. -/
theorem candidate_step {owner old new surplus skipped s t} {oj nj : Array UInt256}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {f : ℕ} {nx : State}
    (c : Congruent op) (rel : DeployedOffset owner old new surplus skipped s t)
    (jumps : ∀ x, oj.contains x = true → nj.contains x = true)
    (dt : (decode t.executionEnv.code t.pc).getD (.STOP, .none) = (op, arg))
    (z : ZOk oj op s)
    (step : EVM.step (f + 1) (C' (gasCut s op) op) (some (op, arg)) (gasCut s op) = .ok nx) :
    ∃ v', DeployedOffset owner old new surplus skipped nx v' ∧
      ∀ g, X (g + 2) nj t =
        (match H v'.toMachineState op with
         | none => X (g + 1) nj v'
         | some o => .ok (if op == .REVERT then .revert v'.gasAvailable o else .success v' o)) := by
  have cut := rel_gasCut rel op z.mem
  have costEq := c.cost cut
  obtain ⟨zt, -⟩ := Z_transport rel costEq jumps z
  obtain ⟨v', step', rel'⟩ := c.step f 0 _ arg cut z.cost step
  refine ⟨v', rel', fun g => ?_⟩
  have sg : EVM.step (g + 1) (C' (gasCut t op) op) (some (op, arg)) (gasCut t op) = .ok v' := by
    rw [c.fuel g 0, costEq]; exact step'
  exact X_run dt zt sg



theorem whole_refines (owner : AccountAddress) (old new : ByteArray) (oj nj : Array UInt256)
    (P : UInt256 → Prop) (cover : ∀ pc, P pc → Point old new oj P pc)
    (jumps : ∀ x, oj.contains x = true → nj.contains x = true) :
    ∀ (fuel : ℕ) (s t : State) (surplus skipped : ℕ) (r : ExecutionResult State),
      DeployedOffset owner old new surplus skipped s t → P s.pc →
      X fuel oj s = .ok r →
      ∃ f r', X f nj t = .ok r' ∧ OutcomeRelated owner old new r r' := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
  intro s t surplus skipped r rel hp ok
  have sc : s.executionEnv.code = old := rel.maps.2.2.1.2.1
  have tc : t.executionEnv.code = new := rel.maps.2.2.2.2.1
  have samePC := offset_pc rel
  cases fuel with
  | zero => rw [X_zero] at ok; cases ok
  | succ f =>
  cases cover s.pc hp with
  | same op arg c a run o n next =>
    have ds : decode s.executionEnv.code s.pc = some (op, arg) := by rw [sc]; exact o
    have dt : decode t.executionEnv.code t.pc = some (op, arg) := by rw [tc, ←samePC]; exact n
    obtain ⟨z, nx, step, rest⟩ := X_inv (getD_of ds) ok
    rw [run] at rest
    cases f with
    | zero => rw [step_zero] at step; cases step
    | succ f =>
    obtain ⟨v', rel', cand⟩ := candidate_step c rel jumps (getD_of dt) z step
    have npc : nx.pc = (gasCut s op).pc + UInt256.ofNat (advance op arg) :=
      a f (C' (gasCut s op) op) arg (gasCut s op) nx step
    obtain ⟨f', r', run', related⟩ :=
      ih (f + 1) (by omega) nx v' surplus skipped r rel' (by rw [npc]; exact next) rest
    cases f' with
    | zero => rw [X_zero] at run'; cases run'
    | succ g =>
      refine ⟨g + 2, r', ?_, related⟩
      rw [cand g, run v'.toMachineState]
      exact run'
  | halt op arg c h o n =>
    have ds : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (op, arg) := by rw [sc]; exact o
    have dt : (decode t.executionEnv.code t.pc).getD (.STOP, .none) = (op, arg) := by
      rw [tc, ←samePC]; exact n
    obtain ⟨z, nx, step, rest⟩ := X_inv ds ok
    cases f with
    | zero => rw [step_zero] at step; cases step
    | succ f =>
    obtain ⟨v', rel', cand⟩ := candidate_step c rel jumps dt z step
    have hh := H_rel rel' op
    have some : ∃ out, H nx.toMachineState op = some out := by
      rcases h with e | e | e <;> subst e <;> simp [H]
    obtain ⟨out, hout⟩ := some
    rw [hout] at rest hh
    refine ⟨f + 2, _, by rw [cand f, ←hh], ?_⟩
    rw [rest]
    by_cases e : op = .REVERT
    · subst e
      exact ⟨rfl, by have := rel'.gas; simp; omega⟩
    · simp only [e, beq_iff_eq, if_false]
      exact ⟨rfl, surplus, skipped, rel'⟩
  | invalid o =>
    have ds : decode s.executionEnv.code s.pc = some (.INVALID, none) := by rw [sc]; exact o
    obtain ⟨z, -⟩ := X_inv (getD_of ds) ok
    exact absurd rfl z.defined
  | jump o n targets =>
    have ds : decode s.executionEnv.code s.pc = some (.JUMP, none) := by rw [sc]; exact o
    have dt : decode t.executionEnv.code t.pc = some (.JUMP, none) := by rw [tc, ←samePC]; exact n
    obtain ⟨z, nx, step, rest⟩ := X_inv (getD_of ds) ok
    rw [jump_running] at rest
    cases f with
    | zero => rw [step_zero] at step; cases step
    | succ f =>
    obtain ⟨v', rel', cand⟩ := candidate_step jump_congruent rel jumps (getD_of dt) z step
    obtain ⟨tail, stack⟩ := jump_pc none f _ _ nx step
    have valid : oj.contains nx.pc = true := by
      have zj := z.jump
      change s.stack = nx.pc :: tail at stack
      simp only [stack, X.notIn, X.belongs, true_and] at zj
      simpa using zj
    obtain ⟨f', r', run', related⟩ :=
      ih (f + 1) (by omega) nx v' surplus skipped r rel' (targets _ valid) rest
    cases f' with
    | zero => rw [X_zero] at run'; cases run'
    | succ g =>
      refine ⟨g + 2, r', ?_, related⟩
      rw [cand g, jump_running v'.toMachineState]
      exact run'
  | jumpi o n next targets =>
    have ds : decode s.executionEnv.code s.pc = some (.JUMPI, none) := by rw [sc]; exact o
    have dt : decode t.executionEnv.code t.pc = some (.JUMPI, none) := by rw [tc, ←samePC]; exact n
    obtain ⟨z, nx, step, rest⟩ := X_inv (getD_of ds) ok
    rw [jumpi_running] at rest
    cases f with
    | zero => rw [step_zero] at step; cases step
    | succ f =>
    obtain ⟨v', rel', cand⟩ := candidate_step jumpi_congruent rel jumps (getD_of dt) z step
    obtain ⟨x, b, tail, stack, npc⟩ := jumpi_pc none f _ _ nx step
    change s.stack = x :: b :: tail at stack
    change nx.pc = if b != ⟨0⟩ then x else s.pc + ⟨1⟩ at npc
    have target : P nx.pc := by
      by_cases hb : b = ⟨0⟩
      · subst hb
        rw [npc]
        exact next
      · have zj := z.jumpi
        have valid : oj.contains x = true := by
          simp only [stack, X.notIn, X.belongs] at zj
          simpa [hb] using zj
        have hb' : (b != ⟨0⟩) = true := by
          obtain ⟨v⟩ := b
          have hv : v ≠ 0 := fun e => hb (by rw [e])
          have e : ((⟨v⟩ : UInt256) == ⟨0⟩) = (v == 0) := rfl
          simp [bne, e, hv]
        rw [npc, if_pos hb']
        exact targets x valid
    obtain ⟨f', r', run', related⟩ :=
      ih (f + 1) (by omega) nx v' surplus skipped r rel' target rest
    cases f' with
    | zero => rw [X_zero] at run'; cases run'
    | succ g =>
      refine ⟨g + 2, r', ?_, related⟩
      rw [cand g, jumpi_running v'.toMachineState]
      exact run'
  | power p w k nz range o n next =>
    obtain ⟨f2, a, tail, hf, srest, rel', cand⟩ :=
      power_case owner old new s t f surplus skipped oj r p w k nz range rel o n ok
    obtain ⟨f', r', run', related⟩ :=
      ih (f2 + 1) (by omega) _ _ (surplus + 2) skipped r rel' next srest
    cases f' with
    | zero => rw [X_zero] at run'; cases run'
    | succ g => exact ⟨g + 3, r', by rw [cand g nj]; exact run', related⟩


def Same (op : Operation .EVM) : Prop := Congruent op ∧ Advances op ∧ Running op

theorem same_of {op : Operation .EVM}
    (T : Option (UInt256 × Nat) → State → Except EVM.ExecutionException State)
    (hstep : ∀ f c arg u, EVM.step (f + 1) c (some (op, arg)) u = T arg (bump u c))
    (hT : ∀ arg, Preserves (T arg))
    (hcost : ∀ s t : State, s.stack = t.stack → C' t op = C' s op)
    (hpc : ∀ arg u v, T arg u = .ok v → v.pc = u.pc + UInt256.ofNat (advance op arg))
    (run : Running op) : Same op :=
  ⟨congruent_of T hstep hT hcost, advances_of T hstep hpc, run⟩

theorem binary_same {op : Operation .EVM} (f : Primop.Binary)
    (hstep : ∀ fu c arg u, EVM.step (fu + 1) c (some (op, arg)) u = EVM.execBinOp f (bump u c))
    (hcost : ∀ s t : State, s.stack = t.stack → C' t op = C' s op)
    (adv : ∀ arg, advance op arg = 1) (run : Running op) : Same op :=
  same_of (fun _ => EVM.execBinOp f) hstep (fun _ => binop_preserves f) hcost
    (fun arg u v h => by rw [adv]; exact binop_pc f u v h) run

theorem unary_same {op : Operation .EVM} (f : Primop.Unary)
    (hstep : ∀ fu c arg u, EVM.step (fu + 1) c (some (op, arg)) u = EVM.execUnOp f (bump u c))
    (hcost : ∀ s t : State, s.stack = t.stack → C' t op = C' s op)
    (adv : ∀ arg, advance op arg = 1) (run : Running op) : Same op :=
  same_of (fun _ => EVM.execUnOp f) hstep (fun _ => unop_preserves f) hcost
    (fun arg u v h => by rw [adv]; exact unop_pc f u v h) run

theorem ternary_same {op : Operation .EVM} (f : Primop.Ternary)
    (hstep : ∀ fu c arg u, EVM.step (fu + 1) c (some (op, arg)) u = EVM.execTriOp f (bump u c))
    (hcost : ∀ s t : State, s.stack = t.stack → C' t op = C' s op)
    (adv : ∀ arg, advance op arg = 1) (run : Running op) : Same op :=
  same_of (fun _ => EVM.execTriOp f) hstep (fun _ => triop_preserves f) hcost
    (fun arg u v h => by rw [adv]; exact triop_pc f u v h) run

theorem env_same {op : Operation .EVM} (g : ExecutionEnv .EVM → UInt256) (free : CodeFree g)
    (hstep : ∀ fu c arg u, EVM.step (fu + 1) c (some (op, arg)) u = EVM.executionEnvOp g (bump u c))
    (hcost : ∀ s t : State, s.stack = t.stack → C' t op = C' s op)
    (adv : ∀ arg, advance op arg = 1) (run : Running op) : Same op :=
  same_of (fun _ => EVM.executionEnvOp g) hstep (fun _ => env_preserves g free) hcost
    (fun arg u v h => by rw [adv]; exact env_pc g u v h) run

theorem machine_same {op : Operation .EVM} (g : MachineState → UInt256 → UInt256 → MachineState)
    (free : MachineFrameless g)
    (hstep : ∀ fu c arg u, EVM.step (fu + 1) c (some (op, arg)) u = EVM.binaryMachineStateOp g (bump u c))
    (hcost : ∀ s t : State, s.stack = t.stack → C' t op = C' s op)
    (adv : ∀ arg, advance op arg = 1) (run : Running op) : Same op :=
  same_of (fun _ => EVM.binaryMachineStateOp g) hstep (fun _ => machine_preserves g free) hcost
    (fun arg u v h => by rw [adv]; exact machine_pc g u v h) run

theorem dup_same {op : Operation .EVM} (n : ℕ)
    (hstep : ∀ fu c arg u, EVM.step (fu + 1) c (some (op, arg)) u = EvmYul.dup n (bump u c))
    (hcost : ∀ s t : State, s.stack = t.stack → C' t op = C' s op)
    (adv : ∀ arg, advance op arg = 1) (run : Running op) : Same op :=
  same_of (fun _ => EvmYul.dup n) hstep (fun _ => dup_preserves n) hcost
    (fun arg u v h => by rw [adv]; exact dup_pc n u v h) run

theorem swap_same {op : Operation .EVM} (n : ℕ)
    (hstep : ∀ fu c arg u, EVM.step (fu + 1) c (some (op, arg)) u = EvmYul.swap n (bump u c))
    (hcost : ∀ s t : State, s.stack = t.stack → C' t op = C' s op)
    (adv : ∀ arg, advance op arg = 1) (run : Running op) : Same op :=
  same_of (fun _ => EvmYul.swap n) hstep (fun _ => swap_preserves n) hcost
    (fun arg u v h => by rw [adv]; exact swap_pc n u v h) run

macro "same_binary" f:term : term =>
  `(binary_same $f (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => by simp [H]))
macro "same_unary" f:term : term =>
  `(unary_same $f (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => by simp [H]))
macro "same_ternary" f:term : term =>
  `(ternary_same $f (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => by simp [H]))
macro "same_env" g:term : term =>
  `(env_same $g (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => by simp [H]))
macro "same_dup" n:term : term =>
  `(dup_same $n (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => by simp [H]))
macro "same_swap" n:term : term =>
  `(swap_same $n (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => by simp [H]))

theorem same_add : Same .ADD := same_binary UInt256.add
theorem same_mul : Same .MUL := same_binary UInt256.mul
theorem same_sub : Same .SUB := same_binary UInt256.sub
theorem same_div : Same .DIV := same_binary UInt256.div
theorem same_sdiv : Same .SDIV := same_binary UInt256.sdiv
theorem same_mod : Same .MOD := same_binary UInt256.mod
theorem same_smod : Same .SMOD := same_binary UInt256.smod
theorem same_signextend : Same .SIGNEXTEND := same_binary UInt256.signextend
theorem same_lt : Same .LT := same_binary UInt256.lt
theorem same_gt : Same .GT := same_binary UInt256.gt
theorem same_slt : Same .SLT := same_binary UInt256.slt
theorem same_sgt : Same .SGT := same_binary UInt256.sgt
theorem same_eq : Same .EQ := same_binary UInt256.eq
theorem same_and : Same .AND := same_binary UInt256.land
theorem same_or : Same .OR := same_binary UInt256.lor
theorem same_xor : Same .XOR := same_binary UInt256.xor
theorem same_byte : Same .BYTE := same_binary UInt256.byteAt
theorem same_shl : Same .SHL := same_binary (flip UInt256.shiftLeft)
theorem same_shr : Same .SHR := same_binary (flip UInt256.shiftRight)
theorem same_sar : Same .SAR := same_binary UInt256.sar
theorem same_exp : Same .EXP :=
  binary_same UInt256.exp (fun _ _ _ _ => rfl) (fun _ _ h => by simp only [C', h]) (fun _ => rfl)
    (fun _ => by simp [H])
theorem same_iszero : Same .ISZERO := same_unary UInt256.isZero
theorem same_not : Same .NOT := same_unary UInt256.lnot
theorem same_addmod : Same .ADDMOD := same_ternary UInt256.addMod
theorem same_mulmod : Same .MULMOD := same_ternary UInt256.mulMod
theorem same_callvalue : Same .CALLVALUE := same_env ExecutionEnv.weiValue
theorem same_calldatasize : Same .CALLDATASIZE := same_env (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.calldata)
theorem same_caller : Same .CALLER := same_env (.ofNat ∘ Fin.val ∘ ExecutionEnv.source)
theorem same_origin : Same .ORIGIN := same_env (.ofNat ∘ Fin.val ∘ ExecutionEnv.sender)
theorem same_address : Same .ADDRESS := same_env (.ofNat ∘ Fin.val ∘ ExecutionEnv.codeOwner)
theorem same_gasprice : Same .GASPRICE := same_env (.ofNat ∘ ExecutionEnv.gasPrice)
theorem same_mstore : Same .MSTORE :=
  machine_same MachineState.mstore mstore_free (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    (fun _ => by simp [H])
theorem same_mstore8 : Same .MSTORE8 :=
  machine_same MachineState.mstore8 mstore8_free (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    (fun _ => by simp [H])
theorem same_mload : Same .MLOAD :=
  same_of (fun arg => EvmYul.step (.MLOAD : Operation .EVM) arg) (fun _ _ _ _ => rfl) mload_preserves (fun _ _ _ => rfl)
    mload_pc (fun _ => by simp [H])
theorem same_calldataload : Same .CALLDATALOAD :=
  same_of (fun arg => EvmYul.step (.CALLDATALOAD : Operation .EVM) arg) (fun _ _ _ _ => rfl) calldataload_preserves
    (fun _ _ _ => rfl) calldataload_pc (fun _ => by simp [H])
theorem same_pop : Same .POP :=
  same_of (fun arg => EvmYul.step (.POP : Operation .EVM) arg) (fun _ _ _ _ => rfl) pop_preserves (fun _ _ _ => rfl)
    pop_pc (fun _ => by simp [H])
theorem same_jumpdest : Same .JUMPDEST :=
  same_of (fun arg => EvmYul.step (.JUMPDEST : Operation .EVM) arg) (fun _ _ _ _ => rfl) jumpdest_preserves
    (fun _ _ _ => rfl) (fun _ u v h => by injection h with h; subst h; rfl) (fun _ => by simp [H])
theorem same_push (p : Operation.POp) (nz : p ≠ .PUSH0) : Same (.Push p) :=
  same_of (fun arg => EvmYul.step (.Push p) arg)
    (fun _ _ _ _ => by cases p <;> first | exact False.elim (nz rfl) | rfl)
    (push_preserves p nz)
    (fun _ _ _ => by rw [cost_push _ p nz, cost_push _ p nz])
    (push_pc p nz) (fun _ => by simp [H])

theorem same_dup1 : Same .DUP1 := same_dup 1
theorem same_dup2 : Same .DUP2 := same_dup 2
theorem same_dup3 : Same .DUP3 := same_dup 3
theorem same_dup4 : Same .DUP4 := same_dup 4
theorem same_dup5 : Same .DUP5 := same_dup 5
theorem same_dup6 : Same .DUP6 := same_dup 6
theorem same_dup7 : Same .DUP7 := same_dup 7
theorem same_dup8 : Same .DUP8 := same_dup 8
theorem same_dup9 : Same .DUP9 := same_dup 9
theorem same_dup10 : Same .DUP10 := same_dup 10
theorem same_dup11 : Same .DUP11 := same_dup 11
theorem same_dup12 : Same .DUP12 := same_dup 12
theorem same_dup13 : Same .DUP13 := same_dup 13
theorem same_dup14 : Same .DUP14 := same_dup 14
theorem same_dup15 : Same .DUP15 := same_dup 15
theorem same_dup16 : Same .DUP16 := same_dup 16
theorem same_swap1 : Same .SWAP1 := same_swap 1
theorem same_swap2 : Same .SWAP2 := same_swap 2
theorem same_swap3 : Same .SWAP3 := same_swap 3
theorem same_swap4 : Same .SWAP4 := same_swap 4
theorem same_swap5 : Same .SWAP5 := same_swap 5
theorem same_swap6 : Same .SWAP6 := same_swap 6
theorem same_swap7 : Same .SWAP7 := same_swap 7
theorem same_swap8 : Same .SWAP8 := same_swap 8
theorem same_swap9 : Same .SWAP9 := same_swap 9
theorem same_swap10 : Same .SWAP10 := same_swap 10
theorem same_swap11 : Same .SWAP11 := same_swap 11
theorem same_swap12 : Same .SWAP12 := same_swap 12
theorem same_swap13 : Same .SWAP13 := same_swap 13
theorem same_swap14 : Same .SWAP14 := same_swap 14
theorem same_swap15 : Same .SWAP15 := same_swap 15
theorem same_swap16 : Same .SWAP16 := same_swap 16

theorem congruent_stop : Congruent .STOP :=
  congruent_of (fun arg => EvmYul.step (.STOP : Operation .EVM) arg) (fun _ _ _ _ => rfl)
    (fun arg => by
      intro owner old new surplus skipped u u' v h run
      change Except.ok { u with toMachineState := u.toMachineState.setReturnData .empty } = .ok v at run
      injection run with run
      subst run
      exact ⟨_, rfl, Frameless.preserve
        (F := fun x => { x with toMachineState := x.toMachineState.setReturnData .empty })
        ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩ h⟩)
    (fun _ _ _ => rfl)
theorem congruent_return : Congruent .RETURN :=
  congruent_of (fun _ => EVM.binaryMachineStateOp MachineState.evmReturn) (fun _ _ _ _ => rfl)
    (fun _ => machine_preserves _ return_free) (fun _ _ _ => rfl)
theorem congruent_revert : Congruent .REVERT :=
  congruent_of (fun _ => EVM.binaryMachineStateOp MachineState.evmRevert) (fun _ _ _ _ => rfl)
    (fun _ => machine_preserves _ revert_free) (fun _ _ _ => rfl)

theorem same_push0 : Same (.Push .PUSH0) :=
  same_of (fun arg => EvmYul.step (.Push .PUSH0) arg) (fun _ _ _ _ => rfl) push0_preserves
    (fun _ _ _ => rfl) push0_pc (fun _ => by simp [H])

theorem word_eq_of_beq {x y : UInt256} (h : (x == y) = true) : x = y := by
  obtain ⟨a⟩ := x
  obtain ⟨b⟩ := y
  have e : ((⟨a⟩ : UInt256) == ⟨b⟩) = (a == b) := rfl
  rw [e] at h
  rw [eq_of_beq h]

theorem cover_cons {Q : UInt256 → Prop} {a : UInt256} {l : List UInt256} (ha : Q a)
    (hl : ∀ x, l.contains x = true → Q x) : ∀ x, (a :: l).contains x = true → Q x := by
  intro x hx
  simp only [List.contains_cons, Bool.or_eq_true] at hx
  rcases hx with h | h
  · rw [word_eq_of_beq h]; exact ha
  · exact hl x h

theorem cover_nil {Q : UInt256 → Prop} : ∀ x, ([] : List UInt256).contains x = true → Q x := by
  intro x hx; simp at hx

theorem jumps_sub (jumps : Array UInt256) (points : List UInt256)
    (h : jumps.toList.all (fun j => points.contains j) = true) :
    ∀ x, jumps.contains x = true → points.contains x = true := by
  intro x hx
  rw [← Array.contains_toList] at hx
  generalize jumps.toList = l at h hx
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.contains_cons, Bool.or_eq_true] at hx
    rcases hx with e | e
    · rw [word_eq_of_beq e]; exact h.1
    · exact ih h.2 e

#print axioms whole_refines
#print axioms same_push
#print axioms same_push0
#print axioms congruent_stop
#print axioms congruent_return
#print axioms congruent_revert

end GolfWhole
