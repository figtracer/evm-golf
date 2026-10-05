import OffsetTransport
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition

/-! Unfolding and inversion of the canonical interpreter loop `X`. -/
namespace GolfWhole

def W (w : Operation .EVM) (s : Stack UInt256) : Bool :=
  w ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] ∨
  (w = .CALL ∧ s[2]? ≠ some ⟨0⟩)

/-- The exceptional-halting check of `X`, verbatim. -/
def Z (validJumps : Array UInt256) (w : Operation .EVM) (evmState : State) :
    Except EVM.ExecutionException (State × ℕ) := do
  let cost₁ := memoryExpansionCost evmState w
  if evmState.gasAvailable.toNat < cost₁ then
    .error .OutOfGass
  let gasAvailable := evmState.gasAvailable - .ofNat cost₁
  let evmState := { evmState with gasAvailable := gasAvailable}
  let cost₂ := C' evmState w
  if evmState.gasAvailable.toNat < cost₂ then
    .error .OutOfGass
  if δ w = none then
    .error .InvalidInstruction
  if evmState.stack.length < (δ w).getD 0 then
    .error .StackUnderflow
  let invalidJump := X.notIn evmState.stack[0]? validJumps
  if w = .JUMP ∧ invalidJump then
    .error .BadJumpDestination
  if w = .JUMPI ∧ (evmState.stack[1]? ≠ some ⟨0⟩) ∧ invalidJump then
    .error .BadJumpDestination
  if w = .RETURNDATACOPY ∧ (evmState.stack.getD 1 ⟨0⟩).toNat + (evmState.stack.getD 2 ⟨0⟩).toNat > evmState.returnData.size then
    .error .InvalidMemoryAccess
  if evmState.stack.length - (δ w).getD 0 + (α w).getD 0 > 1024 then
    .error .StackOverflow
  if (¬ evmState.executionEnv.perm) ∧ W w evmState.stack then
    .error .StaticModeViolation
  if (w = .SSTORE) ∧ evmState.gasAvailable.toNat ≤ GasConstants.Gcallstipend then
    .error .OutOfGass
  if w.isCreate ∧ evmState.stack.getD 2 ⟨0⟩ > ⟨49152⟩ then
    .error .OutOfGass
  pure (evmState, cost₂)

def H (μ : MachineState) (w : Operation .EVM) : Option ByteArray :=
  if w ∈ [.RETURN, .REVERT] then some <| μ.H_return
  else if w ∈ [.STOP, .SELFDESTRUCT] then some .empty else none

theorem X_succ (f : ℕ) (j : Array UInt256) (s : State) :
    X (f + 1) j s =
      (match Z j (decode s.executionEnv.code s.pc |>.getD (.STOP, .none)).1 s with
       | .error e => .error e
       | .ok (s', c) => do
          let n ← EVM.step f c (decode s.executionEnv.code s.pc |>.getD (.STOP, .none)) s'
          match H n.toMachineState (decode s.executionEnv.code s.pc |>.getD (.STOP, .none)).1 with
          | none => X f j n
          | some o =>
            if (decode s.executionEnv.code s.pc |>.getD (.STOP, .none)).1 == .REVERT then
              .ok (.revert n.gasAvailable o)
            else .ok (.success n o)) := by
  conv_lhs => unfold X
  rfl



def gasCut (s : State) (w : Operation .EVM) : State :=
  { s with gasAvailable := s.gasAvailable - .ofNat (memoryExpansionCost s w) }

structure ZOk (j : Array UInt256) (w : Operation .EVM) (s : State) : Prop where
  mem : memoryExpansionCost s w ≤ s.gasAvailable.toNat
  cost : C' (gasCut s w) w ≤ (gasCut s w).gasAvailable.toNat
  defined : δ w ≠ none
  inputs : (δ w).getD 0 ≤ s.stack.length
  jump : ¬(w = .JUMP ∧ X.notIn s.stack[0]? j = true)
  jumpi : ¬(w = .JUMPI ∧ s.stack[1]? ≠ some ⟨0⟩ ∧ X.notIn s.stack[0]? j = true)
  returndata : ¬(w = .RETURNDATACOPY ∧ (s.stack.getD 1 ⟨0⟩).toNat + (s.stack.getD 2 ⟨0⟩).toNat > s.returnData.size)
  outputs : ¬(s.stack.length - (δ w).getD 0 + (α w).getD 0 > 1024)
  static : ¬((¬ s.executionEnv.perm) ∧ W w s.stack = true)
  sstore : ¬((w = .SSTORE) ∧ (gasCut s w).gasAvailable.toNat ≤ GasConstants.Gcallstipend)
  create : ¬(w.isCreate = true ∧ s.stack.getD 2 ⟨0⟩ > ⟨49152⟩)

theorem Z_inv {j w s s' c} (h : Z j w s = .ok (s', c)) :
    ZOk j w s ∧ s' = gasCut s w ∧ c = C' (gasCut s w) w := by
  unfold Z at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  by_cases h1 : s.gasAvailable.toNat < memoryExpansionCost s w
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : C' (gasCut s w) w ≤ (gasCut s w).gasAvailable.toNat
  swap
  · rw [if_pos (by simpa [gasCut] using h2)] at h; cases h
  rw [if_neg (by simpa [gasCut] using h2)] at h
  by_cases h3 : δ w = none
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3] at h
  by_cases h4 : s.stack.length < (δ w).getD 0
  · rw [if_pos (by simpa using h4)] at h; cases h
  rw [if_neg (by simpa using h4)] at h
  by_cases h5 : w = .JUMP ∧ X.notIn s.stack[0]? j = true
  · rw [if_pos h5] at h; cases h
  rw [if_neg h5] at h
  by_cases h6 : w = .JUMPI ∧ s.stack[1]? ≠ some ⟨0⟩ ∧ X.notIn s.stack[0]? j = true
  · rw [if_pos h6] at h; cases h
  rw [if_neg h6] at h
  by_cases h7 : w = .RETURNDATACOPY ∧ (s.stack.getD 1 ⟨0⟩).toNat + (s.stack.getD 2 ⟨0⟩).toNat > s.returnData.size
  · rw [if_pos h7] at h; cases h
  rw [if_neg h7] at h
  by_cases h8 : s.stack.length - (δ w).getD 0 + (α w).getD 0 > 1024
  · rw [if_pos h8] at h; cases h
  rw [if_neg h8] at h
  by_cases h9 : (¬ s.executionEnv.perm) ∧ W w s.stack = true
  · rw [if_pos h9] at h; cases h
  rw [if_neg h9] at h
  by_cases h10 : (w = .SSTORE) ∧ (gasCut s w).gasAvailable.toNat ≤ GasConstants.Gcallstipend
  · rw [if_pos (by simpa [gasCut] using h10)] at h; cases h
  rw [if_neg (by simpa [gasCut] using h10)] at h
  by_cases h11 : w.isCreate = true ∧ s.stack.getD 2 ⟨0⟩ > ⟨49152⟩
  · rw [if_pos h11] at h; cases h
  rw [if_neg h11] at h
  injection h with h
  injection h with e1 e2
  exact ⟨⟨by omega, h2, h3, by omega, h5, h6, h7, h8, h9, h10, h11⟩, e1.symm, e2.symm⟩

theorem Z_of {j w s} (h : ZOk j w s) : Z j w s = .ok (gasCut s w, C' (gasCut s w) w) := by
  have c1 := h.mem
  have c2 := h.cost
  have c4 := h.inputs
  unfold Z
  simp only [bind, Except.bind, pure, Except.pure]
  rw [if_neg (by omega), if_neg (by simpa [gasCut] using c2), if_neg h.defined,
    if_neg (by simpa using c4), if_neg h.jump, if_neg h.jumpi, if_neg h.returndata,
    if_neg h.outputs, if_neg h.static, if_neg (by simpa [gasCut] using h.sstore), if_neg h.create]
  rfl

-- One layer of X for supported nonterminal stack operations, given bounds.
theorem X_bind (s : EVM.State) (fuel : Nat) (jumps : Array UInt256)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (allowed : NonterminalStackOp op)
    (decoded : decode s.executionEnv.code s.pc = some (op, arg))
    (bounds : FullXBounds s op) :
    X (fuel + 1) jumps s =
      (EVM.step fuel (C' s op) (some (op, arg)) s >>= fun n => X fuel jumps n) := by
  have gas := bounds.gas
  have inputs := bounds.inputs
  have outputs := bounds.outputs
  cases allowed with
  | push p nonzero =>
    conv_lhs => unfold X
    simp only [decoded]
    simp [mem_push, cost_push s p nonzero, Operation.isCreate, δ, α,
      show ¬s.gasAvailable.toNat < 3 by simpa [cost_push s p nonzero] using Nat.not_lt.mpr gas,
      show ¬1024 < s.stack.length + 1 by simpa [δ, α] using Nat.not_lt.mpr outputs]
    rfl
  | mul =>
    conv_lhs => unfold X
    simp only [decoded]
    simp [mem_mul, cost_mul, Operation.isCreate, δ, α,
      show ¬s.gasAvailable.toNat < 5 by exact Nat.not_lt.mpr gas,
      show ¬s.stack.length < 2 by exact Nat.not_lt.mpr inputs,
      show ¬1024 < s.stack.length - 2 + 1 by exact Nat.not_lt.mpr outputs]
    rfl
  | shl =>
    conv_lhs => unfold X
    simp only [decoded]
    simp [mem_shl, cost_shl, Operation.isCreate, δ, α,
      show ¬s.gasAvailable.toNat < 3 by exact Nat.not_lt.mpr gas,
      show ¬s.stack.length < 2 by exact Nat.not_lt.mpr inputs,
      show ¬1024 < s.stack.length - 2 + 1 by exact Nat.not_lt.mpr outputs]
    rfl

theorem ok_bounds (s : EVM.State) (fuel : Nat) (jumps : Array UInt256)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat)) (r : ExecutionResult EVM.State)
    (allowed : NonterminalStackOp op)
    (decoded : decode s.executionEnv.code s.pc = some (op, arg))
    (ok : X (fuel + 1) jumps s = .ok r) : FullXBounds s op := by
  unfold X at ok
  simp only [decoded] at ok
  cases allowed with
  | push p nonzero =>
    refine ⟨?_, ?_, ?_⟩
    · by_contra h
      simp [mem_push, cost_push s p nonzero] at h ok
      simp [cost_push s p nonzero, h, bind, Except.bind] at ok
    · simp [δ]
    · by_contra h
      simp [mem_push, cost_push s p nonzero, δ, α] at h ok
      simp [bind, Except.bind] at ok
      split_ifs at ok <;> first | simp at ok | omega
  | mul =>
    refine ⟨?_, ?_, ?_⟩
    · by_contra h
      simp [mem_mul, cost_mul] at h ok
      simp [h, bind, Except.bind] at ok
    · by_contra h
      simp [mem_mul, cost_mul, δ] at h ok
      simp [bind, Except.bind] at ok
      split_ifs at ok <;> first | simp at ok | omega
    · by_contra h
      simp [mem_mul, cost_mul, δ, α] at h ok
      simp [bind, Except.bind] at ok
      split_ifs at ok <;> first | simp at ok | omega
  | shl =>
    refine ⟨?_, ?_, ?_⟩
    · by_contra h
      simp [mem_shl, cost_shl] at h ok
      simp [h, bind, Except.bind] at ok
    · by_contra h
      simp [mem_shl, cost_shl, δ] at h ok
      simp [bind, Except.bind] at ok
      split_ifs at ok <;> first | simp at ok | omega
    · by_contra h
      simp [mem_shl, cost_shl, δ, α] at h ok
      simp [bind, Except.bind] at ok
      split_ifs at ok <;> first | simp at ok | omega

/-- A successful source execution through a supported stack operation exposes
its bounds, its canonical step, and a successful residual execution. -/
theorem X_ok_inv (s : EVM.State) (fuel : Nat) (jumps : Array UInt256)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat)) (r : ExecutionResult EVM.State)
    (allowed : NonterminalStackOp op)
    (decoded : decode s.executionEnv.code s.pc = some (op, arg))
    (ok : X (fuel + 1) jumps s = .ok r) :
    FullXBounds s op ∧ ∃ f next, fuel = f + 1 ∧
      EVM.step (f + 1) (C' s op) (some (op, arg)) s = .ok next ∧
      X (f + 1) jumps next = .ok r := by
  have bounds := ok_bounds s fuel jumps op arg r allowed decoded ok
  refine ⟨bounds, ?_⟩
  rw [X_bind s fuel jumps op arg allowed decoded bounds] at ok
  cases fuel with
  | zero => simp [EVM.step, bind, Except.bind] at ok
  | succ f =>
    cases h : EVM.step (f + 1) (C' s op) (some (op, arg)) s with
    | error e => simp [h, bind, Except.bind] at ok
    | ok next => exact ⟨f, next, rfl, h, by simpa [h, bind, Except.bind] using ok⟩

theorem X_stop_inv (s : EVM.State) (fuel : Nat) (jumps : Array UInt256)
    (r : ExecutionResult EVM.State)
    (decoded : decode s.executionEnv.code s.pc = some (.STOP, none))
    (ok : X (fuel + 1) jumps s = .ok r) :
    s.stack.length ≤ 1024 ∧ r = .success (stopped s) ByteArray.empty := by
  have height : s.stack.length ≤ 1024 := by
    by_contra h
    unfold X at ok
    simp [decoded, mem_stop, cost_stop, Operation.isCreate, δ, α] at ok
    simp [bind, Except.bind] at ok
    split_ifs at ok <;> first | simp at ok | omega
  refine ⟨height, ?_⟩
  cases fuel with
  | zero =>
    unfold X at ok
    simp [decoded, mem_stop, cost_stop, Operation.isCreate, δ, α,
      show ¬1024 < s.stack.length by omega] at ok
    simp [EVM.step, bind, Except.bind, pure, Except.pure] at ok
  | succ f =>
    rw [X_stop s f jumps decoded height] at ok
    exact (Except.ok.inj ok).symm

theorem offset_stopped {owner old new surplus skipped s t}
    (h : DeployedOffset owner old new surplus skipped s t) :
    DeployedOffset owner old new surplus skipped (stopped s) (stopped t) := by
  refine ⟨?_, ?_, h.gas, h.maps⟩
  · have hh := congrArg (fun st : EVM.State => { st with returnData := ByteArray.empty }) h.frame
    simpa [eraseCount, deployedFrame, eraseMaps, eraseCodeGas, stopped] using hh
  · change s.execLength + 1 = (t.execLength + 1) + skipped
    have := h.count
    omega

def OutcomeRelated (owner : AccountAddress) (old new : ByteArray) :
    ExecutionResult EVM.State → ExecutionResult EVM.State → Prop
  | .success s o, .success t o' => o = o' ∧ ∃ surplus skipped, DeployedOffset owner old new surplus skipped s t
  | .revert g o, .revert g' o' => o = o' ∧ g.toNat ≤ g'.toNat
  | _, _ => False

theorem X_zero (j : Array UInt256) (s : EVM.State) : X 0 j s = .error .OutOfFuel := by
  unfold X; rfl

theorem two_stack (s : EVM.State) (two : 2 ≤ s.stack.length) :
    ∃ b a tail, s.stack = b :: a :: tail := by
  match hs : s.stack, two with
  | b :: a :: tail, _ => exact ⟨b, a, tail, rfl⟩

theorem power_case (owner : AccountAddress) (old new : ByteArray)
    (s t : EVM.State) (fuel surplus skipped : Nat) (oj : Array UInt256)
    (r : ExecutionResult EVM.State) (p : Operation.POp) (w k : Nat)
    (nz : p ≠ .PUSH0) (range : k < 256)
    (rel : DeployedOffset owner old new surplus skipped s t)
    (o : MulPowerAt old s.pc p w k) (n : ShiftPowerAt new s.pc p w k)
    (ok : X (fuel + 1) oj s = .ok r) :
    ∃ f a tail, fuel = f + 2 ∧ X (f + 1) oj (mulPowerPost s old w k a tail) = .ok r ∧
      DeployedOffset owner old new (surplus + 2) skipped
        (mulPowerPost s old w k a tail) (shiftPowerPost t new w k a tail) ∧
      ∀ g nj, X (g + 3) nj t = X (g + 1) nj (shiftPowerPost t new w k a tail) := by
  have sc : s.executionEnv.code = old := rel.maps.2.2.1.2.1
  have samePC := offset_pc rel
  have ds : decode s.executionEnv.code s.pc = some (.Push p, some (UInt256.ofNat (2^k), w)) := by
    rw [sc]; exact o.1
  obtain ⟨b1, f1, next, rfl, step1, rest1⟩ :=
    X_ok_inv s fuel oj (.Push p) _ r (.push p nz) ds ok
  rw [cost_push s p nz, step_push s p _ w f1 3 nz] at step1
  injection step1 with hn
  subst hn
  have ds2 : decode (s.executionEnv.code) (s.pc + UInt256.ofNat (w + 1)) = some (.MUL, none) := by
    rw [sc]; exact o.2
  obtain ⟨b2, f2, -, rfl, -, -⟩ := X_ok_inv _ f1 oj .MUL none r .mul ds2 rest1
  have g1 : 3 ≤ s.gasAvailable.toNat := by have := b1.gas; rwa [cost_push s p nz] at this
  have g2 := b2.gas
  simp only [cost_mul] at g2
  rw [word_sub_toNat s.gasAvailable 3 (by decide) g1] at g2
  have gas : 8 ≤ s.gasAvailable.toNat := by omega
  have inputs := b2.inputs
  simp [δ] at inputs
  obtain ⟨a, tail, stack⟩ : ∃ a tail, s.stack = a :: tail := by
    match hs : s.stack, inputs with
    | a :: tail, _ => exact ⟨a, tail, rfl⟩
  have outputs := b1.outputs
  simp [δ, α] at outputs
  have height : s.stack.length < 1024 := by omega
  have nt : ShiftPowerAt new t.pc p w k := by rw [←samePC]; exact n
  have bd := offset_power_boundary owner old new s t p w k surplus skipped a tail f2 0 oj oj
    rel nz range o nt stack gas height
  refine ⟨f2, a, tail, rfl, by rw [←bd.1]; exact ok, bd.2.2, ?_⟩
  intro g nj
  exact (offset_power_boundary owner old new s t p w k surplus skipped a tail f2 g oj nj
    rel nz range o nt stack gas height).2.1

#print axioms X_succ
#print axioms Z_inv
#print axioms Z_of
#print axioms X_ok_inv
#print axioms X_stop_inv
#print axioms power_case

end GolfWhole
