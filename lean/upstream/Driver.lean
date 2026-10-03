import EvmYul.EVM.Semantics

/-! Canonical EVM region proof support against the pinned upstream semantics. -/
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM
namespace GolfUpstream

@[simp] theorem word_sub_zero (a : UInt256) : a - UInt256.ofNat 0 = a := by
  change UInt256.mk (a.val - 0) = a
  simp

def binaryPost (s : EVM.State) (value : UInt256) (tail : List UInt256) (cost : Nat) : EVM.State :=
  { s with
    stack := value :: tail
    pc := s.pc + UInt256.ofNat 1
    gasAvailable := s.gasAvailable - UInt256.ofNat cost
    execLength := s.execLength + 1 }

@[simp] theorem mem_mul (s : EVM.State) : memoryExpansionCost s .MUL = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

@[simp] theorem cost_mul (s : EVM.State) : C' s .MUL = 5 := by rfl

theorem X_mul (s : EVM.State) (a b : UInt256) (tail : List UInt256) (fuel : Nat)
    (jumps : Array UInt256)
    (decoded : decode s.executionEnv.code s.pc = some (.MUL, none))
    (stack : s.stack = b :: a :: tail)
    (gas : 5 ≤ s.gasAvailable.toNat)
    (height : tail.length < 1024) :
    X (fuel + 2) jumps s = X (fuel + 1) jumps (binaryPost s (UInt256.mul b a) tail 5) := by
  conv_lhs => unfold X
  simp only [decoded]
  simp [mem_mul, cost_mul, Operation.isCreate, δ, α, EVM.step,
    EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, Stack.push,
    binaryPost, stack, show ¬s.gasAvailable.toNat < 5 by omega,
    show ¬1024 < tail.length + 1 by omega]
  rfl

@[simp] theorem mem_shl (s : EVM.State) : memoryExpansionCost s .SHL = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

@[simp] theorem cost_shl (s : EVM.State) : C' s .SHL = 3 := by rfl

theorem X_shl (s : EVM.State) (a b : UInt256) (tail : List UInt256) (fuel : Nat)
    (jumps : Array UInt256)
    (decoded : decode s.executionEnv.code s.pc = some (.SHL, none))
    (stack : s.stack = b :: a :: tail)
    (gas : 3 ≤ s.gasAvailable.toNat)
    (height : tail.length < 1024) :
    X (fuel + 2) jumps s = X (fuel + 1) jumps (binaryPost s (UInt256.shiftLeft a b) tail 3) := by
  conv_lhs => unfold X
  simp only [decoded]
  simp [mem_shl, cost_shl, Operation.isCreate, δ, α, EVM.step,
    EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, Stack.push,
    binaryPost, stack, show ¬s.gasAvailable.toNat < 3 by omega,
    show ¬1024 < tail.length + 1 by omega]
  rfl

theorem word_sub_toNat (g : UInt256) (n : Nat) (small : n < UInt256.size)
    (enough : n ≤ g.toNat) :
    (g - UInt256.ofNat n).toNat = g.toNat - n := by
  change (g.val - Fin.ofNat UInt256.size n).val = g.val.val - n
  have val : (Fin.ofNat UInt256.size n).val = n := Nat.mod_eq_of_lt small
  rw [Fin.sub_val_of_le]
  · rw [val]
  · change (Fin.ofNat UInt256.size n).val ≤ g.val.val
    simpa only [val] using enough

def withCode (s : EVM.State) (code : ByteArray) : EVM.State :=
  { s with executionEnv := { s.executionEnv with code := code } }

def eraseCodeGas (s : EVM.State) : EVM.State :=
  { s with
    executionEnv := { s.executionEnv with code := ByteArray.empty }
    gasAvailable := UInt256.ofNat 0 }

def pushedWidth (s : EVM.State) (v : UInt256) (width : Nat) : EVM.State :=
  { s with
    stack := v :: s.stack
    pc := s.pc + UInt256.ofNat (width + 1)
    gasAvailable := s.gasAvailable - UInt256.ofNat 3
    execLength := s.execLength + 1 }

@[simp] theorem mem_push (s : EVM.State) (p : Operation.POp) :
    memoryExpansionCost s (.Push p) = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

theorem cost_push (s : EVM.State) (p : Operation.POp) (nonzero : p ≠ .PUSH0) :
    C' s (.Push p) = 3 := by
  cases p <;> first | exact False.elim (nonzero rfl) | rfl

theorem step_push (s : EVM.State) (p : Operation.POp) (v : UInt256)
    (width fuel cost : Nat) (nonzero : p ≠ .PUSH0) :
    EVM.step (fuel + 1) cost (some (.Push p, some (v, width))) s =
      .ok { s with
        stack := v :: s.stack
        pc := s.pc + UInt256.ofNat (width + 1)
        gasAvailable := s.gasAvailable - UInt256.ofNat cost
        execLength := s.execLength + 1 } := by
  cases p <;> first | exact False.elim (nonzero rfl) | rfl

theorem X_push_width (s : EVM.State) (p : Operation.POp) (v : UInt256)
    (width fuel : Nat) (jumps : Array UInt256) (nonzero : p ≠ .PUSH0)
    (decoded : decode s.executionEnv.code s.pc = some (.Push p, some (v, width)))
    (gas : 3 ≤ s.gasAvailable.toNat) (height : s.stack.length < 1024) :
    X (fuel + 2) jumps s = X (fuel + 1) jumps (pushedWidth s v width) := by
  conv_lhs => unfold X
  simp only [decoded]
  simp [mem_push, cost_push s p nonzero, Operation.isCreate, δ, α,
    show ¬s.gasAvailable.toNat < 3 by omega,
    show ¬1024 < s.stack.length + 1 by omega]
  change (do
    let next ← EVM.step (fuel + 1) 3 (some (.Push p, some (v, width))) s
    X (fuel + 1) jumps next) = _
  rw [step_push s p v width fuel 3 nonzero]
  rfl

def stopped (s : EVM.State) : EVM.State :=
  { s with returnData := ByteArray.empty, execLength := s.execLength + 1 }

@[simp] theorem mem_stop (s : EVM.State) : memoryExpansionCost s .STOP = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

@[simp] theorem cost_stop (s : EVM.State) : C' s .STOP = 0 := by rfl

theorem X_stop (s : EVM.State) (fuel : Nat) (jumps : Array UInt256)
    (decoded : decode s.executionEnv.code s.pc = some (.STOP, none))
    (height : s.stack.length ≤ 1024) :
    X (fuel + 2) jumps s = .ok (.success (stopped s) ByteArray.empty) := by
  conv_lhs => unfold X
  simp [decoded, mem_stop, cost_stop, Operation.isCreate, δ, α, EVM.step,
    stopped, show ¬1024 < s.stack.length by omega]
  change Except.ok (ExecutionResult.success (stopped { s with gasAvailable := s.gasAvailable - UInt256.ofNat 0 }) ByteArray.empty) = _
  rw [word_sub_zero]
  rfl

inductive NonterminalStackOp : Operation .EVM → Prop where
  | push (p : Operation.POp) (nonzero : p ≠ .PUSH0) : NonterminalStackOp (.Push p)
  | mul : NonterminalStackOp .MUL
  | shl : NonterminalStackOp .SHL

structure FullXBounds (s : EVM.State) (op : Operation .EVM) : Prop where
  gas : C' s op ≤ s.gasAvailable.toNat
  inputs : (δ op).getD 0 ≤ s.stack.length
  outputs : s.stack.length - (δ op).getD 0 + (α op).getD 0 ≤ 1024

theorem gas_preservation :
  ∀ (baseline candidate : UInt256) (cost surplus : Nat),
    cost < UInt256.size → cost ≤ baseline.toNat →
    candidate.toNat = baseline.toNat + surplus →
    (candidate - UInt256.ofNat cost).toNat =
      (baseline - UInt256.ofNat cost).toNat + surplus := by
  intro baseline candidate cost surplus small enough related
  have candidateEnough : cost ≤ candidate.toNat := by omega
  rw [word_sub_toNat baseline cost small enough,
    word_sub_toNat candidate cost small candidateEnough]
  omega

theorem X_next (s next : EVM.State) (fuel : Nat) (jumps : Array UInt256)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (allowed : NonterminalStackOp op)
    (decoded : decode s.executionEnv.code s.pc = some (op, arg))
    (bounds : FullXBounds s op)
    (canonical : EVM.step (fuel + 1) (C' s op) (some (op, arg)) s = .ok next) :
    X (fuel + 2) jumps s = X (fuel + 1) jumps next := by
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
    change (do
      let n ← EVM.step (fuel + 1) 3 (some (.Push p, arg)) s
      X (fuel + 1) jumps n) = _
    rw [show EVM.step (fuel + 1) 3 (some (.Push p, arg)) s = .ok next by
      simpa [cost_push s p nonzero] using canonical]
    rfl
  | mul =>
    conv_lhs => unfold X
    simp only [decoded]
    simp [mem_mul, cost_mul, Operation.isCreate, δ, α,
      show ¬s.gasAvailable.toNat < 5 by exact Nat.not_lt.mpr gas,
      show ¬s.stack.length < 2 by exact Nat.not_lt.mpr inputs,
      show ¬1024 < s.stack.length - 2 + 1 by exact Nat.not_lt.mpr outputs]
    change (do
      let n ← EVM.step (fuel + 1) 5 (some (.MUL, arg)) s
      X (fuel + 1) jumps n) = _
    rw [cost_mul] at canonical
    rw [canonical]
    rfl
  | shl =>
    conv_lhs => unfold X
    simp only [decoded]
    simp [mem_shl, cost_shl, Operation.isCreate, δ, α,
      show ¬s.gasAvailable.toNat < 3 by exact Nat.not_lt.mpr gas,
      show ¬s.stack.length < 2 by exact Nat.not_lt.mpr inputs,
      show ¬1024 < s.stack.length - 2 + 1 by exact Nat.not_lt.mpr outputs]
    change (do
      let n ← EVM.step (fuel + 1) 3 (some (.SHL, arg)) s
      X (fuel + 1) jumps n) = _
    rw [cost_shl] at canonical
    rw [canonical]
    rfl

theorem step_mul (s : EVM.State) (fuel cost : Nat) (arg : Option (UInt256 × Nat))
    (a b : UInt256) (tail : List UInt256) (stack : s.stack = b :: a :: tail) :
    EVM.step (fuel + 1) cost (some (.MUL, arg)) s =
      .ok (binaryPost s (UInt256.mul b a) tail cost) := by
  simp [EVM.step, stack, binaryPost, EVM.State.replaceStackAndIncrPC,
    EVM.State.incrPC, Stack.push]
  rfl

theorem step_shl (s : EVM.State) (fuel cost : Nat) (arg : Option (UInt256 × Nat))
    (a b : UInt256) (tail : List UInt256) (stack : s.stack = b :: a :: tail) :
    EVM.step (fuel + 1) cost (some (.SHL, arg)) s =
      .ok (binaryPost s (UInt256.shiftLeft a b) tail cost) := by
  simp [EVM.step, stack, binaryPost, EVM.State.replaceStackAndIncrPC,
    EVM.State.incrPC, Stack.push]
  rfl

inductive ExtendedStackOp : Operation .EVM → Prop where
  | add : ExtendedStackOp .ADD
  | swap1 : ExtendedStackOp .SWAP1
  | push0 : ExtendedStackOp .PUSH0
  | dup1 : ExtendedStackOp .DUP1

@[simp] theorem mem_add (s : EVM.State) : memoryExpansionCost s .ADD = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

@[simp] theorem cost_add (s : EVM.State) : C' s .ADD = 3 := rfl

@[simp] theorem mem_swap1 (s : EVM.State) : memoryExpansionCost s .SWAP1 = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

@[simp] theorem cost_swap1 (s : EVM.State) : C' s .SWAP1 = 3 := rfl

@[simp] theorem mem_push0 (s : EVM.State) : memoryExpansionCost s .PUSH0 = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

@[simp] theorem cost_push0 (s : EVM.State) : C' s .PUSH0 = 2 := rfl

@[simp] theorem mem_dup1 (s : EVM.State) : memoryExpansionCost s .DUP1 = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

@[simp] theorem cost_dup1 (s : EVM.State) : C' s .DUP1 = 3 := rfl

theorem step_add (s : EVM.State) (fuel cost : Nat) (arg : Option (UInt256 × Nat))
    (a b : UInt256) (tail : List UInt256) (stack : s.stack = b :: a :: tail) :
    EVM.step (fuel+1) cost (some (.ADD,arg)) s =
      .ok (binaryPost s (UInt256.add b a) tail cost) := by
  simp [EVM.step, stack, binaryPost, EVM.State.replaceStackAndIncrPC,
    EVM.State.incrPC, Stack.push]
  rfl

theorem step_swap1 (s : EVM.State) (fuel cost : Nat) (arg : Option (UInt256 × Nat))
    (a b : UInt256) (tail : List UInt256) (stack : s.stack = b :: a :: tail) :
    EVM.step (fuel+1) cost (some (.SWAP1,arg)) s =
      .ok (binaryPost s a (b :: tail) cost) := by
  simp [EVM.step, stack, binaryPost, EVM.State.replaceStackAndIncrPC,
    EVM.State.incrPC, EvmYul.swap]
  rfl

theorem step_dup1 (s : EVM.State) (fuel cost : Nat) (arg : Option (UInt256 × Nat))
    (a : UInt256) (tail : List UInt256) (stack : s.stack = a :: tail) :
    EVM.step (fuel+1) cost (some (.DUP1,arg)) s =
      .ok (binaryPost s a (a :: tail) cost) := by
  simp [EVM.step, stack, binaryPost, EVM.State.replaceStackAndIncrPC,
    EVM.State.incrPC, EvmYul.dup]
  rfl

theorem step_push0 (s : EVM.State) (fuel cost : Nat) (arg : Option (UInt256 × Nat)) :
    EVM.step (fuel+1) cost (some (.PUSH0,arg)) s =
      .ok (binaryPost s (UInt256.ofNat 0) s.stack cost) := by
  rfl

theorem X_next_extended (s next : EVM.State) (fuel : Nat) (jumps : Array UInt256)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (allowed : ExtendedStackOp op)
    (decoded : decode s.executionEnv.code s.pc = some (op,arg))
    (bounds : FullXBounds s op)
    (canonical : EVM.step (fuel+1) (C' s op) (some (op,arg)) s = .ok next) :
    X (fuel+2) jumps s = X (fuel+1) jumps next := by
  have gas := bounds.gas
  have inputs := bounds.inputs
  have outputs := bounds.outputs
  cases allowed with
  | add =>
    conv_lhs => unfold X
    simp only [decoded]
    simp [mem_add, cost_add, Operation.isCreate, δ, α,
      show ¬s.gasAvailable.toNat < 3 by exact Nat.not_lt.mpr gas,
      show ¬s.stack.length < 2 by exact Nat.not_lt.mpr inputs,
      show ¬1024 < s.stack.length - 2 + 1 by exact Nat.not_lt.mpr outputs]
    change (do
      let n ← EVM.step (fuel+1) 3 (some (.ADD,arg)) s
      X (fuel+1) jumps n) = _
    rw [cost_add] at canonical
    rw [canonical]
    rfl
  | swap1 =>
    conv_lhs => unfold X
    simp only [decoded]
    simp [mem_swap1, cost_swap1, Operation.isCreate, δ, α,
      show ¬s.gasAvailable.toNat < 3 by exact Nat.not_lt.mpr gas,
      show ¬s.stack.length < 2 by exact Nat.not_lt.mpr inputs,
      show ¬1024 < s.stack.length - 2 + 2 by exact Nat.not_lt.mpr outputs]
    change (do
      let n ← EVM.step (fuel+1) 3 (some (.SWAP1,arg)) s
      X (fuel+1) jumps n) = _
    rw [cost_swap1] at canonical
    rw [canonical]
    rfl
  | push0 =>
    conv_lhs => unfold X
    simp only [decoded]
    simp [mem_push0, cost_push0, Operation.isCreate, δ, α,
      show ¬s.gasAvailable.toNat < 2 by exact Nat.not_lt.mpr gas,
      show ¬s.stack.length < 0 by exact Nat.not_lt.mpr inputs,
      show ¬1024 < s.stack.length + 1 by simpa [δ, α] using Nat.not_lt.mpr outputs]
    change (do
      let n ← EVM.step (fuel+1) 2 (some (.PUSH0,arg)) s
      X (fuel+1) jumps n) = _
    rw [cost_push0] at canonical
    rw [canonical]
    rfl
  | dup1 =>
    conv_lhs => unfold X
    simp only [decoded]
    simp [mem_dup1, cost_dup1, Operation.isCreate, δ, α,
      show ¬s.gasAvailable.toNat < 3 by exact Nat.not_lt.mpr gas,
      show ¬s.stack.length < 1 by exact Nat.not_lt.mpr inputs,
      show ¬1024 < s.stack.length - 1 + 2 by exact Nat.not_lt.mpr outputs]
    change (do
      let n ← EVM.step (fuel+1) 3 (some (.DUP1,arg)) s
      X (fuel+1) jumps n) = _
    rw [cost_dup1] at canonical
    rw [canonical]
    rfl


#print axioms X_next
#print axioms X_next_extended
#print axioms step_add
#print axioms step_swap1
#print axioms step_dup1
#print axioms step_push0
end GolfUpstream
