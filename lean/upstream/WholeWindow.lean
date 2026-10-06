import WholeThread
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition

/-! Straight-line stack windows (PUSH, DUP, SWAP, POP) with a symbolic stack. -/
namespace GolfWhole

/-- Binary and unary window operations, as the interpreter applies them to (top, second). -/
inductive BinK where
  | add | mul | sub | div | sdiv | mod | smod | signextend
  | lt | gt | slt | sgt | eq | and | or | xor | byte | shl | shr | sar
  deriving DecidableEq

inductive UnK where
  | iszero | not
  deriving DecidableEq

def binF : BinK → UInt256 → UInt256 → UInt256
  | .add => UInt256.add
  | .mul => UInt256.mul
  | .sub => UInt256.sub
  | .div => UInt256.div
  | .sdiv => UInt256.sdiv
  | .mod => UInt256.mod
  | .smod => UInt256.smod
  | .signextend => UInt256.signextend
  | .lt => UInt256.lt
  | .gt => UInt256.gt
  | .slt => UInt256.slt
  | .sgt => UInt256.sgt
  | .eq => UInt256.eq
  | .and => UInt256.land
  | .or => UInt256.lor
  | .xor => UInt256.xor
  | .byte => UInt256.byteAt
  | .shl => flip UInt256.shiftLeft
  | .shr => flip UInt256.shiftRight
  | .sar => UInt256.sar

def unF : UnK → UInt256 → UInt256
  | .iszero => UInt256.isZero
  | .not => UInt256.lnot

inductive Sym where
  | input (i : Nat)
  | lit (v : UInt256)
  | un (f : UnK) (a : Sym)
  | bin (f : BinK) (a b : Sym)
  deriving DecidableEq

instance : Inhabited Sym := ⟨.lit ⟨0⟩⟩

def Sym.val (base : List UInt256) : Sym → UInt256
  | .input i => base.getD i ⟨0⟩
  | .lit v => v
  | .un f a => unF f (a.val base)
  | .bin f a b => binF f (a.val base) (b.val base)

/-- A strict total order on terms: literals, inputs, unary, binary. Soundness never
depends on it; it only makes the normal form canonical. -/
def Sym.lt : Sym → Sym → Bool
  | .lit x, .lit y => x.val.val < y.val.val
  | .lit _, _ => true
  | .input _, .lit _ => false
  | .input i, .input j => i < j
  | .input _, _ => true
  | .un _ _, .lit _ => false
  | .un _ _, .input _ => false
  | .un f a, .un g b => if f = g then a.lt b else f.toCtorIdx < g.toCtorIdx
  | .un _ _, .bin _ _ _ => true
  | .bin _ _ _, .lit _ => false
  | .bin _ _ _, .input _ => false
  | .bin _ _ _, .un _ _ => false
  | .bin f a b, .bin g c d =>
    if f = g then (if a = c then b.lt d else a.lt c) else f.toCtorIdx < g.toCtorIdx

def swapList {α : Type} [Inhabited α] (k : Nat) (a : List α) : List α :=
  let top := a.take (k + 1)
  top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ a.drop (k + 1)

theorem take_append_le {α : Type} (n : Nat) (a b : List α) (h : n ≤ a.length) :
    (a ++ b).take n = a.take n := by
  simp [List.take_append_of_le_length h]

theorem drop_append_le {α : Type} (n : Nat) (a b : List α) (h : n ≤ a.length) :
    (a ++ b).drop n = a.drop n ++ b := by
  simp [List.drop_append_of_le_length h]

theorem getLast!_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (l : List α) (h : l ≠ []) :
    (l.map f).getLast! = f l.getLast! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast!_eq_getLast?_getD, List.getLast?_map]
  cases e : l.getLast? with
  | none => simp [List.getLast?_eq_none_iff] at e; exact absurd e h
  | some x => simp

theorem head!_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (l : List α) (h : l ≠ []) :
    (l.map f).head! = f l.head! := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => rfl

theorem tail!_map {α β : Type} (f : α → β) (l : List α) : (l.map f).tail! = l.tail!.map f := by
  cases l <;> rfl

/-- SWAP on a stack whose top `k+1` words are symbolic. -/
theorem swap_concrete (base : List UInt256) (a : List Sym) (rest : List UInt256) (k : Nat)
    (h : k + 1 ≤ a.length) :
    swapList k (a.map (Sym.val base) ++ rest) = (swapList k a).map (Sym.val base) ++ rest := by
  have ne : a.take (k + 1) ≠ [] := by
    intro e; rw [List.take_eq_nil_iff] at e; rcases e with e | e
    · omega
    · simp [e] at h
  unfold swapList
  rw [take_append_le _ _ _ (by simp; omega), drop_append_le _ _ _ (by simp; omega),
    ← List.map_take, ← List.map_drop]
  simp only []
  rw [getLast!_map _ _ ne, head!_map _ _ ne, tail!_map, ← List.map_dropLast]
  simp

theorem dup_concrete (base : List UInt256) (a : List Sym) (rest : List UInt256) (k : Nat)
    (h1 : 1 ≤ k) (h : k ≤ a.length) :
    ((a.map (Sym.val base) ++ rest).take k).getLast! = Sym.val base ((a.take k).getLast!) := by
  have ne : a.take k ≠ [] := by
    intro e; rw [List.take_eq_nil_iff] at e; rcases e with e | e
    · omega
    · simp [e] at h; omega
  rw [take_append_le _ _ _ (by simp; omega), ← List.map_take, getLast!_map _ _ ne]


/-- Window instructions. `dup k` is `DUPk`, `swap k` is `SWAPk`. -/
inductive WOp where
  | push (p : Operation.POp) (v : UInt256) (w : Nat)
  | push0
  | dup (k : Nat)
  | swap (k : Nat)
  | pop
  | un (f : UnK)
  | bin (f : BinK)
  deriving DecidableEq

def WOp.need : WOp → Nat
  | .push _ _ _ => 0
  | .push0 => 0
  | .dup k => k
  | .swap k => k + 1
  | .pop => 1
  | .un _ => 1
  | .bin _ => 2

def WOp.cost : WOp → Nat
  | .pop => 2
  | .push0 => 2
  | .bin .mul | .bin .div | .bin .sdiv | .bin .mod | .bin .smod | .bin .signextend => 5
  | _ => 3

def WOp.len : WOp → Nat
  | .push _ _ w => w + 1
  | _ => 1

def WOp.apply {α : Type} [Inhabited α] (lit : UInt256 → α) (bin : BinK → α → α → α)
    (un : UnK → α → α) : WOp → List α → List α
  | .push _ v _, l => lit v :: l
  | .push0, l => lit ⟨0⟩ :: l
  | .dup k, l => (l.take k).getLast! :: l
  | .swap k, l => swapList k l
  | .pop, l => l.tail
  | .un f, a :: l => un f a :: l
  | .un _, l => l
  | .bin f, a :: b :: l => bin f a b :: l
  | .bin _, l => l

theorem apply_append (op : WOp) (base : List UInt256) (a : List Sym) (rest : List UInt256)
    (h : op.need ≤ a.length) (k1 : ∀ k, op = .dup k → 1 ≤ k) :
    op.apply id binF unF (a.map (Sym.val base) ++ rest) =
      (op.apply Sym.lit Sym.bin Sym.un a).map (Sym.val base) ++ rest := by
  cases op with
  | push p v w => rfl
  | push0 => rfl
  | dup k =>
    simp only [WOp.apply, WOp.need] at h ⊢
    rw [dup_concrete base a rest k (k1 k rfl) h]
    rfl
  | swap k =>
    simp only [WOp.apply, WOp.need] at h ⊢
    exact swap_concrete base a rest k h
  | pop =>
    simp only [WOp.apply, WOp.need] at h ⊢
    cases a with
    | nil => simp at h
    | cons x xs => rfl
  | un f =>
    simp only [WOp.need] at h
    match a, h with
    | x :: a', _ => rfl
  | bin f =>
    simp only [WOp.need] at h
    match a, h with
    | x :: y :: a', _ => rfl

/-- Symbolic inputs `m, m+1, ...` pulled from below the explicit stack. -/
def pulls (m n : Nat) : List Sym := (List.range n).map fun i => .input (m + i)

def sstep (op : WOp) (st : List Sym × Nat) : List Sym × Nat :=
  let extra := op.need - st.1.length
  (op.apply Sym.lit Sym.bin Sym.un (st.1 ++ pulls st.2 extra), st.2 + extra)

theorem pulls_val (base : List UInt256) (m n : Nat) (h : m + n ≤ base.length) :
    (pulls m n).map (Sym.val base) ++ base.drop (m + n) = base.drop m := by
  induction n with
  | zero => simp [pulls]
  | succ n ih =>
    have hm : m + n < base.length := by omega
    rw [← ih (by omega)]
    simp only [pulls, List.range_succ, List.map_append, List.map_map, List.append_assoc]
    congr 1
    simp only [List.map_cons, List.map_nil, Function.comp, Sym.val, List.singleton_append]
    rw [show base.getD (m + n) ⟨0⟩ = base[m + n] by simp [List.getD_eq_getElem?_getD, hm], ← Nat.add_assoc]
    exact (List.drop_eq_getElem_cons hm).symm

/-- One symbolic step tracks one concrete step whenever the inputs exist. -/
theorem sstep_sound (op : WOp) (base : List UInt256) (a : List Sym) (m : Nat)
    (k1 : ∀ k, op = .dup k → 1 ≤ k)
    (fits : m + (op.need - a.length) ≤ base.length) :
    op.need ≤ (a.map (Sym.val base) ++ base.drop m).length ∧
    op.apply id binF unF (a.map (Sym.val base) ++ base.drop m) =
      (sstep op (a, m)).1.map (Sym.val base) ++ base.drop (sstep op (a, m)).2 := by
  have e : a.map (Sym.val base) ++ base.drop m =
      (a ++ pulls m (op.need - a.length)).map (Sym.val base) ++ base.drop (m + (op.need - a.length)) := by
    rw [List.map_append, List.append_assoc, pulls_val base m _ fits]
  refine ⟨?_, ?_⟩
  · simp only [List.length_append, List.length_map, List.length_drop]; omega
  · rw [e, apply_append op base _ _ (by simp [pulls]; omega) k1]
    rfl

theorem sstep_need (op : WOp) (base : List UInt256) (a : List Sym) (m : Nat)
    (hm : m ≤ base.length)
    (enough : op.need ≤ (a.map (Sym.val base) ++ base.drop m).length) :
    m + (op.need - a.length) ≤ base.length := by
  simp only [List.length_append, List.length_map, List.length_drop] at enough
  omega

theorem sstep_mono (op : WOp) (st : List Sym × Nat) : st.2 ≤ (sstep op st).2 := by
  simp [sstep]


theorem swapList_length {α : Type} [Inhabited α] (k : Nat) (l : List α) (h1 : 1 ≤ k)
    (h : k + 1 ≤ l.length) : (swapList k l).length = l.length := by
  unfold swapList
  have ht : (l.take (k + 1)).length = k + 1 := by simp; omega
  generalize hl : l.take (k + 1) = top at ht
  cases top with
  | nil => simp at ht
  | cons x rest =>
    simp only [List.tail!_cons, List.length_cons, List.length_append, List.length_dropLast,
      List.length_nil, List.length_drop] at ht ⊢
    omega

def dupOp : Nat → Operation .EVM
  | 1 => .DUP1 | 2 => .DUP2 | 3 => .DUP3 | 4 => .DUP4 | 5 => .DUP5 | 6 => .DUP6
  | 7 => .DUP7 | 8 => .DUP8 | 9 => .DUP9 | 10 => .DUP10 | 11 => .DUP11 | 12 => .DUP12
  | 13 => .DUP13 | 14 => .DUP14 | 15 => .DUP15 | 16 => .DUP16 | _ => .INVALID

def swapOp : Nat → Operation .EVM
  | 1 => .SWAP1 | 2 => .SWAP2 | 3 => .SWAP3 | 4 => .SWAP4 | 5 => .SWAP5 | 6 => .SWAP6
  | 7 => .SWAP7 | 8 => .SWAP8 | 9 => .SWAP9 | 10 => .SWAP10 | 11 => .SWAP11 | 12 => .SWAP12
  | 13 => .SWAP13 | 14 => .SWAP14 | 15 => .SWAP15 | 16 => .SWAP16 | _ => .INVALID

def WOp.op : WOp → Operation .EVM
  | .push p _ _ => .Push p
  | .push0 => .Push .PUSH0
  | .dup k => dupOp k
  | .swap k => swapOp k
  | .pop => .POP
  | .un .iszero => .ISZERO
  | .un .not => .NOT
  | .bin .add => .ADD
  | .bin .mul => .MUL
  | .bin .sub => .SUB
  | .bin .div => .DIV
  | .bin .sdiv => .SDIV
  | .bin .mod => .MOD
  | .bin .smod => .SMOD
  | .bin .signextend => .SIGNEXTEND
  | .bin .lt => .LT
  | .bin .gt => .GT
  | .bin .slt => .SLT
  | .bin .sgt => .SGT
  | .bin .eq => .EQ
  | .bin .and => .AND
  | .bin .or => .OR
  | .bin .xor => .XOR
  | .bin .byte => .BYTE
  | .bin .shl => .SHL
  | .bin .shr => .SHR
  | .bin .sar => .SAR

def WOp.arg : WOp → Option (UInt256 × Nat)
  | .push _ v w => some (v, w)
  | _ => none

def WOp.valid : WOp → Bool
  | .push p _ _ => p != .PUSH0
  | .push0 => true
  | .dup k => 1 ≤ k && k ≤ 16
  | .swap k => 1 ≤ k && k ≤ 16
  | .pop => true
  | .un _ => true
  | .bin _ => true

/-- Static facts about a valid window instruction. -/
structure WFacts (op : WOp) : Prop where
  cost : ∀ s, C' s op.op = op.cost
  mem : ∀ s, memoryExpansionCost s op.op = 0
  run : Running op.op
  inputs : (δ op.op).getD 0 = op.need
  defined : δ op.op ≠ none
  outputs : ∀ l : List UInt256, op.need ≤ l.length →
    l.length - (δ op.op).getD 0 + (α op.op).getD 0 = (op.apply id binF unF l).length
  notJump : op.op ≠ .JUMP ∧ op.op ≠ .JUMPI ∧ op.op ≠ .RETURNDATACOPY ∧ op.op ≠ .SSTORE
  static : ∀ st, W op.op st = false
  create : op.op.isCreate = false
  step : ∀ (f : ℕ) (u : State), op.need ≤ u.stack.length →
    EVM.step (f + 1) op.cost (some (op.op, op.arg)) u =
      .ok ((bump u op.cost).replaceStackAndIncrPC (op.apply id binF unF u.stack) op.len)
  dup1 : ∀ k, op = .dup k → 1 ≤ k

theorem dup_ok (k : ℕ) (v : State) (h : k ≤ v.stack.length) :
    EvmYul.dup k v = .ok (v.replaceStackAndIncrPC ((v.stack.take k).getLast! :: v.stack)) := by
  unfold EvmYul.dup; simp [List.length_take, h]

theorem swap_ok (k : ℕ) (v : State) (h : k + 1 ≤ v.stack.length) :
    EvmYul.swap k v = .ok (v.replaceStackAndIncrPC (swapList k v.stack)) := by
  unfold EvmYul.swap; simp [List.length_take, h, swapList]

theorem wfacts (op : WOp) (v : op.valid = true) : WFacts op := by
  cases op with
  | push p x w =>
    have nz : p ≠ .PUSH0 := by simpa [WOp.valid] using v
    refine ⟨fun s => cost_push s p nz, fun s => mem_push s p, fun _ => by simp [H, WOp.op], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cases p <;> first | exact absurd rfl nz | rfl
    · cases p <;> first | exact absurd rfl nz | simp [WOp.op, δ]
    · intro l _; cases p <;> first | exact absurd rfl nz | simp [WOp.op, WOp.apply, WOp.need, δ, α]
    · simp [WOp.op]
    · intro st; cases p <;> first | exact absurd rfl nz | simp [WOp.op, W]
    · cases p <;> first | exact absurd rfl nz | rfl
    · intro f u _
      have e : EVM.step (f + 1) 3 (some (.Push p, some (x, w))) u = EvmYul.step (.Push p) (some (x, w)) (bump u 3) := by
        cases p <;> first | exact absurd rfl nz | rfl
      simp only [WOp.op, WOp.arg, WOp.cost, WOp.apply, WOp.len]
      rw [e]
      cases p <;> first | exact absurd rfl nz | rfl
    · intro k h; cases h
  | push0 =>
    refine ⟨fun _ => rfl, fun s => by simp [WOp.op, memoryExpansionCost, memoryExpansionCost.μᵢ'],
      fun _ => by simp [H, WOp.op], rfl, by simp [WOp.op, δ], ?_, by simp [WOp.op],
      fun st => by simp [WOp.op, W], rfl, fun f u _ => rfl, fun k e => by cases e⟩
    intro l _; simp [WOp.op, WOp.apply, δ, α]
  | dup k =>
    have hk : 1 ≤ k ∧ k ≤ 16 := by simpa [WOp.valid] using v
    obtain ⟨h1, h2⟩ := hk
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k' e => by cases e; exact h1⟩ <;>
      (have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨
          k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by omega
       rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> first
        | (intro s; rfl; done)
        | (intro s; simp [WOp.op, dupOp, memoryExpansionCost, memoryExpansionCost.μᵢ']; done)
        | (intro μ; simp [H, WOp.op, dupOp]; done)
        | rfl
        | (simp [WOp.op, dupOp, δ]; done)
        | (intro l hl; simp [WOp.op, dupOp, WOp.apply, WOp.need, δ, α] at hl ⊢; omega)
        | (simp [WOp.op, dupOp]; done)
        | (intro st; simp [WOp.op, dupOp, W]; done)
        | (intro f u h; exact dup_ok _ (bump u 3) h)
  | swap k =>
    have hk : 1 ≤ k ∧ k ≤ 16 := by simpa [WOp.valid] using v
    obtain ⟨h1, h2⟩ := hk
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k' e => by cases e⟩ <;>
      (have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨
          k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by omega
       rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> first
        | (intro s; rfl; done)
        | (intro s; simp [WOp.op, swapOp, memoryExpansionCost, memoryExpansionCost.μᵢ']; done)
        | (intro μ; simp [H, WOp.op, swapOp]; done)
        | rfl
        | (simp [WOp.op, swapOp, δ]; done)
        | (intro l hl; simp only [WOp.op, swapOp, WOp.apply, WOp.need, δ, α, Option.getD] at hl ⊢;
           rw [swapList_length _ _ (by omega) hl]; omega)
        | (simp [WOp.op, swapOp]; done)
        | (intro st; simp [WOp.op, swapOp, W]; done)
        | (intro f u h; exact swap_ok _ (bump u 3) h)
  | un f =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k e => by cases e⟩ <;> cases f <;> first
      | (intro s; rfl; done)
      | (intro s; simp [WOp.op, memoryExpansionCost, memoryExpansionCost.μᵢ']; done)
      | (intro μ; simp [H, WOp.op]; done)
      | rfl
      | (simp [WOp.op, δ]; done)
      | (intro l hl; simp only [WOp.need] at hl
         match l, hl with
         | x :: l', _ => simp [WOp.op, WOp.apply, δ, α])
      | (simp [WOp.op]; done)
      | (intro st; simp [WOp.op, W]; done)
      | (intro f u h
         simp only [WOp.need] at h
         obtain ⟨x, l', hs⟩ : ∃ x l', u.stack = x :: l' := by
           match e : u.stack, h with
           | x :: l', _ => exact ⟨x, l', rfl⟩
         change EVM.execUnOp _ (bump u _) = _
         unfold EVM.execUnOp
         have : ∀ c, (bump u c).stack = x :: l' := fun _ => hs
         simp only [this, Stack.pop, WOp.apply, hs]
         rfl)
  | bin f =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k e => by cases e⟩ <;> cases f <;> first
      | (intro s; rfl; done)
      | (intro s; simp [WOp.op, memoryExpansionCost, memoryExpansionCost.μᵢ']; done)
      | (intro μ; simp [H, WOp.op]; done)
      | rfl
      | (simp [WOp.op, δ]; done)
      | (intro l hl; simp only [WOp.need] at hl
         match l, hl with
         | x :: y :: l', _ => simp [WOp.op, WOp.apply, δ, α])
      | (simp [WOp.op]; done)
      | (intro st; simp [WOp.op, W]; done)
      | (intro f u h
         simp only [WOp.need] at h
         obtain ⟨x, y, l', hs⟩ : ∃ x y l', u.stack = x :: y :: l' := by
           match e : u.stack, h with
           | x :: y :: l', _ => exact ⟨x, y, l', rfl⟩
         change EVM.execBinOp _ (bump u _) = _
         unfold EVM.execBinOp
         have : ∀ c, (bump u c).stack = x :: y :: l' := fun _ => hs
         simp only [this, Stack.pop2, WOp.apply, hs]
         rfl)
  | pop =>
    refine ⟨fun _ => rfl, fun s => by simp [WOp.op, memoryExpansionCost, memoryExpansionCost.μᵢ'],
      fun _ => by simp [H, WOp.op], rfl, by simp [WOp.op, δ], ?_, by simp [WOp.op], fun st => by simp [WOp.op, W],
      rfl, ?_, fun k e => by cases e⟩
    · intro l hl; simp [WOp.op, WOp.apply, WOp.need, δ, α] at hl ⊢
    · intro f u h
      simp only [WOp.need] at h
      obtain ⟨x, xs, hs⟩ : ∃ x xs, u.stack = x :: xs := by
        match e : u.stack, h with
        | x :: xs, _ => exact ⟨x, xs, rfl⟩
      change (match (bump u 2).stack.pop with
        | some ⟨s, _⟩ => Except.ok ((bump u 2).replaceStackAndIncrPC s)
        | _ => Except.error .StackUnderflow : Except EVM.ExecutionException State) = _
      have : (bump u 2).stack = x :: xs := hs
      simp [this, Stack.pop, WOp.apply, hs]
      rfl


/-- A window decoded at consecutive offsets of `code`, from `pc` to `e`. -/
inductive WCode (code : ByteArray) : UInt256 → List WOp → UInt256 → Prop where
  | nil (pc : UInt256) : WCode code pc [] pc
  | cons (pc pc' e : UInt256) (op : WOp) (ops : List WOp) (v : op.valid = true)
      (d : decode code pc = some (op.op, op.arg)) (adv : pc + UInt256.ofNat op.len = pc')
      (rest : WCode code pc' ops e) : WCode code pc (op :: ops) e

def srun : List WOp → List Sym × Nat → List Sym × Nat
  | [], st => st
  | op :: ops, st => srun ops (sstep op st)

def scost : List WOp → Nat
  | [] => 0
  | op :: ops => op.cost + scost ops

/-- Stack height after each instruction, relative to the window input depth. -/
def sheights : List WOp → List Sym × Nat → List Int
  | [], _ => []
  | op :: ops, st => ((sstep op st).1.length - (sstep op st).2 : Int) :: sheights ops (sstep op st)

theorem srun_mono : ∀ (ops : List WOp) (st : List Sym × Nat), st.2 ≤ (srun ops st).2
  | [], _ => le_refl _
  | op :: ops, st => le_trans (sstep_mono op st) (srun_mono ops (sstep op st))

theorem window_source {code : ByteArray} {j : Array UInt256} {pc e : UInt256} {ops : List WOp}
    (wc : WCode code pc ops e) (base : List UInt256) :
    ∀ (u : State) (a : List Sym) (m fuel : ℕ) (r : ExecutionResult State),
      u.executionEnv.code = code → u.pc = pc → m ≤ base.length →
      u.stack = a.map (Sym.val base) ++ base.drop m → X fuel j u = .ok r →
      (srun ops (a, m)).2 ≤ base.length ∧
      (∀ h ∈ sheights ops (a, m), (base.length : Int) + h ≤ 1024) ∧
      scost ops ≤ u.gasAvailable.toNat ∧
      ∃ g : UInt256, g.toNat + scost ops = u.gasAvailable.toNat ∧ ∃ f, fuel = f + ops.length ∧
        X f j { u with
          stack := (srun ops (a, m)).1.map (Sym.val base) ++ base.drop (srun ops (a, m)).2
          pc := e
          gasAvailable := g
          execLength := u.execLength + ops.length } = .ok r := by
  induction wc with
  | nil pc =>
    intro u a m f r _ hpc hm hst ok
    refine ⟨hm, by simp [sheights], by simp [scost], u.gasAvailable, by simp [scost], f, rfl, ?_⟩
    simp only [srun, List.length_nil, Nat.add_zero]
    rw [← hst, ← hpc]
    exact ok
  | cons pc pc' e op ops v d adv rest ih =>
    intro u a m fuel r hc hpc hm hst ok
    have F := wfacts op v
    cases fuel with
    | zero => rw [X_zero] at ok; cases ok
    | succ f =>
    obtain ⟨z, g, n, hg, step, run⟩ :=
      source_step (by rw [hc, hpc]; exact d) F.run (F.mem u) ok
    have need : op.need ≤ u.stack.length := by have := z.inputs; rwa [F.inputs] at this
    have fits := sstep_need op base a m hm (by rw [← hst]; exact need)
    obtain ⟨-, sound⟩ := sstep_sound op base a m F.dup1 fits
    rw [F.cost, F.step g u need] at step
    injection step with hn
    subst hn
    have gcost : op.cost ≤ u.gasAvailable.toNat := by
      have := z.cost; rwa [gasCut_zero (F.mem u), F.cost] at this
    have post := z.outputs
    rw [F.outputs _ need] at post
    rw [hst, sound] at post
    rw [← hg] at run
    obtain ⟨M, hts, cost, g', hg', f', hf', fin⟩ :=
      ih ((bump u op.cost).replaceStackAndIncrPC (op.apply id binF unF u.stack) op.len)
        (sstep op (a, m)).1 (sstep op (a, m)).2 f r hc
        (by rw [← adv, ← hpc]; rfl) fits
        (by show op.apply id binF unF u.stack = _; rw [hst]; exact sound) run
    have sub := word_sub_toNat u.gasAvailable op.cost (by unfold WOp.cost; split <;> decide) gcost
    refine ⟨M, ?_, ?_, g', ?_, ?_⟩
    · intro h hh
      simp only [sheights, List.mem_cons] at hh
      rcases hh with rfl | hh
      · simp only [List.length_append, List.length_map, List.length_drop] at post
        have := sstep_mono op (a, m)
        simp only at this
        omega
      · exact hts h hh
    · simp only [scost]
      change scost ops ≤ (u.gasAvailable - UInt256.ofNat op.cost).toNat at cost
      omega
    · simp only [scost]
      change g'.toNat + scost ops = (u.gasAvailable - UInt256.ofNat op.cost).toNat at hg'
      omega
    · refine ⟨f', by simp; omega, ?_⟩
      simp only [srun]
      rw [show u.execLength + (op :: ops).length = u.execLength + 1 + ops.length by simp; omega]
      exact fin


theorem window_cand {code : ByteArray} {j : Array UInt256} {pc e : UInt256} {ops : List WOp}
    (wc : WCode code pc ops e) (base : List UInt256) :
    ∀ (u : State) (a : List Sym) (m : ℕ),
      u.executionEnv.code = code → u.pc = pc →
      u.stack = a.map (Sym.val base) ++ base.drop m →
      (srun ops (a, m)).2 ≤ base.length →
      (∀ h ∈ sheights ops (a, m), (base.length : Int) + h ≤ 1024) →
      scost ops ≤ u.gasAvailable.toNat →
      ∃ g : UInt256, g.toNat + scost ops = u.gasAvailable.toNat ∧
        ∀ F, X (F + 1 + ops.length) j u = X (F + 1) j { u with
          stack := (srun ops (a, m)).1.map (Sym.val base) ++ base.drop (srun ops (a, m)).2
          pc := e
          gasAvailable := g
          execLength := u.execLength + ops.length } := by
  induction wc with
  | nil pc =>
    intro u a m _ hpc hst _ _ _
    refine ⟨u.gasAvailable, by simp [scost], fun F => ?_⟩
    simp only [srun, List.length_nil, Nat.add_zero]
    rw [← hst, ← hpc]
  | cons pc pc' e op ops v d adv rest ih =>
    intro u a m hc hpc hst hM hts gas
    have F := wfacts op v
    have mono := srun_mono ops (sstep op (a, m))
    have hM' : (srun ops (sstep op (a, m))).2 ≤ base.length := hM
    have fits : m + (op.need - a.length) ≤ base.length := by
      have : (sstep op (a, m)).2 = m + (op.need - a.length) := rfl
      omega
    obtain ⟨need', sound⟩ := sstep_sound op base a m F.dup1 fits
    have need : op.need ≤ u.stack.length := by rw [hst]; exact need'
    have gcost : op.cost ≤ u.gasAvailable.toNat := by simp only [scost] at gas; omega
    have h0 := hts _ List.mem_cons_self
    have z : ZOk j op.op u := by
      refine ⟨by rw [F.mem]; omega, by rw [gasCut_zero (F.mem u), F.cost]; exact gcost, F.defined,
        by rw [F.inputs]; exact need, fun h => F.notJump.1 h.1, fun h => F.notJump.2.1 h.1,
        fun h => F.notJump.2.2.1 h.1, ?_, by simp [F.static], fun h => F.notJump.2.2.2 h.1,
        by simp [F.create]⟩
      rw [F.outputs _ need, hst, sound]
      simp only [List.length_append, List.length_map, List.length_drop]
      have := sstep_mono op (a, m)
      simp only at this
      omega
    have sub := word_sub_toNat u.gasAvailable op.cost (by unfold WOp.cost; split <;> decide) gcost
    obtain ⟨g', hg', fin⟩ :=
      ih ((bump u op.cost).replaceStackAndIncrPC (op.apply id binF unF u.stack) op.len)
        (sstep op (a, m)).1 (sstep op (a, m)).2 hc (by rw [← adv, ← hpc]; rfl)
        (by show op.apply id binF unF u.stack = _; rw [hst]; exact sound) hM'
        (fun h hh => hts h (List.mem_cons_of_mem _ hh))
        (by change scost ops ≤ (u.gasAvailable - UInt256.ofNat op.cost).toNat
            simp only [scost] at gas; omega)
    have run := candidate_run (j := j) (by rw [hc, hpc]; exact d) F.run (F.mem u) z
      (fun g => by rw [F.cost]; exact F.step g u need)
    refine ⟨g', ?_, fun Fu => ?_⟩
    · simp only [scost]
      change g'.toNat + scost ops = (u.gasAvailable - UInt256.ofNat op.cost).toNat at hg'
      omega
    · rw [show Fu + 1 + (op :: ops).length = (Fu + ops.length) + 2 by simp; omega, run,
        show Fu + ops.length + 1 = Fu + 1 + ops.length by omega, fin Fu]
      simp only [srun]
      rw [show u.execLength + (op :: ops).length = u.execLength + 1 + ops.length by simp; omega]
      rfl


theorem size_eq : UInt256.size = 2 ^ 256 := rfl

def ones : UInt256 := ⟨⟨UInt256.size - 1, by decide⟩⟩

theorem add_comm' (a b : UInt256) : UInt256.add a b = UInt256.add b a := by
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := b; simp only [UInt256.add, UInt256.mk.injEq]; apply Fin.ext
  simp [Fin.val_add, Nat.add_comm]
theorem add_assoc' (a b c : UInt256) : UInt256.add (UInt256.add a b) c = UInt256.add a (UInt256.add b c) := by
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := b; obtain ⟨z⟩ := c
  simp only [UInt256.add, UInt256.mk.injEq]; apply Fin.ext
  show ((x.val + y.val) % UInt256.size + z.val) % UInt256.size = (x.val + (y.val + z.val) % UInt256.size) % UInt256.size
  rw [Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]
theorem add_idl (a : UInt256) : UInt256.add ⟨0⟩ a = a := by
  obtain ⟨x⟩ := a; simp [UInt256.add]

theorem mul_comm' (a b : UInt256) : UInt256.mul a b = UInt256.mul b a := by
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := b; simp only [UInt256.mul, UInt256.mk.injEq]; apply Fin.ext
  simp [Fin.val_mul, Nat.mul_comm]
theorem mul_assoc' (a b c : UInt256) : UInt256.mul (UInt256.mul a b) c = UInt256.mul a (UInt256.mul b c) := by
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := b; obtain ⟨z⟩ := c
  simp only [UInt256.mul, UInt256.mk.injEq]; apply Fin.ext
  show ((x.val * y.val) % UInt256.size * z.val) % UInt256.size = (x.val * ((y.val * z.val) % UInt256.size)) % UInt256.size
  rw [Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.mul_assoc]
theorem mul_idl (a : UInt256) : UInt256.mul ⟨1⟩ a = a := by
  obtain ⟨x⟩ := a; simp only [UInt256.mul, UInt256.mk.injEq]; apply Fin.ext
  show ((1 : Fin UInt256.size).val * x.val) % UInt256.size = x.val
  rw [show (1 : Fin UInt256.size).val = 1 from rfl, Nat.one_mul, Nat.mod_eq_of_lt x.isLt]
theorem mul_zero_l (a : UInt256) : UInt256.mul ⟨0⟩ a = ⟨0⟩ := by
  obtain ⟨x⟩ := a; simp only [UInt256.mul, UInt256.mk.injEq]; apply Fin.ext
  show ((0 : Fin UInt256.size).val * x.val) % UInt256.size = (0 : Fin UInt256.size).val
  rw [show (0 : Fin UInt256.size).val = 0 from rfl, Nat.zero_mul, Nat.zero_mod]

theorem bnd_and (x y : Fin UInt256.size) : x.val &&& y.val < UInt256.size :=
  lt_of_le_of_lt Nat.and_le_left x.isLt
theorem bnd_or (x y : Fin UInt256.size) : x.val ||| y.val < UInt256.size :=
  Nat.or_lt_two_pow (show x.val < 2^256 from x.isLt) (show y.val < 2^256 from y.isLt)
theorem bnd_xor (x y : Fin UInt256.size) : x.val ^^^ y.val < UInt256.size :=
  Nat.xor_lt_two_pow (show x.val < 2^256 from x.isLt) (show y.val < 2^256 from y.isLt)

theorem land_v (x y : Fin UInt256.size) : (UInt256.land ⟨x⟩ ⟨y⟩).val.val = x.val &&& y.val :=
  Nat.mod_eq_of_lt (bnd_and x y)
theorem lor_v (x y : Fin UInt256.size) : (UInt256.lor ⟨x⟩ ⟨y⟩).val.val = x.val ||| y.val :=
  Nat.mod_eq_of_lt (bnd_or x y)
theorem xor_v (x y : Fin UInt256.size) : (UInt256.xor ⟨x⟩ ⟨y⟩).val.val = x.val ^^^ y.val :=
  Nat.mod_eq_of_lt (bnd_xor x y)

theorem ext' {a b : UInt256} (h : a.val.val = b.val.val) : a = b := by
  obtain ⟨⟨x, _⟩⟩ := a; obtain ⟨⟨y, _⟩⟩ := b; simp only at h; subst h; rfl

theorem land_eq (x y : Fin UInt256.size) : UInt256.land ⟨x⟩ ⟨y⟩ = ⟨⟨x.val &&& y.val, bnd_and x y⟩⟩ := ext' (land_v x y)
theorem lor_eq (x y : Fin UInt256.size) : UInt256.lor ⟨x⟩ ⟨y⟩ = ⟨⟨x.val ||| y.val, bnd_or x y⟩⟩ := ext' (lor_v x y)
theorem xor_eq (x y : Fin UInt256.size) : UInt256.xor ⟨x⟩ ⟨y⟩ = ⟨⟨x.val ^^^ y.val, bnd_xor x y⟩⟩ := ext' (xor_v x y)

theorem land_comm' (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := b; apply ext'; rw [land_v, land_v, Nat.and_comm]
theorem land_assoc' (a b c : UInt256) : UInt256.land (UInt256.land a b) c = UInt256.land a (UInt256.land b c) := by
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := b; obtain ⟨z⟩ := c
  apply ext'
  rw [land_eq, land_eq, land_eq, land_eq]; exact Nat.and_assoc _ _ _
theorem land_idl (a : UInt256) : UInt256.land ones a = a := by
  obtain ⟨x⟩ := a; apply ext'
  show (UInt256.land ⟨⟨2^256 - 1, by decide⟩⟩ ⟨x⟩).val.val = x.val
  rw [land_v, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (show x.val < 2^256 from x.isLt)]
theorem land_zero_l (a : UInt256) : UInt256.land ⟨0⟩ a = ⟨0⟩ := by
  obtain ⟨x⟩ := a; apply ext'
  show (UInt256.land ⟨⟨0, by decide⟩⟩ ⟨x⟩).val.val = 0
  rw [land_v]; simp
theorem land_idem (a : UInt256) : UInt256.land a a = a := by
  obtain ⟨x⟩ := a; apply ext'; rw [land_v, Nat.and_self]

theorem lor_comm' (a b : UInt256) : UInt256.lor a b = UInt256.lor b a := by
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := b; apply ext'; rw [lor_v, lor_v, Nat.or_comm]
theorem lor_assoc' (a b c : UInt256) : UInt256.lor (UInt256.lor a b) c = UInt256.lor a (UInt256.lor b c) := by
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := b; obtain ⟨z⟩ := c
  apply ext'
  rw [lor_eq, lor_eq, lor_eq, lor_eq]; exact Nat.or_assoc _ _ _
theorem lor_idl (a : UInt256) : UInt256.lor ⟨0⟩ a = a := by
  obtain ⟨x⟩ := a; apply ext'
  show (UInt256.lor ⟨⟨0, by decide⟩⟩ ⟨x⟩).val.val = x.val
  rw [lor_v]; simp
theorem lor_ones_l (a : UInt256) : UInt256.lor ones a = ones := by
  obtain ⟨x⟩ := a; apply ext'
  show (UInt256.lor ⟨⟨2^256 - 1, by decide⟩⟩ ⟨x⟩).val.val = 2^256 - 1
  rw [lor_v]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_or, Nat.testBit_two_pow_sub_one]
  by_cases h : i < 256
  · simp [h]
  · have : x.val.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le (show x.val < 2^256 from x.isLt) (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h, this]
theorem lor_idem (a : UInt256) : UInt256.lor a a = a := by
  obtain ⟨x⟩ := a; apply ext'; rw [lor_v, Nat.or_self]

theorem xor_comm' (a b : UInt256) : UInt256.xor a b = UInt256.xor b a := by
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := b; apply ext'; rw [xor_v, xor_v, Nat.xor_comm]
theorem xor_assoc' (a b c : UInt256) : UInt256.xor (UInt256.xor a b) c = UInt256.xor a (UInt256.xor b c) := by
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := b; obtain ⟨z⟩ := c
  apply ext'
  rw [xor_eq, xor_eq, xor_eq, xor_eq]; exact Nat.xor_assoc _ _ _
theorem xor_idl (a : UInt256) : UInt256.xor ⟨0⟩ a = a := by
  obtain ⟨x⟩ := a; apply ext'
  show (UInt256.xor ⟨⟨0, by decide⟩⟩ ⟨x⟩).val.val = x.val
  rw [xor_v]; simp


/-! Commutative, associative operators with an identity. -/

structure ACLaw (F : UInt256 → UInt256 → UInt256) (e : UInt256) : Prop where
  comm : ∀ a b, F a b = F b a
  assoc : ∀ a b c, F (F a b) c = F a (F b c)
  idl : ∀ a, F e a = a

theorem ACLaw.idr {F e} (h : ACLaw F e) (a : UInt256) : F a e = a := by rw [h.comm]; exact h.idl a
theorem ACLaw.lcomm {F e} (h : ACLaw F e) (a b c : UInt256) : F a (F b c) = F b (F a c) := by
  rw [← h.assoc, h.comm a b, h.assoc]

/-- Identity element of each commutative, associative operator. -/
def ident : BinK → Option UInt256
  | .add => some ⟨0⟩
  | .mul => some ⟨1⟩
  | .and => some ones
  | .or => some ⟨0⟩
  | .xor => some ⟨0⟩
  | _ => none

def absorb : BinK → Option UInt256
  | .mul => some ⟨0⟩
  | .and => some ⟨0⟩
  | .or => some ones
  | _ => none

def idem : BinK → Bool
  | .and => true
  | .or => true
  | _ => false

theorem ident_law {f : BinK} {e : UInt256} (h : ident f = some e) : ACLaw (binF f) e := by
  cases f <;> simp only [ident, reduceCtorEq, Option.some.injEq] at h <;> subst h
  · exact ⟨add_comm', add_assoc', add_idl⟩
  · exact ⟨mul_comm', mul_assoc', mul_idl⟩
  · exact ⟨land_comm', land_assoc', land_idl⟩
  · exact ⟨lor_comm', lor_assoc', lor_idl⟩
  · exact ⟨xor_comm', xor_assoc', xor_idl⟩

theorem absorb_law {f : BinK} {z : UInt256} (h : absorb f = some z) (a : UInt256) : binF f z a = z := by
  cases f <;> simp only [absorb, reduceCtorEq, Option.some.injEq] at h <;> subst h
  · exact mul_zero_l a
  · exact land_zero_l a
  · exact lor_ones_l a

theorem idem_law {f : BinK} (h : idem f = true) (a : UInt256) : binF f a a = a := by
  cases f <;> simp only [idem, Bool.false_eq_true] at h
  · exact land_idem a
  · exact lor_idem a

def fv (F : UInt256 → UInt256 → UInt256) (e : UInt256) (base : List UInt256) (l : List Sym) : UInt256 :=
  l.foldr (fun s acc => F (s.val base) acc) e

theorem fv_append {F e} (h : ACLaw F e) (base : List UInt256) (l1 l2 : List Sym) :
    fv F e base (l1 ++ l2) = F (fv F e base l1) (fv F e base l2) := by
  induction l1 with
  | nil => exact (h.idl _).symm
  | cons x l ih => simp only [fv, List.cons_append, List.foldr_cons] at ih ⊢; rw [ih, h.assoc]

def flat (f : BinK) : Sym → List Sym
  | .bin g a b => if g = f then flat f a ++ flat f b else [.bin g a b]
  | s => [s]

theorem flat_val {f e} (h : ACLaw (binF f) e) (base : List UInt256) :
    ∀ s : Sym, fv (binF f) e base (flat f s) = s.val base
  | .input _ => h.idr _
  | .lit _ => h.idr _
  | .un _ _ => h.idr _
  | .bin g a b => by
    unfold flat
    split
    · subst_vars; rw [fv_append h, flat_val h base a, flat_val h base b]; rfl
    · exact h.idr _

def litFold (f : BinK) (e : UInt256) : List Sym → UInt256 × List Sym
  | [] => (e, [])
  | s :: l =>
    match s with
    | .lit v => (binF f v (litFold f e l).1, (litFold f e l).2)
    | _ => ((litFold f e l).1, s :: (litFold f e l).2)

theorem litFold_val {f e} (h : ACLaw (binF f) e) (base : List UInt256) : ∀ l : List Sym,
    binF f (litFold f e l).1 (fv (binF f) e base (litFold f e l).2) = fv (binF f) e base l
  | [] => h.idr _
  | s :: l => by
    have ih := litFold_val h base l
    unfold litFold
    split
    · simp only [fv, List.foldr_cons, Sym.val] at ih ⊢; rw [h.assoc, ih]
    · simp only [fv, List.foldr_cons] at ih ⊢; rw [h.lcomm, ih]

def ins (x : Sym) : List Sym → List Sym
  | [] => [x]
  | y :: l => if y.lt x then y :: ins x l else x :: y :: l

def sortS (l : List Sym) : List Sym := l.foldr ins []

theorem ins_val {F e} (h : ACLaw F e) (base : List UInt256) (x : Sym) : ∀ l : List Sym,
    fv F e base (ins x l) = F (x.val base) (fv F e base l)
  | [] => rfl
  | y :: l => by
    unfold ins
    split
    · have ih := ins_val h base x l
      simp only [fv, List.foldr_cons] at ih ⊢; rw [ih, h.lcomm]
    · rfl

theorem sortS_val {F e} (h : ACLaw F e) (base : List UInt256) : ∀ l : List Sym,
    fv F e base (sortS l) = fv F e base l
  | [] => rfl
  | x :: l => by
    simp only [sortS, List.foldr_cons] at *
    rw [ins_val h base, show List.foldr ins [] l = sortS l from rfl, sortS_val h base l]; rfl

def dedup : List Sym → List Sym
  | x :: y :: l => if x = y then dedup (y :: l) else x :: dedup (y :: l)
  | l => l

theorem dedup_val {F e} (h : ACLaw F e) (hi : ∀ a, F a a = a) (base : List UInt256) :
    ∀ l : List Sym, fv F e base (dedup l) = fv F e base l
  | [] => rfl
  | [_] => rfl
  | x :: y :: l => by
    have ih := dedup_val h hi base (y :: l)
    unfold dedup
    split
    · subst_vars; rw [ih]; simp only [fv, List.foldr_cons]; rw [← h.assoc, hi]
    · simp only [fv, List.foldr_cons] at ih ⊢; rw [ih]

def build (f : BinK) (e : UInt256) : List Sym → Sym
  | [] => .lit e
  | [x] => x
  | x :: y :: l => .bin f x (build f e (y :: l))

theorem build_val {f e} (h : ACLaw (binF f) e) (base : List UInt256) : ∀ l : List Sym,
    (build f e l).val base = fv (binF f) e base l
  | [] => rfl
  | [x] => (h.idr _).symm
  | x :: y :: l => by
    have ih := build_val h base (y :: l)
    simp only [build, Sym.val] at ih ⊢; rw [ih]; rfl

/-- Canonical form of an operand list under a commutative, associative operator:
literals folded, operands sorted, duplicates dropped for idempotent operators. -/
def acNorm (f : BinK) (e : UInt256) (l : List Sym) : Sym :=
  if absorb f = some (litFold f e l).1 then .lit (litFold f e l).1
  else build f e (if (litFold f e l).1 = e
    then (if idem f then dedup (sortS (litFold f e l).2) else sortS (litFold f e l).2)
    else .lit (litFold f e l).1 ::
      (if idem f then dedup (sortS (litFold f e l).2) else sortS (litFold f e l).2))

theorem acNorm_val {f e} (h : ACLaw (binF f) e) (base : List UInt256) (l : List Sym) :
    (acNorm f e l).val base = fv (binF f) e base l := by
  have lf := litFold_val h base l
  have rest : fv (binF f) e base
      (if idem f then dedup (sortS (litFold f e l).2) else sortS (litFold f e l).2) =
      fv (binF f) e base (litFold f e l).2 := by
    split
    · rw [dedup_val h (idem_law ‹_›), sortS_val h]
    · rw [sortS_val h]
  unfold acNorm
  split
  · rename_i ha; rw [← lf, absorb_law ha]; rfl
  · rw [build_val h]
    split
    · rename_i hc; rw [rest, ← lf, hc, h.idl]
    · simp only [fv, List.foldr_cons, Sym.val] at rest lf ⊢; rw [rest, lf]

def pow2 (k : UInt256) : UInt256 := UInt256.ofNat (2 ^ k.val.val)

theorem sub_self' (a : UInt256) : UInt256.sub a a = ⟨0⟩ := by
  obtain ⟨x⟩ := a; simp [UInt256.sub]
theorem sub_add' (a c : UInt256) : UInt256.sub a c = UInt256.add a (UInt256.sub ⟨0⟩ c) := by
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := c; simp only [UInt256.sub, UInt256.add, UInt256.mk.injEq]
  rw [zero_sub]; exact sub_eq_add_neg x y
theorem shl_mul (b k : UInt256) (hk : k.val.val < 256) :
    flip UInt256.shiftLeft k b = UInt256.mul b (pow2 k) := by
  obtain ⟨x⟩ := b; obtain ⟨⟨n, hn⟩⟩ := k
  simp only at hk
  simp only [flip, UInt256.shiftLeft, UInt256.mul, pow2, UInt256.ofNat, Id.run]
  rw [if_neg (by simp only [ge_iff_le, Fin.le_def, show ((256 : Fin UInt256.size) : Nat) = 256 from rfl]; omega)]
  congr 1; apply Fin.ext
  show (x.val <<< n) % UInt256.size = (x.val * (2 ^ n % UInt256.size)) % UInt256.size
  rw [Nat.mul_mod_mod, Nat.shiftLeft_eq]
theorem shl_big (b k : UInt256) (hk : ¬ k.val.val < 256) : flip UInt256.shiftLeft k b = ⟨0⟩ := by
  obtain ⟨⟨n, hn⟩⟩ := k
  simp only at hk
  simp only [flip, UInt256.shiftLeft]
  rw [if_pos (by simp only [ge_iff_le, Fin.le_def, show ((256 : Fin UInt256.size) : Nat) = 256 from rfl]; omega)]
theorem shr_div (b k : UInt256) (hk : k.val.val < 256) :
    flip UInt256.shiftRight k b = UInt256.div b (pow2 k) := by
  obtain ⟨x⟩ := b; obtain ⟨⟨n, hn⟩⟩ := k
  simp only at hk
  simp only [flip, UInt256.shiftRight, UInt256.div, pow2, UInt256.ofNat, Id.run]
  rw [if_neg (by simp only [ge_iff_le, Fin.le_def, show ((256 : Fin UInt256.size) : Nat) = 256 from rfl]; omega)]
  congr 1; apply Fin.ext
  have hp : 2 ^ n < UInt256.size := by rw [size_eq]; exact Nat.pow_lt_pow_right (by decide) hk
  show (x.val >>> n) % UInt256.size = x.val / (2 ^ n % UInt256.size)
  rw [Nat.mod_eq_of_lt hp, Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)
theorem shr_big (b k : UInt256) (hk : ¬ k.val.val < 256) : flip UInt256.shiftRight k b = ⟨0⟩ := by
  obtain ⟨⟨n, hn⟩⟩ := k
  simp only at hk
  simp only [flip, UInt256.shiftRight]
  rw [if_pos (by simp only [ge_iff_le, Fin.le_def, show ((256 : Fin UInt256.size) : Nat) = 256 from rfl]; omega)]
theorem gt_lt (a b : UInt256) : UInt256.gt a b = UInt256.lt b a := rfl
theorem sgt_slt (a b : UInt256) : UInt256.sgt a b = UInt256.slt b a := by
  simp only [UInt256.sgt, UInt256.slt, UInt256.sgtBool, UInt256.sltBool]
  split_ifs <;> rfl
theorem eq_comm' (a b : UInt256) : UInt256.eq a b = UInt256.eq b a := by
  simp only [UInt256.eq]; congr 1; exact decide_eq_decide.mpr eq_comm
theorem eq_zero (a : UInt256) : UInt256.eq a ⟨0⟩ = UInt256.isZero a := by
  simp only [UInt256.eq, UInt256.isZero, UInt256.eq0]
  congr 1
  obtain ⟨x⟩ := a
  by_cases h : x = 0
  · subst h; rfl
  · have h1 : decide ((⟨x⟩ : UInt256) = ⟨0⟩) = false := decide_eq_false (fun e => h (by cases e; rfl))
    rw [h1]
    show false = (x == 0)
    exact (beq_eq_false_iff_ne.mpr h).symm

/-- Literal folding for operators whose kernel evaluation is cheap. -/
def foldable : BinK → Bool
  | .sub | .div | .mod | .lt | .gt | .eq | .shl | .shr => true
  | _ => false

/-- Rewrites for non-associative operators, applied to normalized operands. -/
def normOp (f : BinK) (a b : Sym) : Sym :=
  match f with
  | .sub => if a = b then .lit ⟨0⟩ else
      match b with
      | .lit c => acNorm .add ⟨0⟩ (flat .add a ++ [.lit (UInt256.sub ⟨0⟩ c)])
      | _ => .bin .sub a b
  | .shl =>
      match a with
      | .lit k => if k.val.val < 256 then acNorm .mul ⟨1⟩ (flat .mul b ++ [.lit (pow2 k)]) else .lit ⟨0⟩
      | _ => .bin .shl a b
  | .shr =>
      match a with
      | .lit k => if k.val.val < 256 then (if k.val.val = 0 then b else .bin .div b (.lit (pow2 k)))
          else .lit ⟨0⟩
      | _ => .bin .shr a b
  | .gt => .bin .lt b a
  | .sgt => .bin .slt b a
  | .eq => if b = .lit ⟨0⟩ then .un .iszero a else if a = .lit ⟨0⟩ then .un .iszero b
      else if b.lt a then .bin .eq b a else .bin .eq a b
  | _ => .bin f a b

def normBin (f : BinK) (a b : Sym) : Sym :=
  match ident f with
  | some e => acNorm f e (flat f a ++ flat f b)
  | none =>
    match a, b with
    | .lit x, .lit y => if foldable f then .lit (binF f x y) else normOp f a b
    | _, _ => normOp f a b

def normUn (f : UnK) (a : Sym) : Sym :=
  match a with
  | .lit x => .lit (unF f x)
  | _ => .un f a

/-- Canonical form used to compare window results. -/
def norm : Sym → Sym
  | .un f a => normUn f (norm a)
  | .bin f a b => normBin f (norm a) (norm b)
  | s => s

theorem add_law : ACLaw (binF .add) ⟨0⟩ := ident_law rfl
theorem mul_law : ACLaw (binF .mul) ⟨1⟩ := ident_law rfl

theorem normOp_val (base : List UInt256) (f : BinK) (a b : Sym) :
    (normOp f a b).val base = binF f (a.val base) (b.val base) := by
  unfold normOp
  split
  · split
    · subst_vars; simp only [Sym.val, binF, sub_self']
    · split
      · rename_i c _
        rw [acNorm_val add_law, fv_append add_law, flat_val add_law]
        simp only [fv, List.foldr_cons, List.foldr_nil, Sym.val, binF]
        rw [show UInt256.add (UInt256.sub ⟨0⟩ c) ⟨0⟩ = UInt256.sub ⟨0⟩ c from add_law.idr _, ← sub_add']
      · rfl
  · split
    · split
      · rw [acNorm_val mul_law, fv_append mul_law, flat_val mul_law]
        simp only [fv, List.foldr_cons, List.foldr_nil, Sym.val]
        rw [mul_law.idr]; show _ = flip UInt256.shiftLeft _ _; rw [shl_mul _ _ ‹_›]; rfl
      · simp only [Sym.val, binF]; rw [shl_big _ _ ‹_›]
    · rfl
  · split
    · split
      · split
        · rename_i k _ h0
          simp only [Sym.val, binF]
          rw [shr_div _ _ ‹_›]
          obtain ⟨⟨n, hn⟩⟩ := k; simp only at h0; subst h0
          obtain ⟨⟨y, hy⟩⟩ := b.val base
          simp only [UInt256.div, pow2, UInt256.ofNat, Id.run]; congr 1; apply Fin.ext
          show y = y / (2 ^ 0 % UInt256.size); simp [Nat.mod_eq_of_lt (show 1 < UInt256.size by decide)]
        · simp only [Sym.val, binF]; rw [shr_div _ _ ‹_›]
      · simp only [Sym.val, binF]; rw [shr_big _ _ ‹_›]
    · rfl
  · rfl
  · simp only [Sym.val, binF]; exact (sgt_slt _ _).symm
  · split
    · subst_vars; simp only [Sym.val, binF, unF]; exact (eq_zero _).symm
    · split
      · subst_vars; simp only [Sym.val, binF, unF]; rw [eq_comm']; exact (eq_zero _).symm
      · split
        · simp only [Sym.val, binF]; exact eq_comm' _ _
        · rfl
  · rfl

theorem normBin_val (base : List UInt256) (f : BinK) (a b : Sym) :
    (normBin f a b).val base = binF f (a.val base) (b.val base) := by
  unfold normBin
  split
  · rename_i e he
    have h := ident_law he
    rw [acNorm_val h, fv_append h, flat_val h, flat_val h]
  · split
    · split
      · rfl
      · exact normOp_val base f _ _
    · exact normOp_val base f a b

theorem normUn_val (base : List UInt256) (f : UnK) (a : Sym) :
    (normUn f a).val base = unF f (a.val base) := by
  unfold normUn; split <;> rfl

theorem norm_val (base : List UInt256) : ∀ s : Sym, (norm s).val base = s.val base
  | .input _ => rfl
  | .lit _ => rfl
  | .un f a => by simp only [norm, normUn_val, norm_val base a, Sym.val]
  | .bin f a b => by simp only [norm, normBin_val, norm_val base a, norm_val base b, Sym.val]


/-- Decidable window equivalence: the candidate needs no deeper stack, ends with
the same stack, costs no more gas, runs no more instructions and never grows
the stack above some height the original reaches. -/
def windowCheck (opsO opsN : List WOp) : Bool :=
  decide ((srun opsN ([], 0)).2 ≤ (srun opsO ([], 0)).2) &&
  decide (((srun opsN ([], 0)).1 ++ pulls (srun opsN ([], 0)).2
    ((srun opsO ([], 0)).2 - (srun opsN ([], 0)).2)).map norm = (srun opsO ([], 0)).1.map norm) &&
  decide (scost opsN ≤ scost opsO) && decide (opsN.length ≤ opsO.length) &&
  decide (0 < opsO.length) &&
  (sheights opsN ([], 0)).all (fun h => (sheights opsO ([], 0)).any (fun h' => decide (h ≤ h')))

theorem window_segment (owner : AccountAddress) (old new : ByteArray) (oj nj : Array UInt256)
    (P : UInt256 → Prop) (pc e : UInt256) (opsO opsN : List WOp)
    (wo : WCode old pc opsO e) (wn : WCode new pc opsN e) (check : windowCheck opsO opsN = true)
    (next : P e) : Segment owner old new oj nj P pc := by
  intro fuel s t surplus skipped r rel hpc ok
  have sc : s.executionEnv.code = old := rel.maps.2.2.1.2.1
  have tc : t.executionEnv.code = new := rel.maps.2.2.2.2.1
  have samePC := offset_pc rel
  have st := rel_stack rel
  simp only [windowCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true]
    at check
  obtain ⟨⟨⟨⟨⟨hMN, heq⟩, hcost⟩, hlen⟩, hpos⟩, hh⟩ := check
  have base0 : s.stack = ([] : List Sym).map (Sym.val s.stack) ++ s.stack.drop 0 := by simp
  obtain ⟨hMO, htsO, costO, gO, hgO, f, hf, finO⟩ :=
    window_source wo s.stack s [] 0 fuel r sc hpc (Nat.zero_le _) base0 ok
  have tgas : t.gasAvailable.toNat = s.gasAvailable.toNat + surplus := rel.gas
  obtain ⟨gN, hgN, cand⟩ := window_cand wn s.stack t [] 0 tc (by rw [← samePC, hpc])
    (by rw [← st]; exact base0) (by omega)
    (fun h hh' => by
      obtain ⟨h', hm, hle⟩ := hh h hh'
      have := htsO h' hm
      omega)
    (by omega)
  refine ⟨f, _, _, surplus + (scost opsO - scost opsN), skipped + (opsO.length - opsN.length),
    opsN.length, by omega, finO, next, ?_, fun g => cand g⟩
  have hstk : (srun opsO ([], 0)).1.map (Sym.val s.stack) ++ s.stack.drop (srun opsO ([], 0)).2 =
      (srun opsN ([], 0)).1.map (Sym.val s.stack) ++ s.stack.drop (srun opsN ([], 0)).2 := by
    have hd : s.stack.drop (srun opsO ([], 0)).2 = s.stack.drop ((srun opsN ([], 0)).2 +
        ((srun opsO ([], 0)).2 - (srun opsN ([], 0)).2)) := by congr 1; omega
    have vals : ∀ l : List Sym, l.map (Sym.val s.stack) = (l.map norm).map (Sym.val s.stack) := by
      intro l; rw [List.map_map]; congr 1; funext x; exact (norm_val _ x).symm
    rw [hd, vals (srun opsO ([], 0)).1, ← heq, ← vals, List.map_append, List.append_assoc,
      pulls_val _ _ _ (by omega)]
  refine ⟨?_, ?_, ?_, rel.maps⟩
  · rw [hstk]
    have h := congrArg (fun z : State => ({ z with
      stack := (srun opsN ([], 0)).1.map (Sym.val s.stack) ++ s.stack.drop (srun opsN ([], 0)).2
      pc := e } : State)) rel.frame
    simpa [eraseCount, deployedFrame, eraseMaps, eraseCodeGas] using h
  · change s.execLength + opsO.length = (t.execLength + opsN.length) + (skipped + (opsO.length - opsN.length))
    have := rel.count; omega
  · change gN.toNat = gO.toNat + (surplus + (scost opsO - scost opsN))
    omega

#print axioms window_source
#print axioms window_cand
#print axioms window_segment
end GolfWhole
