import WholeThread
import WholeSym
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition

/-! Window instructions and their interpreter facts. -/
namespace GolfWhole

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

theorem wfacts_dup (k : Nat) (v : (WOp.dup k).valid = true) : WFacts (.dup k) := by
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

theorem wfacts_swap (k : Nat) (v : (WOp.swap k).valid = true) : WFacts (.swap k) := by
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

#print axioms wfacts_dup
#print axioms wfacts_swap

end GolfWhole
