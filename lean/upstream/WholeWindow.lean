import WholeThread
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition

/-! Straight-line stack windows (PUSH, DUP, SWAP, POP) with a symbolic stack. -/
namespace GolfWhole

/-- Binary window operations, as the interpreter applies them to (top, second). -/
inductive BinK where
  | add | sub | and | or | shl
  deriving DecidableEq

def binF : BinK → UInt256 → UInt256 → UInt256
  | .add => UInt256.add
  | .sub => UInt256.sub
  | .and => UInt256.land
  | .or => UInt256.lor
  | .shl => flip UInt256.shiftLeft

inductive Sym where
  | input (i : Nat)
  | lit (v : UInt256)
  | bin (f : BinK) (a b : Sym)
  deriving DecidableEq

instance : Inhabited Sym := ⟨.lit ⟨0⟩⟩

def Sym.val (base : List UInt256) : Sym → UInt256
  | .input i => base.getD i ⟨0⟩
  | .lit v => v
  | .bin f a b => binF f (a.val base) (b.val base)

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
  | bin (f : BinK)
  deriving DecidableEq

def WOp.need : WOp → Nat
  | .push _ _ _ => 0
  | .push0 => 0
  | .dup k => k
  | .swap k => k + 1
  | .pop => 1
  | .bin _ => 2

def WOp.cost : WOp → Nat
  | .pop => 2
  | .push0 => 2
  | _ => 3

def WOp.len : WOp → Nat
  | .push _ _ w => w + 1
  | _ => 1

def WOp.apply {α : Type} [Inhabited α] (lit : UInt256 → α) (bin : BinK → α → α → α) :
    WOp → List α → List α
  | .push _ v _, l => lit v :: l
  | .push0, l => lit ⟨0⟩ :: l
  | .dup k, l => (l.take k).getLast! :: l
  | .swap k, l => swapList k l
  | .pop, l => l.tail
  | .bin f, a :: b :: l => bin f a b :: l
  | .bin _, l => l

theorem apply_append (op : WOp) (base : List UInt256) (a : List Sym) (rest : List UInt256)
    (h : op.need ≤ a.length) (k1 : ∀ k, op = .dup k → 1 ≤ k) :
    op.apply id binF (a.map (Sym.val base) ++ rest) =
      (op.apply Sym.lit Sym.bin a).map (Sym.val base) ++ rest := by
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
  | bin f =>
    simp only [WOp.need] at h
    match a, h with
    | x :: y :: a', _ => rfl

/-- Symbolic inputs `m, m+1, ...` pulled from below the explicit stack. -/
def pulls (m n : Nat) : List Sym := (List.range n).map fun i => .input (m + i)

def sstep (op : WOp) (st : List Sym × Nat) : List Sym × Nat :=
  let extra := op.need - st.1.length
  (op.apply Sym.lit Sym.bin (st.1 ++ pulls st.2 extra), st.2 + extra)

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
    op.apply id binF (a.map (Sym.val base) ++ base.drop m) =
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
  | .bin .add => .ADD
  | .bin .sub => .SUB
  | .bin .and => .AND
  | .bin .or => .OR
  | .bin .shl => .SHL

def WOp.arg : WOp → Option (UInt256 × Nat)
  | .push _ v w => some (v, w)
  | _ => none

def WOp.valid : WOp → Bool
  | .push p _ _ => p != .PUSH0
  | .push0 => true
  | .dup k => 1 ≤ k && k ≤ 16
  | .swap k => 1 ≤ k && k ≤ 16
  | .pop => true
  | .bin _ => true

/-- Static facts about a valid window instruction. -/
structure WFacts (op : WOp) : Prop where
  cost : ∀ s, C' s op.op = op.cost
  mem : ∀ s, memoryExpansionCost s op.op = 0
  run : Running op.op
  inputs : (δ op.op).getD 0 = op.need
  defined : δ op.op ≠ none
  outputs : ∀ l : List UInt256, op.need ≤ l.length →
    l.length - (δ op.op).getD 0 + (α op.op).getD 0 = (op.apply id binF l).length
  notJump : op.op ≠ .JUMP ∧ op.op ≠ .JUMPI ∧ op.op ≠ .RETURNDATACOPY ∧ op.op ≠ .SSTORE
  static : ∀ st, W op.op st = false
  create : op.op.isCreate = false
  step : ∀ (f : ℕ) (u : State), op.need ≤ u.stack.length →
    EVM.step (f + 1) op.cost (some (op.op, op.arg)) u =
      .ok ((bump u op.cost).replaceStackAndIncrPC (op.apply id binF u.stack) op.len)
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
         change EVM.execBinOp _ (bump u 3) = _
         unfold EVM.execBinOp
         have : (bump u 3).stack = x :: y :: l' := hs
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
      ih ((bump u op.cost).replaceStackAndIncrPC (op.apply id binF u.stack) op.len)
        (sstep op (a, m)).1 (sstep op (a, m)).2 f r hc
        (by rw [← adv, ← hpc]; rfl) fits
        (by show op.apply id binF u.stack = _; rw [hst]; exact sound) run
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
      ih ((bump u op.cost).replaceStackAndIncrPC (op.apply id binF u.stack) op.len)
        (sstep op (a, m)).1 (sstep op (a, m)).2 hc (by rw [← adv, ← hpc]; rfl)
        (by show op.apply id binF u.stack = _; rw [hst]; exact sound) hM'
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


theorem land_self' (a : UInt256) : UInt256.land a a = a := by
  obtain ⟨x⟩ := a; simp only [UInt256.land, UInt256.mk.injEq]; apply Fin.ext
  show (x.val &&& x.val) % UInt256.size = x.val
  rw [Nat.and_self, Nat.mod_eq_of_lt x.isLt]
theorem land_absorb (a b : UInt256) : UInt256.land a (UInt256.land a b) = UInt256.land a b := by
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := b
  simp only [UInt256.land, UInt256.mk.injEq]; apply Fin.ext
  show (x.val &&& ((x.val &&& y.val) % UInt256.size)) % UInt256.size = (x.val &&& y.val) % UInt256.size
  have hxy : (x.val &&& y.val) % UInt256.size = x.val &&& y.val :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left x.isLt)
  rw [hxy, ← Nat.and_assoc, Nat.and_self, hxy]
theorem shl_zero (b : UInt256) : UInt256.shiftLeft b ⟨0⟩ = b := by
  obtain ⟨x⟩ := b; simp only [UInt256.shiftLeft]
  simp only [ge_iff_le]
  rw [if_neg (by decide)]
  congr 1; apply Fin.ext
  show (x.val <<< (0 : Fin UInt256.size).val) % UInt256.size = x.val
  simp [Nat.mod_eq_of_lt x.isLt]

theorem lor_self' (a : UInt256) : UInt256.lor a a = a := by
  obtain ⟨x⟩ := a; simp only [UInt256.lor, UInt256.mk.injEq]; apply Fin.ext
  show (x.val ||| x.val) % UInt256.size = x.val
  rw [Nat.or_self, Nat.mod_eq_of_lt x.isLt]

theorem add_zero' (a : UInt256) : UInt256.add a ⟨0⟩ = a := by
  obtain ⟨x⟩ := a; simp [UInt256.add]

theorem zero_add' (a : UInt256) : UInt256.add ⟨0⟩ a = a := by
  obtain ⟨x⟩ := a; simp [UInt256.add]

theorem sub_zero' (a : UInt256) : UInt256.sub a ⟨0⟩ = a := by
  obtain ⟨x⟩ := a; simp [UInt256.sub]

def andRule (a b : Sym) : Sym :=
  match b with
  | .bin .and a' _ => if a' = a then b else .bin .and a b
  | _ => .bin .and a b

def normRule : BinK → Sym → Sym → Sym
  | .add, a, b => if b = .lit ⟨0⟩ then a else if a = .lit ⟨0⟩ then b else .bin .add a b
  | .sub, a, b => if b = .lit ⟨0⟩ then a else .bin .sub a b
  | .and, a, b => if a = b then a else andRule a b
  | .or, a, b => if a = b then a else .bin .or a b
  | .shl, a, b => if a = .lit ⟨0⟩ then b else .bin .shl a b

/-- Constant folding and identities used to compare window results. -/
def normBin (f : BinK) (a b : Sym) : Sym :=
  match a, b with
  | .lit x, .lit y => .lit (binF f x y)
  | _, _ => normRule f a b

def norm : Sym → Sym
  | .bin f a b => normBin f (norm a) (norm b)
  | s => s

theorem andRule_val (base : List UInt256) (a b : Sym) :
    (andRule a b).val base = binF .and (a.val base) (b.val base) := by
  unfold andRule
  split
  · split
    · subst_vars; simp [Sym.val, binF, land_absorb]
    · rfl
  · rfl

theorem normRule_val (base : List UInt256) (f : BinK) (a b : Sym) :
    (normRule f a b).val base = binF f (a.val base) (b.val base) := by
  cases f <;> simp only [normRule]
  · split
    · subst_vars; simp [Sym.val, binF, add_zero']
    · split
      · subst_vars; simp [Sym.val, binF, zero_add']
      · rfl
  · split
    · subst_vars; simp [Sym.val, binF, sub_zero']
    · rfl
  · split
    · subst_vars; simp [binF, land_self']
    · exact andRule_val base a b
  · split
    · subst_vars; simp [binF, lor_self']
    · rfl
  · split
    · subst_vars; simp [Sym.val, binF, flip, shl_zero]
    · rfl

theorem normBin_val (base : List UInt256) (f : BinK) (a b : Sym) :
    (normBin f a b).val base = binF f (a.val base) (b.val base) := by
  unfold normBin
  split
  · rfl
  · exact normRule_val base f a b

theorem norm_val (base : List UInt256) : ∀ s : Sym, (norm s).val base = s.val base
  | .input _ => rfl
  | .lit _ => rfl
  | .bin f a b => by
    simp only [norm, normBin_val, norm_val base a, norm_val base b, Sym.val]

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
