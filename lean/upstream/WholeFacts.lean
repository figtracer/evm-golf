import WholeWindow
import WholeCover
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition

/-! Per-point facts about the original stack, and their transfer along the program.
A certificate lists (pc, facts) entries; the invariant `Inv` says the current state
matches some entry. Generated proofs check each transfer by kernel evaluation. -/
namespace GolfWhole

/-- Knowledge about one stack slot: its value is below `2 ^ bits` and, when `set`
is given, is one of the listed numbers. -/
structure Abs where
  bits : Nat
  set : Option (List Nat)
  deriving DecidableEq

def top : Abs := ⟨256, none⟩

def Abs.holds (a : Abs) (v : UInt256) : Prop :=
  v.val.val < 2 ^ a.bits ∧ ∀ l, a.set = some l → v.val.val ∈ l

/-- Facts about the top slots, top first. The stack has at least as many slots. -/
def Holds : List Abs → List UInt256 → Prop
  | [], _ => True
  | _ :: _, [] => False
  | a :: as, v :: vs => a.holds v ∧ Holds as vs

theorem top_holds (v : UInt256) : top.holds v := ⟨lt_size v, fun _ h => by cases h⟩

/-- `a` implies `b`. A finite set also bounds the bit length. -/
def Abs.le (a b : Abs) : Bool :=
  (decide (a.bits ≤ b.bits) ||
    (match a.set with
     | some l => l.all (fun x => decide (x < 2 ^ b.bits))
     | none => false)) &&
  (match b.set with
   | none => true
   | some lb => match a.set with
     | some la => la.all (fun x => lb.contains x)
     | none => false)

theorem Abs.le_sound {a b : Abs} (h : a.le b = true) {v : UInt256} (hv : a.holds v) : b.holds v := by
  obtain ⟨ab, aset⟩ := a
  obtain ⟨bb, bset⟩ := b
  obtain ⟨hb, hs⟩ := hv
  simp only [Abs.le, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h hb hs
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rcases h1 with h1 | h1
    · exact lt_of_lt_of_le hb (pow_mono h1)
    · cases aset with
      | none => cases h1
      | some l =>
        simp only [List.all_eq_true, decide_eq_true_eq] at h1
        exact h1 _ (hs l rfl)
  · intro lb e
    simp only at e
    subst e
    cases aset with
    | none => cases h2
    | some la =>
      simp only [List.all_eq_true, List.contains_iff_mem] at h2
      exact h2 _ (hs la rfl)

/-- Every fact of `gs` follows from `fs`. -/
def implies : List Abs → List Abs → Bool
  | _, [] => true
  | [], _ :: _ => false
  | a :: as, b :: bs => a.le b && implies as bs

theorem implies_sound : ∀ (fs gs : List Abs) (st : List UInt256),
    implies fs gs = true → Holds fs st → Holds gs st
  | _, [], _, _, _ => trivial
  | [], _ :: _, _, h, _ => by simp [implies] at h
  | _ :: _, _ :: _, [], _, h => by simp [Holds] at h
  | a :: as, b :: bs, v :: vs, h, ⟨ha, hs⟩ => by
    simp only [implies, Bool.and_eq_true] at h
    exact ⟨Abs.le_sound h.1 ha, implies_sound as bs vs h.2 hs⟩

theorem holds_drop : ∀ (fs : List Abs) (st : List UInt256) (m : Nat), Holds fs st →
    Holds (fs.drop m) (st.drop m)
  | fs, st, 0, h => by simpa using h
  | [], st, m + 1, _ => by simp [Holds]
  | _ :: _, [], m + 1, h => by simp [Holds] at h
  | _ :: fs, _ :: st, m + 1, ⟨_, h⟩ => by simpa using holds_drop fs st m h

theorem holds_append : ∀ (as : List Abs) (xs : List UInt256) (bs : List Abs) (ys : List UInt256),
    Holds as xs → as.length = xs.length → Holds bs ys → Holds (as ++ bs) (xs ++ ys)
  | [], [], _, _, _, _, h => by simpa using h
  | [], _ :: _, _, _, _, e, _ => by simp at e
  | _ :: _, [], _, _, _, e, _ => by simp at e
  | a :: as, x :: xs, bs, ys, ⟨ha, h⟩, e, hb => ⟨ha, holds_append as xs bs ys h (by simpa using e) hb⟩

theorem holds_getD : ∀ (fs : List Abs) (st : List UInt256), Holds fs st →
    ∀ i, (fs.getD i top).holds (st.getD i ⟨0⟩)
  | [], st, _, i => by simp only [List.getD_nil]; exact top_holds _
  | _ :: _, [], h, _ => by simp [Holds] at h
  | a :: fs, v :: st, ⟨ha, _⟩, 0 => ha
  | a :: fs, v :: st, ⟨_, h⟩, i + 1 => by simpa using holds_getD fs st h i

theorem holds_fits {fs : List Abs} {st : List UInt256} (h : Holds fs st) :
    Fits (fs.map Abs.bits) st := by
  intro i
  have hg := (holds_getD fs st h i).1
  have e : (fs.map Abs.bits).getD i 256 = (fs.getD i top).bits := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases fs[i]? <;> rfl
  rw [e]; exact hg

def litAbs (v : UInt256) : Abs := ⟨bitLen v.val.val, some [v.val.val]⟩

/-- Facts about a symbolic term over a stack described by `fs`. -/
def absOf (fs : List Abs) : Sym → Abs
  | .input i => fs.getD i top
  | .lit v => litAbs v
  | .un f a => ⟨(Sym.un f a).bits (fs.map Abs.bits), none⟩
  | .bin f a b => ⟨(Sym.bin f a b).bits (fs.map Abs.bits), none⟩

theorem absOf_holds {fs : List Abs} {st : List UInt256} (h : Holds fs st) :
    ∀ s : Sym, (absOf fs s).holds (s.val st)
  | .input i => holds_getD fs st h i
  | .lit v => ⟨bitLen_lt (lt_size v), fun l e => by
      cases e; exact List.mem_singleton_self _⟩
  | .un f a => ⟨bits_sound _ st (holds_fits h) (.un f a), fun _ e => by cases e⟩
  | .bin f a b => ⟨bits_sound _ st (holds_fits h) (.bin f a b), fun _ e => by cases e⟩

theorem holds_map {fs : List Abs} {st : List UInt256} (h : Holds fs st) :
    ∀ l : List Sym, Holds (l.map (absOf fs)) (l.map (Sym.val st))
  | [] => trivial
  | s :: l => ⟨absOf_holds h s, holds_map h l⟩

/-- Facts after replacing the top `m` slots by the terms `a`. -/
def xferS (a : List Sym) (m : Nat) (fs : List Abs) : List Abs := a.map (absOf fs) ++ fs.drop m

theorem holds_xferS {fs : List Abs} {st : List UInt256} (h : Holds fs st) (a : List Sym) (m : Nat) :
    Holds (xferS a m fs) (a.map (Sym.val st) ++ st.drop m) :=
  holds_append _ _ _ _ (holds_map h a) (by simp) (holds_drop fs st m h)

/-! Stack effects of single instructions. -/

/-- Every successful step of `op` from a stack with enough inputs relates the stacks by `E`. -/
def Eff (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (E : List UInt256 → List UInt256 → Prop) : Prop :=
  ∀ (f : ℕ) (u v : State), (δ op).getD 0 ≤ u.stack.length →
    EVM.step (f + 1) (C' u op) (some (op, arg)) u = .ok v → E u.stack v.stack

theorem eff_wop (op : WOp) (v : op.valid = true) :
    Eff op.op op.arg (fun st st' => op.need ≤ st.length ∧ st' = op.apply id binF unF st) := by
  intro f u w hin step
  have F := wfacts op v
  rw [F.inputs] at hin
  rw [F.cost, F.step f u hin] at step
  injection step with step
  subst step
  exact ⟨hin, rfl⟩

def xferW (op : WOp) (fs : List Abs) : List Abs :=
  xferS (sstep op ([], 0)).1 (sstep op ([], 0)).2 fs

theorem xf_wop {op : WOp} (v : op.valid = true) {fs fs' : List Abs}
    (chk : implies (xferW op fs) fs' = true) :
    ∀ st st', (op.need ≤ st.length ∧ st' = op.apply id binF unF st) → Holds fs st → Holds fs' st' := by
  rintro st st' ⟨hin, rfl⟩ h
  apply implies_sound _ _ _ chk
  have F := wfacts op v
  obtain ⟨-, e⟩ := sstep_sound op st [] 0 F.dup1 (by simpa using hin)
  simp only [List.map_nil, List.nil_append, List.drop_zero] at e
  rw [e]
  exact holds_xferS h _ _

/-- `op` pops `pop` slots and pushes values described by `outs`. -/
def Shape (pop : Nat) (outs : List Abs) (st st' : List UInt256) : Prop :=
  ∃ o, st' = o ++ st.drop pop ∧ o.length = outs.length ∧ Holds outs o

theorem xf_shape {pop : Nat} {outs fs fs' : List Abs} (chk : implies (outs ++ fs.drop pop) fs' = true) :
    ∀ st st', Shape pop outs st st' → Holds fs st → Holds fs' st' := by
  rintro st st' ⟨o, rfl, len, ho⟩ h
  exact implies_sound _ _ _ chk (holds_append _ _ _ _ ho len.symm (holds_drop fs st pop h))

/-! The invariant and the generic successor obligations. -/

/-- The state matches some certificate entry. -/
def Inv (T : List (Nat × List Abs)) (pc : UInt256) (st : List UInt256) : Prop :=
  ∃ p ∈ T, pc = UInt256.ofNat p.1 ∧ Holds p.2 st

theorem inv_of {T : List (Nat × List Abs)} {x : UInt256} {n : Nat} {fs fs' : List Abs} {st : List UInt256}
    (sum : x = UInt256.ofNat n) (mem : (n, fs') ∈ T) (chk : implies fs fs' = true) (h : Holds fs st) :
    Inv T x st :=
  ⟨(n, fs'), mem, sum, implies_sound _ _ _ chk h⟩

theorem same_next {T : List (Nat × List Abs)} {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    {E : List UInt256 → List UInt256 → Prop} {pc : UInt256} {k n : Nat} {fs fs' : List Abs}
    (eff : Eff op arg E) (xf : ∀ st st', E st st' → Holds fs st → Holds fs' st')
    (sum : pc + UInt256.ofNat k = UInt256.ofNat n) (mem : (n, fs') ∈ T) :
    ∀ (f : ℕ) (u v : State), (δ op).getD 0 ≤ u.stack.length →
      EVM.step (f + 1) (C' u op) (some (op, arg)) u = .ok v → Holds fs u.stack →
      Inv T (pc + UInt256.ofNat k) v.stack :=
  fun f u v hin step h => ⟨(n, fs'), mem, sum, xf _ _ (eff f u v hin step) h⟩

theorem ofNat_val (x : UInt256) : UInt256.ofNat x.val.val = x := by
  obtain ⟨⟨n, hn⟩⟩ := x
  apply ext'
  show (Fin.ofNat UInt256.size n).val = n
  simp only [Fin.ofNat, Nat.mod_eq_of_lt hn]

/-- Every listed destination that is a valid jump target is covered. -/
def TargetsOk (T : List (Nat × List Abs)) (oj : Array UInt256) (fs : List Abs) (S : List Nat) : Prop :=
  ∀ c ∈ S, ∀ tail, Holds fs tail → oj.contains (UInt256.ofNat c) = true → Inv T (UInt256.ofNat c) tail

theorem targets_nil {T oj fs} : TargetsOk T oj fs [] := fun _ h => by cases h

theorem targets_mem {T oj fs} {c : Nat} {fc : List Abs} {S : List Nat} (mem : (c, fc) ∈ T)
    (chk : implies fs fc = true) (rest : TargetsOk T oj fs S) : TargetsOk T oj fs (c :: S) := by
  intro c' hc tail h valid
  rcases List.mem_cons.mp hc with rfl | hc
  · exact inv_of rfl mem chk h
  · exact rest c' hc tail h valid

theorem targets_bad {T oj fs} {c : Nat} {S : List Nat} (bad : oj.contains (UInt256.ofNat c) = false)
    (rest : TargetsOk T oj fs S) : TargetsOk T oj fs (c :: S) := by
  intro c' hc tail h valid
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [bad] at valid; cases valid
  · exact rest c' hc tail h valid

theorem target_of {T oj} {a : Abs} {fs : List Abs} {S : List Nat} (hs : a.set = some S)
    (ok : TargetsOk T oj fs S) {x : UInt256} {tail : List UInt256} (ha : a.holds x) (h : Holds fs tail)
    (valid : oj.contains x = true) : Inv T x tail := by
  have m := ha.2 S hs
  have r := ok _ m tail h (by rw [ofNat_val]; exact valid)
  rwa [ofNat_val] at r

theorem jump_set {T oj} {a : Abs} {fs : List Abs} {S : List Nat} (hs : a.set = some S)
    (ok : TargetsOk T oj fs S) :
    ∀ x tail, Holds (a :: fs) (x :: tail) → oj.contains x = true → Inv T x tail :=
  fun _ _ ⟨ha, h⟩ valid => target_of hs ok ha h valid

theorem jump_any {T : List (Nat × List Abs)} {oj : Array UInt256} {A : List UInt256 → Prop}
    (all : ∀ x, oj.contains x = true → ∀ st, Inv T x st) :
    ∀ x tail, A (x :: tail) → oj.contains x = true → Inv T x tail :=
  fun x tail _ valid => all x valid tail

theorem jumpi_set {T oj} {a : Abs} {fs : List Abs} {S : List Nat} (hs : a.set = some S)
    (ok : TargetsOk T oj (fs.drop 1) S) :
    ∀ x b tail, Holds (a :: fs) (x :: b :: tail) → b ≠ ⟨0⟩ → oj.contains x = true → Inv T x tail :=
  fun _ _ tail ⟨ha, h⟩ _ valid => target_of hs ok ha (by simpa using holds_drop fs _ 1 h) valid

theorem jumpi_any {T : List (Nat × List Abs)} {oj : Array UInt256} {A : List UInt256 → Prop}
    (all : ∀ x, oj.contains x = true → ∀ st, Inv T x st) :
    ∀ x b tail, A (x :: b :: tail) → b ≠ ⟨0⟩ → oj.contains x = true → Inv T x tail :=
  fun x _ tail _ _ valid => all x valid tail

theorem jumpi_next {T : List (Nat × List Abs)} {x : UInt256} {n : Nat} {fs fs' : List Abs}
    (sum : x = UInt256.ofNat n) (mem : (n, fs') ∈ T) (chk : implies (fs.drop 2) fs' = true) :
    ∀ y tail, Holds fs (y :: ⟨0⟩ :: tail) → Inv T x tail :=
  fun _ tail h => inv_of sum mem chk (by simpa using holds_drop fs _ 2 h)

/-- Fall-through and taken successors of a threaded JUMPI. -/
theorem thread_fall {T : List (Nat × List Abs)} {x : UInt256} {n : Nat} {fs fs' : List Abs}
    (sum : x = UInt256.ofNat n) (mem : (n, fs') ∈ T) (chk : implies (fs.drop 1) fs' = true) :
    ∀ tail, Holds fs (⟨0⟩ :: tail) → Inv T x tail :=
  fun tail h => inv_of sum mem chk (by simpa using holds_drop fs _ 1 h)

theorem thread_target {T : List (Nat × List Abs)} {x : UInt256} {n : Nat} {fs fs' : List Abs}
    (sum : x = UInt256.ofNat n) (mem : (n, fs') ∈ T) (chk : implies (fs.drop 1) fs' = true) :
    ∀ c tail, Holds fs (c :: tail) → c ≠ ⟨0⟩ → Inv T x tail :=
  fun _ tail h _ => inv_of sum mem chk (by simpa using holds_drop fs _ 1 h)

theorem power_next {T : List (Nat × List Abs)} {x : UInt256} {n : Nat} {fs fs' : List Abs}
    {g : UInt256 → UInt256}
    (sum : x = UInt256.ofNat n) (mem : (n, fs') ∈ T) (chk : implies (top :: fs.drop 1) fs' = true) :
    ∀ a tail, Holds fs (a :: tail) → Inv T x (g a :: tail) :=
  fun a tail h => inv_of sum mem chk ⟨top_holds _, by simpa using holds_drop fs _ 1 h⟩

theorem window_next {T : List (Nat × List Abs)} {x : UInt256} {n : Nat} {fs fs' : List Abs}
    (opsO : List WOp) (sum : x = UInt256.ofNat n) (mem : (n, fs') ∈ T)
    (chk : implies (xferS (srun opsO ([], 0)).1 (srun opsO ([], 0)).2 fs) fs' = true) :
    ∀ st, Holds fs st →
      Inv T x ((srun opsO ([], 0)).1.map (Sym.val st) ++ st.drop (srun opsO ([], 0)).2) :=
  fun _ h => inv_of sum mem chk (holds_xferS h _ _)

/-- Successor of a call: the inputs are popped and the status word is pushed. -/
theorem call_next {T : List (Nat × List Abs)} {x : UInt256} {n pop : Nat} {fs fs' : List Abs}
    (sum : x = UInt256.ofNat n) (mem : (n, fs') ∈ T) (chk : implies (top :: fs.drop pop) fs' = true) :
    ∀ st y, Holds fs st → (y = ⟨0⟩ ∨ y = ⟨1⟩) → Inv T x (y :: st.drop pop) :=
  fun st _ h _ => inv_of sum mem chk ⟨top_holds _, holds_drop fs st pop h⟩

theorem window_fits {fs : List Abs} : ∀ st, Holds fs st → Fits (fs.map Abs.bits) st :=
  fun _ h => holds_fits h

/-! Assembling the cover from per-entry obligations. -/

theorem mem_at {α : Type} {l : List α} (i : Nat) {x : α} (h : l[i]? = some x) : x ∈ l :=
  List.mem_of_getElem? h

theorem entries_cons {R : Nat × List Abs → Prop} {a : Nat × List Abs} {l : List (Nat × List Abs)}
    (ha : R a) (hl : ∀ p ∈ l, R p) : ∀ p ∈ a :: l, R p := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ha
  · exact hl p hp

theorem entries_nil {R : Nat × List Abs → Prop} : ∀ p ∈ ([] : List (Nat × List Abs)), R p :=
  fun _ h => by cases h

theorem entries_app {R : Nat × List Abs → Prop} {l₁ l₂ : List (Nat × List Abs)}
    (h₁ : ∀ p ∈ l₁, R p) (h₂ : ∀ p ∈ l₂, R p) : ∀ p ∈ l₁ ++ l₂, R p := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact h₁ p hp
  · exact h₂ p hp

theorem cover_of {HC : Prop} {old new : ByteArray} {oj : Array UInt256} {T : List (Nat × List Abs)}
    (h : ∀ p ∈ T, Point HC old new oj (Inv T) (Holds p.2) (UInt256.ofNat p.1)) :
    ∀ pc st, Inv T pc st → ∃ A : List UInt256 → Prop, A st ∧ Point HC old new oj (Inv T) A pc := by
  rintro pc st ⟨p, mem, rfl, hh⟩
  exact ⟨Holds p.2, hh, h p mem⟩

/-- Entries without facts. -/
def tops (T : List (Nat × List Abs)) : List Nat :=
  T.filterMap (fun p => if p.2.isEmpty then some p.1 else none)

theorem tops_mem {T : List (Nat × List Abs)} {n : Nat} (h : n ∈ tops T) : (n, []) ∈ T := by
  simp only [tops, List.mem_filterMap] at h
  obtain ⟨⟨m, fs⟩, mem, e⟩ := h
  cases fs with
  | nil => simp only [List.isEmpty_nil, if_true, Option.some.injEq] at e; subst e; exact mem
  | cons _ _ => simp at e

theorem mem_of_contains {l : List Nat} {x : UInt256} (h : (l.map UInt256.ofNat).contains x = true) :
    ∃ n ∈ l, x = UInt256.ofNat n := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    simp only [List.map_cons, List.contains_cons, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨y, List.mem_cons_self, word_eq_of_beq h⟩
    · obtain ⟨n, hn, e⟩ := ih h
      exact ⟨n, List.mem_cons_of_mem _ hn, e⟩

/-- Jumps with unknown destinations reach entries without facts. -/
theorem top_targets (T : List (Nat × List Abs)) (jumpsN : List Nat)
    (h : subsetSorted jumpsN (tops T) = true) :
    ∀ x, (jumpsN.map UInt256.ofNat).toArray.contains x = true → ∀ st, Inv T x st := by
  intro x hx st
  obtain ⟨n, hn, e⟩ := mem_of_contains (jumps_points jumpsN (tops T) h x hx)
  exact ⟨(n, []), tops_mem hn, e, trivial⟩

#print axioms implies_sound
#print axioms xf_wop
#print axioms xf_shape
#print axioms same_next
#print axioms jump_set
#print axioms window_next
#print axioms call_next
#print axioms cover_of
#print axioms top_targets

end GolfWhole
