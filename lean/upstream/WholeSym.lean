import Driver
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open EvmYul

/-! Symbolic window terms and a verified normalizer for comparing them. -/
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

/-- Bit length with structural recursion, so the kernel evaluates it. -/
def bitLenAux : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => if n = 0 then 0 else bitLenAux k (n / 2) + 1

def bitLen (n : Nat) : Nat := bitLenAux 256 n

theorem bitLenAux_lt : ∀ (k n : Nat), n < 2 ^ k → n < 2 ^ bitLenAux k n
  | 0, n, h => by simp only [bitLenAux]; exact h
  | k + 1, n, h => by
    simp only [bitLenAux]
    split
    · simp_all
    · have hk : n / 2 < 2 ^ k := by rw [Nat.pow_succ] at h; omega
      have ih := bitLenAux_lt k (n / 2) hk
      rw [Nat.pow_succ]; omega

theorem bitLen_lt {n : Nat} (h : n < 2 ^ 256) : n < 2 ^ bitLen n := bitLenAux_lt 256 n h

/-- An upper bound on the bit length of a term's value, given bounds `env` on the
inputs (missing entries mean 256). -/
def Sym.bits (env : List Nat) : Sym → Nat
  | .input i => env.getD i 256
  | .lit v => bitLen v.val.val
  | .un .iszero _ => 1
  | .un .not _ => 256
  | .bin f a b =>
    match f with
    | .and => min (a.bits env) (b.bits env)
    | .or | .xor => max (a.bits env) (b.bits env)
    | .lt | .gt | .slt | .sgt | .eq => 1
    | .div | .mod => a.bits env
    | .shr => b.bits env
    | _ => 256

theorem lt_size (x : UInt256) : x.val.val < 2 ^ 256 := x.val.isLt

theorem fromBool_lt (b : Bool) : (UInt256.fromBool b).val.val < 2 ^ 1 := by
  cases b <;> decide

theorem pow_mono {m n : Nat} (h : m ≤ n) : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) h

/-- Every input fits its bound in `env`. -/
def Fits (env : List Nat) (base : List UInt256) : Prop :=
  ∀ i, (base.getD i ⟨0⟩).val.val < 2 ^ env.getD i 256

theorem fits_nil (base : List UInt256) : Fits [] base := fun _ => lt_size _

theorem bits_sound (env : List Nat) (base : List UInt256) (hf : Fits env base) :
    ∀ s : Sym, (s.val base).val.val < 2 ^ s.bits env
  | .input i => hf i
  | .lit v => bitLen_lt (lt_size v)
  | .un .iszero _ => fromBool_lt _
  | .un .not _ => lt_size _
  | .bin f a b => by
    have ha := bits_sound env base hf a
    have hb := bits_sound env base hf b
    cases f <;> simp only [Sym.bits, Sym.val, binF]
    all_goals first
      | exact lt_size _
      | exact fromBool_lt _
      | skip
    · -- div
      generalize Sym.val base a = va at ha ⊢; generalize Sym.val base b = vb at hb ⊢
      obtain ⟨⟨x, hx⟩⟩ := va; obtain ⟨⟨y, hy⟩⟩ := vb
      exact lt_of_le_of_lt (Nat.div_le_self _ _) ha
    · -- mod
      generalize Sym.val base a = va at ha ⊢; generalize Sym.val base b = vb at hb ⊢
      obtain ⟨⟨x, hx⟩⟩ := va; obtain ⟨⟨y, hy⟩⟩ := vb
      simp only [UInt256.mod]
      split
      · exact lt_of_lt_of_le (show 0 < 2 ^ _ from Nat.two_pow_pos _) (le_refl _)
      · exact lt_of_le_of_lt (Nat.mod_le _ _) ha
    · -- and
      generalize Sym.val base a = va at ha ⊢; generalize Sym.val base b = vb at hb ⊢
      obtain ⟨x⟩ := va; obtain ⟨y⟩ := vb
      rw [land_v]
      rcases Nat.le_total (a.bits env) (b.bits env) with h | h
      · rw [Nat.min_eq_left h]; exact lt_of_le_of_lt Nat.and_le_left ha
      · rw [Nat.min_eq_right h]; exact lt_of_le_of_lt Nat.and_le_right hb
    · -- or
      generalize Sym.val base a = va at ha ⊢; generalize Sym.val base b = vb at hb ⊢
      obtain ⟨x⟩ := va; obtain ⟨y⟩ := vb
      rw [lor_v]
      exact Nat.or_lt_two_pow (lt_of_lt_of_le ha (pow_mono (Nat.le_max_left _ _)))
        (lt_of_lt_of_le hb (pow_mono (Nat.le_max_right _ _)))
    · -- xor
      generalize Sym.val base a = va at ha ⊢; generalize Sym.val base b = vb at hb ⊢
      obtain ⟨x⟩ := va; obtain ⟨y⟩ := vb
      rw [xor_v]
      exact Nat.xor_lt_two_pow (lt_of_lt_of_le ha (pow_mono (Nat.le_max_left _ _)))
        (lt_of_lt_of_le hb (pow_mono (Nat.le_max_right _ _)))
    · -- shr
      generalize Sym.val base a = va at ha ⊢; generalize Sym.val base b = vb at hb ⊢
      obtain ⟨⟨x, hx⟩⟩ := va; obtain ⟨⟨y, hy⟩⟩ := vb
      simp only [flip, UInt256.shiftRight]
      split
      · exact Nat.two_pow_pos _
      · exact lt_of_le_of_lt (le_trans (Nat.mod_le _ _) (Nat.shiftRight_le _ _)) hb

def minBits (env : List Nat) (l : List Sym) : Nat := l.foldr (fun s m => min (s.bits env) m) 256

theorem and_fold_lt (env : List Nat) (base : List UInt256) (hf : Fits env base) : ∀ l : List Sym,
    (fv (binF .and) ones base l).val.val < 2 ^ minBits env l
  | [] => lt_size _
  | x :: l => by
    have hx := bits_sound env base hf x
    have hl := and_fold_lt env base hf l
    simp only [fv, List.foldr_cons, minBits] at hl ⊢
    generalize List.foldr (fun s acc => binF BinK.and (Sym.val base s) acc) ones l = r at hl ⊢
    generalize Sym.val base x = vx at hx ⊢
    obtain ⟨u⟩ := vx; obtain ⟨w⟩ := r
    show (UInt256.land ⟨u⟩ ⟨w⟩).val.val < _
    rw [land_v]
    rcases Nat.le_total (x.bits env) (List.foldr (fun s m => min (s.bits env) m) 256 l) with h | h
    · rw [Nat.min_eq_left h]; exact lt_of_le_of_lt Nat.and_le_left hx
    · rw [Nat.min_eq_right h]; exact lt_of_le_of_lt Nat.and_le_right hl

/-- A literal mask that keeps every bit an `and` operand list can have set. -/
def maskDrop (env : List Nat) (f : BinK) (c : UInt256) (rest : List Sym) : Bool :=
  f == .and && c.val.val &&& (2 ^ minBits env rest - 1) == 2 ^ minBits env rest - 1

theorem mask_keep (c y m : Nat) (hy : y < 2 ^ m) (hc : c &&& (2 ^ m - 1) = 2 ^ m - 1) :
    c &&& y = y := by
  have e : y &&& (2 ^ m - 1) = y := by rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hy]
  calc c &&& y = c &&& (y &&& (2 ^ m - 1)) := by rw [e]
    _ = (c &&& (2 ^ m - 1)) &&& y := by rw [Nat.and_comm y, ← Nat.and_assoc]
    _ = y := by rw [hc, Nat.and_comm, e]

theorem maskDrop_val (env : List Nat) (base : List UInt256) (hf : Fits env base) (c : UInt256)
    (rest : List Sym) (h : maskDrop env .and c rest = true) :
    binF .and c (fv (binF .and) ones base rest) = binF .and ones (fv (binF .and) ones base rest) := by
  have hb := and_fold_lt env base hf rest
  simp only [maskDrop, beq_self_eq_true, Bool.true_and, beq_iff_eq] at h
  generalize fv (binF .and) ones base rest = r at hb ⊢
  rw [show binF .and ones r = r from land_idl r]
  obtain ⟨cv⟩ := c; obtain ⟨rv⟩ := r
  apply ext'
  show (UInt256.land ⟨cv⟩ ⟨rv⟩).val.val = rv.val
  rw [land_v]
  exact mask_keep _ _ _ hb h

/-- Canonical form of an operand list under a commutative, associative operator:
literals folded, operands sorted, duplicates dropped for idempotent operators. -/
def acBuild (f : BinK) (e c : UInt256) (rest : List Sym) : Sym :=
  if absorb f = some c then .lit c
  else build f e (if c = e
    then (if idem f then dedup (sortS rest) else sortS rest)
    else .lit c :: (if idem f then dedup (sortS rest) else sortS rest))

def acNorm (env : List Nat) (f : BinK) (e : UInt256) (l : List Sym) : Sym :=
  acBuild f e (if maskDrop env f (litFold f e l).1 (litFold f e l).2 then e else (litFold f e l).1)
    (litFold f e l).2

theorem acBuild_val {f e} (h : ACLaw (binF f) e) (base : List UInt256) (c : UInt256) (rest : List Sym) :
    (acBuild f e c rest).val base = binF f c (fv (binF f) e base rest) := by
  have hr : fv (binF f) e base (if idem f then dedup (sortS rest) else sortS rest) =
      fv (binF f) e base rest := by
    split
    · rw [dedup_val h (idem_law ‹_›), sortS_val h]
    · rw [sortS_val h]
  unfold acBuild
  split
  · rename_i ha; rw [absorb_law ha]; rfl
  · rw [build_val h]
    split
    · rename_i hc; rw [hr, hc, h.idl]
    · simp only [fv, List.foldr_cons, Sym.val] at hr ⊢; rw [hr]

theorem acNorm_val {f e} (h : ACLaw (binF f) e) (env : List Nat) (base : List UInt256)
    (hf : Fits env base) (l : List Sym) :
    (acNorm env f e l).val base = fv (binF f) e base l := by
  have lf := litFold_val h base l
  unfold acNorm
  rw [acBuild_val h]
  split
  · rename_i hm
    have hf : f = .and := by simp only [maskDrop, Bool.and_eq_true, beq_iff_eq] at hm; exact hm.1
    subst hf
    have he : e = ones := by
      have : UInt256.land e ones = e := by rw [land_comm']; exact land_idl e
      exact this.symm.trans (h.idl ones)
    subst he
    rw [← maskDrop_val env base hf _ _ hm, lf]
  · exact lf

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
def normOp (env : List Nat) (f : BinK) (a b : Sym) : Sym :=
  match f with
  | .sub => if a = b then .lit ⟨0⟩ else
      match b with
      | .lit c => acNorm env .add ⟨0⟩ (flat .add a ++ [.lit (UInt256.sub ⟨0⟩ c)])
      | _ => .bin .sub a b
  | .shl =>
      match a with
      | .lit k => if k.val.val < 256 then acNorm env .mul ⟨1⟩ (flat .mul b ++ [.lit (pow2 k)]) else .lit ⟨0⟩
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

def normBin (env : List Nat) (f : BinK) (a b : Sym) : Sym :=
  match ident f with
  | some e => acNorm env f e (flat f a ++ flat f b)
  | none =>
    match a, b with
    | .lit x, .lit y => if foldable f then .lit (binF f x y) else normOp env f a b
    | _, _ => normOp env f a b

def normUn (env : List Nat) (f : UnK) (a : Sym) : Sym :=
  match a with
  | .lit x => .lit (unF f x)
  | .un .iszero y => if f = .iszero ∧ y.bits env ≤ 1 then y else .un f a
  | _ => .un f a

theorem iszero_iszero (y : UInt256) (h : y.val.val < 2) : UInt256.isZero (UInt256.isZero y) = y := by
  obtain ⟨⟨n, hn⟩⟩ := y
  simp only at h
  rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> rfl

/-- Canonical form used to compare window results, given input bounds `env`. -/
def norm (env : List Nat) : Sym → Sym
  | .un f a => normUn env f (norm env a)
  | .bin f a b => normBin env f (norm env a) (norm env b)
  | s => s

theorem add_law : ACLaw (binF .add) ⟨0⟩ := ident_law rfl
theorem mul_law : ACLaw (binF .mul) ⟨1⟩ := ident_law rfl

theorem normOp_val (env : List Nat) (base : List UInt256) (hf : Fits env base) (f : BinK) (a b : Sym) :
    (normOp env f a b).val base = binF f (a.val base) (b.val base) := by
  unfold normOp
  split
  · split
    · subst_vars; simp only [Sym.val, binF, sub_self']
    · split
      · rename_i c _
        rw [acNorm_val add_law env base hf, fv_append add_law, flat_val add_law]
        simp only [fv, List.foldr_cons, List.foldr_nil, Sym.val, binF]
        rw [show UInt256.add (UInt256.sub ⟨0⟩ c) ⟨0⟩ = UInt256.sub ⟨0⟩ c from add_law.idr _, ← sub_add']
      · rfl
  · split
    · split
      · rw [acNorm_val mul_law env base hf, fv_append mul_law, flat_val mul_law]
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

theorem normBin_val (env : List Nat) (base : List UInt256) (hf : Fits env base) (f : BinK) (a b : Sym) :
    (normBin env f a b).val base = binF f (a.val base) (b.val base) := by
  unfold normBin
  split
  · rename_i e he
    have h := ident_law he
    rw [acNorm_val h env base hf, fv_append h, flat_val h, flat_val h]
  · split
    · split
      · rfl
      · exact normOp_val env base hf f _ _
    · exact normOp_val env base hf f a b

theorem normUn_val (env : List Nat) (base : List UInt256) (hf : Fits env base) (f : UnK) (a : Sym) :
    (normUn env f a).val base = unF f (a.val base) := by
  unfold normUn
  split
  · rfl
  · rename_i y
    split
    · rename_i h
      obtain ⟨rfl, hb⟩ := h
      have := bits_sound env base hf y
      exact (iszero_iszero _ (lt_of_lt_of_le this (pow_mono hb))).symm
    · rfl
  · rfl

theorem norm_val (env : List Nat) (base : List UInt256) (hf : Fits env base) :
    ∀ s : Sym, (norm env s).val base = s.val base
  | .input _ => rfl
  | .lit _ => rfl
  | .un f a => by simp only [norm, normUn_val env base hf, norm_val env base hf a, Sym.val]
  | .bin f a b => by
    simp only [norm, normBin_val env base hf, norm_val env base hf a, norm_val env base hf b, Sym.val]


#print axioms norm_val

end GolfWhole
