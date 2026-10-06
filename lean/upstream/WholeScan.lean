import EvmYul.EVM.Semantics
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
open EvmYul EvmYul.EVM

/-! A natural-number jump-table scanner, proved equal to the checked `D_J`. -/
namespace GolfWhole

def width (b : Nat) : Nat := if 96 ≤ b ∧ b ≤ 127 then b - 95 else 0

theorem parse_table : ∀ b : Fin 256,
    ((parseInstr (UInt8.ofNat b.val)).map argOnNBytesOfInstr = some (width b.val)) ∧
    ((parseInstr (UInt8.ofNat b.val) = some .JUMPDEST) = (b.val = 91)) := by
  decide +kernel


def ofBytes (l : List Nat) : ByteArray := ⟨(l.map UInt8.ofNat).toArray⟩

/-- Structural scan: `skip` immediate bytes remain before the next opcode. -/
def scanL : List Nat → Nat → Nat → Array UInt256 → Array UInt256
  | [], _, _, acc => acc
  | b :: rest, 0, pc, acc =>
    scanL rest (width b) (pc + 1) (if b = 91 then acc.push (UInt256.ofNat pc) else acc)
  | _ :: rest, k + 1, pc, acc => scanL rest k (pc + 1) acc

theorem scan_skip : ∀ (w : Nat) (rest : List Nat) (pc : Nat) (acc : Array UInt256),
    scanL rest w pc acc = scanL (rest.drop w) 0 (pc + w) acc := by
  intro w
  induction w with
  | zero => intro rest pc acc; rfl
  | succ w ih =>
    intro rest pc acc
    cases rest with
    | nil => simp [scanL]
    | cons x xs =>
      simp only [scanL, List.drop_succ_cons]
      rw [ih]
      congr 1
      omega

theorem get_ofBytes (l : List Nat) (i : Nat) :
    (ofBytes l).get? i = (l[i]?).map UInt8.ofNat := by
  unfold ofBytes
  simp [ByteArray.get?, ByteArray.size, ByteArray.get, getElem?_def]

theorem drop_cons_index {l : List Nat} {i b rest} (h : l.drop i = b :: rest) : l[i]? = some b := by
  have := congrArg List.head? h
  rw [List.head?_drop] at this
  exact this

theorem drop_succ_drop {l : List Nat} {i b rest} (h : l.drop i = b :: rest) (w : Nat) :
    l.drop (i + 1 + w) = rest.drop w := by
  rw [Nat.add_assoc, ← List.drop_drop, h, Nat.add_comm 1 w]
  rfl

theorem checked_scan (l : List Nat) (bytes : ∀ b ∈ l, b < 256) :
    ∀ (n : Nat) (pc : Nat) (acc : Array UInt256), (l.drop pc).length < n →
      D_J_checked n (ofBytes l) pc acc = some (scanL (l.drop pc) 0 pc acc) := by
  intro n
  induction n with
  | zero => intro pc acc h; omega
  | succ n ih =>
    intro pc acc h
    cases e : l.drop pc with
    | nil =>
      have : l[pc]? = none := by
        rw [List.getElem?_eq_none_iff]
        have := congrArg List.length e
        simp at this; omega
      simp [D_J_checked, get_ofBytes, this, scanL]
    | cons b rest =>
      have hb : b < 256 := bytes b (List.mem_of_getElem? (drop_cons_index e))
      obtain ⟨t1, t2⟩ := parse_table ⟨b, hb⟩
      simp only at t1 t2
      cases p : parseInstr (UInt8.ofNat b) with
      | none => simp [p] at t1
      | some op =>
        simp only [p, Option.map_some, Option.some.injEq] at t1 t2
        have next := drop_succ_drop e (width b)
        have lt : (l.drop (pc + 1 + width b)).length < n := by
          rw [next]; rw [e] at h; simp at h ⊢; omega
        rw [D_J_checked, get_ofBytes, drop_cons_index e]
        simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, p]
        rw [t1, ih _ _ lt, next]
        simp only [scanL]
        rw [scan_skip (width b) rest]
        by_cases j : b = 91
        · have : op = .JUMPDEST := by rw [t2]; exact j
          simp [this, j]
        · have : op ≠ .JUMPDEST := fun e => j (by rw [←t2]; exact e)
          simp [this, j]

theorem dj_scan (l : List Nat) (bytes : ∀ b ∈ l, b < 256) (small : l.length + 32 < UInt256.size) :
    D_J (ofBytes l) (UInt256.ofNat 0) = scanL l 0 0 #[] := by
  have size : (ofBytes l).size = l.length := by simp [ofBytes, ByteArray.size]
  have zero : (UInt256.ofNat 0).toNat = 0 := rfl
  unfold D_J
  rw [if_pos (by rw [size]; exact small), zero, checked_scan l bytes _ 0 #[] (by simp [size])]
  simp

/-- Decoding on a byte list; equal to `decode` on the encoded image. -/
def decodeL : List Nat → Option (Operation .EVM × Option (UInt256 × Nat))
  | [] => none
  | b :: rest => (parseInstr (UInt8.ofNat b)).map fun op =>
    (op, if argOnNBytesOfInstr op == 0 then none
      else some (uInt256OfByteArray (ofBytes (rest.take (argOnNBytesOfInstr op))), argOnNBytesOfInstr op))

theorem extract_data (a : ByteArray) (start stop : Nat)
    (ordered : start ≤ stop) (small : stop < 2^64) :
    (a.extract' start stop).data = a.data.extract start stop := by
  have smallStart : start < 2^64 := by omega
  change start < 18446744073709551616 at smallStart
  change stop < 18446744073709551616 at small
  simp [ByteArray.extract', smallStart, small, ByteArray.extract, ByteArray.copySlice,
    ByteArray.empty, Nat.add_sub_of_le ordered]

theorem word_of_list (x y : ByteArray) (h : x.data.toList = y.data.toList) :
    uInt256OfByteArray x = uInt256OfByteArray y := by
  unfold uInt256OfByteArray; rw [h]

theorem decode_ofBytes (l : List Nat) (pc : Nat) (small : pc + 40 < 2^64) :
    decode (ofBytes l) (UInt256.ofNat pc) = decodeL (l.drop pc) := by
  have hpc : (UInt256.ofNat pc).toNat = pc := by
    change pc % UInt256.size = pc
    exact Nat.mod_eq_of_lt (by unfold UInt256.size; omega)
  unfold decode
  rw [hpc, get_ofBytes]
  cases e : l.drop pc with
  | nil =>
    have : l[pc]? = none := by
      rw [List.getElem?_eq_none_iff]
      have := congrArg List.length e
      simp at this; omega
    simp [this, decodeL]
  | cons b rest =>
    rw [drop_cons_index e]
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, decodeL]
    cases p : parseInstr (UInt8.ofNat b) with
    | none => simp
    | some op =>
      simp only [Option.bind_some, Option.map_some]
      have w : argOnNBytesOfInstr op ≤ 32 := by
        unfold argOnNBytesOfInstr; split <;> omega
      have d : l.drop (pc + 1) = rest := by
        rw [← List.drop_drop, e]; rfl
      have v : uInt256OfByteArray ((ofBytes l).extract' pc.succ (pc.succ + argOnNBytesOfInstr op)) =
          uInt256OfByteArray (ofBytes (rest.take (argOnNBytesOfInstr op))) := by
        apply word_of_list
        rw [extract_data _ _ _ (by omega) (by omega)]
        simp only [Array.toList_extract, ofBytes, List.extract, List.toList_toArray]
        rw [show pc.succ + argOnNBytesOfInstr op - pc.succ = argOnNBytesOfInstr op by omega,
          ← List.map_drop, Nat.succ_eq_add_one, d, List.map_take]
      rw [v]

theorem decode_fact (l : List Nat) (pc : Nat) {x : Operation .EVM × Option (UInt256 × Nat)}
    (small : pc + 40 < 2^64) (h : decodeL (l.drop pc) = some x) :
    decode (ofBytes l) (UInt256.ofNat pc) = some x := by
  rw [decode_ofBytes l pc small, h]

theorem decode_getD (l : List Nat) (pc : Nat) {x : Operation .EVM × Option (UInt256 × Nat)}
    (small : pc + 40 < 2^64) (h : (decodeL (l.drop pc)).getD (.STOP, .none) = x) :
    (decode (ofBytes l) (UInt256.ofNat pc)).getD (.STOP, .none) = x := by
  rw [decode_ofBytes l pc small, h]

theorem decode_fact' (l : List Nat) (n : Nat) {p : UInt256} {x : Operation .EVM × Option (UInt256 × Nat)}
    (hp : p = UInt256.ofNat n) (small : n + 40 < 2^64) (h : decodeL (l.drop n) = some x) :
    decode (ofBytes l) p = some x := by
  rw [hp]; exact decode_fact l n small h

theorem tail_drop {l t : List Nat} {k pc : Nat} (hk : l.drop k = t) (hle : k ≤ pc) :
    l.drop pc = t.drop (pc - k) := by
  rw [← hk, List.drop_drop]; congr 1; omega

theorem decode_tail (l t : List Nat) (k pc : Nat) {x : Operation .EVM × Option (UInt256 × Nat)}
    (hk : l.drop k = t) (hle : k ≤ pc) (small : pc + 40 < 2^64)
    (h : decodeL (t.drop (pc - k)) = some x) : decode (ofBytes l) (UInt256.ofNat pc) = some x := by
  rw [decode_ofBytes l pc small, tail_drop hk hle, h]

theorem decode_tail' (l t : List Nat) (k n : Nat) {p : UInt256}
    {x : Operation .EVM × Option (UInt256 × Nat)} (hp : p = UInt256.ofNat n)
    (hk : l.drop k = t) (hle : k ≤ n) (small : n + 40 < 2^64)
    (h : decodeL (t.drop (n - k)) = some x) : decode (ofBytes l) p = some x := by
  rw [hp]; exact decode_tail l t k n hk hle small h

theorem decode_tail_getD (l t : List Nat) (k pc : Nat) {x : Operation .EVM × Option (UInt256 × Nat)}
    (hk : l.drop k = t) (hle : k ≤ pc) (small : pc + 40 < 2^64)
    (h : (decodeL (t.drop (pc - k))).getD (.STOP, .none) = x) :
    (decode (ofBytes l) (UInt256.ofNat pc)).getD (.STOP, .none) = x := by
  rw [decode_ofBytes l pc small, tail_drop hk hle, h]

theorem drop_step {l t c rest : List Nat} {k n : Nat} (hk : l.drop k = t) (ht : t = c ++ rest)
    (hc : c.length = n) : l.drop (k + n) = rest := by
  rw [← List.drop_drop, hk, ht, List.drop_left' hc]

/-- The scanner state after a byte block, so a long scan can be checked per block. -/
def scanS : List Nat → Nat → Nat → Array UInt256 → Nat × Nat × Array UInt256
  | [], k, pc, acc => (k, pc, acc)
  | b :: rest, 0, pc, acc =>
    scanS rest (width b) (pc + 1) (if b = 91 then acc.push (UInt256.ofNat pc) else acc)
  | _ :: rest, k + 1, pc, acc => scanS rest k (pc + 1) acc

theorem scanL_append : ∀ (a b : List Nat) (k pc : Nat) (acc : Array UInt256),
    scanL (a ++ b) k pc acc = scanL b (scanS a k pc acc).1 (scanS a k pc acc).2.1 (scanS a k pc acc).2.2
  | [], _, _, _, _ => rfl
  | x :: xs, b, 0, pc, acc => by simp only [List.cons_append, scanL, scanS]; exact scanL_append xs b _ _ _
  | x :: xs, b, k + 1, pc, acc => by simp only [List.cons_append, scanL, scanS]; exact scanL_append xs b _ _ _

theorem scan_block {c rest : List Nat} {k pc k' pc' : Nat} {acc acc' r : Array UInt256}
    (h : scanS c k pc acc = (k', pc', acc')) (next : scanL rest k' pc' acc' = r) :
    scanL (c ++ rest) k pc acc = r := by
  rw [scanL_append, h]; exact next

theorem scan_last {c : List Nat} {k pc k' pc' : Nat} {acc acc' : Array UInt256}
    (h : scanS c k pc acc = (k', pc', acc')) : scanL c k pc acc = acc' := by
  have := scanL_append c [] k pc acc
  rw [List.append_nil] at this
  rw [this, h]; rfl

theorem scanS_acc : ∀ (c : List Nat) (k pc : Nat) (acc : Array UInt256),
    scanS c k pc acc = ((scanS c k pc #[]).1, (scanS c k pc #[]).2.1, acc ++ (scanS c k pc #[]).2.2)
  | [], k, pc, acc => by simp [scanS]
  | b :: rest, 0, pc, acc => by
    simp only [scanS]
    rw [scanS_acc rest _ _ (if b = 91 then acc.push _ else acc),
      scanS_acc rest _ _ (if b = 91 then (#[] : Array UInt256).push _ else #[])]
    split <;> simp [Array.append_assoc]
  | _ :: rest, k + 1, pc, acc => by
    simp only [scanS]; exact scanS_acc rest k (pc + 1) acc

theorem scan_block' {c rest : List Nat} {k pc k' pc' : Nat} {acc loc acc' r : Array UInt256}
    (h : scanS c k pc #[] = (k', pc', loc)) (hacc : (acc ++ loc).toList = acc'.toList)
    (next : scanL rest k' pc' acc' = r) : scanL (c ++ rest) k pc acc = r := by
  rw [scanL_append, scanS_acc, h]; rw [← Array.toList_inj.mp hacc] at next; exact next

theorem scan_last' {c : List Nat} {k pc k' pc' : Nat} {acc loc acc' : Array UInt256}
    (h : scanS c k pc #[] = (k', pc', loc)) (hacc : (acc ++ loc).toList = acc'.toList) :
    scanL c k pc acc = acc' := by
  have := scanL_append c [] k pc acc
  rw [List.append_nil] at this
  rw [this, scanS_acc, h, ← Array.toList_inj.mp hacc]; rfl

theorem bound_append {a b : List Nat} (ha : ∀ x ∈ a, x < 256) (hb : ∀ x ∈ b, x < 256) :
    ∀ x ∈ a ++ b, x < 256 := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · exact hb x h

theorem length_block {a b : List Nat} {m n : Nat} (ha : a.length = m) (hb : b.length = n) :
    (a ++ b).length = m + n := by
  rw [List.length_append, ha, hb]

#print axioms dj_scan
#print axioms decode_ofBytes

end GolfWhole
