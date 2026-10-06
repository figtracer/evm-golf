import WholeXi
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition GolfXiEntry

/-! Lifting Ξ refinement to the message-call function Θ. -/
namespace GolfWhole

/-- The value transfer at the start of pinned Θ. -/
def transfer (σ : AccountMap .EVM) (s r : AccountAddress) (v : UInt256) : AccountMap .EVM :=
  let σ'₁ :=
    match σ.find? r with
      | none => if v != ⟨0⟩ then σ.insert r { (default : Account .EVM) with balance := v } else σ
      | some acc => σ.insert r { acc with balance := acc.balance + v }
  match σ'₁.find? s with
    | none => σ'₁
    | some acc => σ'₁.insert s { acc with balance := acc.balance - v }

/-- The execution environment built by pinned Θ for code `code`. -/
def thetaEnv (bvh : List ByteArray) (s o r : AccountAddress) (code : ByteArray)
    (p v' : UInt256) (d : ByteArray) (e : Nat) (H : BlockHeader) (w : Bool) : ExecutionEnv .EVM :=
  { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d, source := s,
    weiValue := v', depth := e, perm := w, code := code, header := H,
    blobVersionedHashes := bvh }

/-- Θ results, the candidate given gas `gC`: same created set, substate, status and output,
related account maps that keep the owner's code; the candidate keeps no less gas than the
original and no more than `gC`. -/
def ThetaRelated (owner : AccountAddress) (old new : ByteArray) (gC : UInt256)
    (q q' : Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate × Bool × ByteArray) :
    Prop :=
  q.1 = q'.1 ∧ MapsRelated owner old new q.2.1 q'.2.1 ∧
    (∃ a, q.2.1.find? owner = some a ∧ a.code = old) ∧ (∃ a, q'.2.1.find? owner = some a ∧ a.code = new) ∧
    q.2.2.1.toNat ≤ q'.2.2.1.toNat ∧ q'.2.2.1.toNat ≤ gC.toNat ∧
    q.2.2.2.1 = q'.2.2.2.1 ∧ q.2.2.2.2 = q'.2.2.2.2

theorem sub_toNat (a b : UInt256) (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat :=
  Fin.coe_sub_iff_le.mpr h

theorem add_toNat (a b : UInt256) (h : a.toNat + b.toNat < UInt256.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  show (a.val + b.val).val = _
  rw [Fin.val_add]; exact Nat.mod_eq_of_lt h

theorem div_toNat (a b : UInt256) : (a / b).toNat = a.toNat / b.toNat := rfl

theorem min_toNat (a b : UInt256) : (min a b).toNat = min a.toNat b.toNat := by
  show (if a ≤ b then a else b).toNat = _
  by_cases h : a ≤ b
  · rw [if_pos h]; exact (Nat.min_eq_left h).symm
  · rw [if_neg h]; exact (Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h))).symm

theorem maps_insert_at (owner k : AccountAddress) (old new : ByteArray) (m m' : AccountMap .EVM)
    (a a' : Account .EVM) (rel : MapsRelated owner old new m m')
    (h : AccountsRelated owner k old new a a') :
    MapsRelated owner old new (m.insert k a) (m'.insert k a') := by
  intro addr
  rw [Batteries.RBMap.find?_insert, Batteries.RBMap.find?_insert]
  by_cases e : compare addr k = .eq
  · rw [if_pos e, if_pos e]
    have : addr = k := compare_eq_iff_eq.mp e
    subst this
    exact h
  · rw [if_neg e, if_neg e]
    exact rel addr

theorem related_balance (owner k : AccountAddress) (old new : ByteArray) (a a' : Account .EVM)
    (f : UInt256 → UInt256) (h : AccountsRelated owner k old new a a') :
    AccountsRelated owner k old new { a with balance := f a.balance } { a' with balance := f a'.balance } := by
  obtain ⟨n, b, st, ts, c⟩ := h
  exact ⟨n, by simp only [b], st, ts, c⟩

theorem related_find {owner : AccountAddress} {old new : ByteArray} {m m' : AccountMap .EVM}
    (rel : MapsRelated owner old new m m') (k : AccountAddress) :
    (m.find? k = none ∧ m'.find? k = none) ∨
      ∃ a a', m.find? k = some a ∧ m'.find? k = some a' ∧ AccountsRelated owner k old new a a' := by
  have h := rel k
  cases e : m.find? k <;> cases e' : m'.find? k <;> rw [e, e'] at h
  · exact Or.inl ⟨rfl, rfl⟩
  · exact h.elim
  · exact h.elim
  · exact Or.inr ⟨_, _, rfl, rfl, h⟩

theorem owner_insert (owner k : AccountAddress) (code : ByteArray) (m : AccountMap .EVM)
    (a : Account .EVM) (h : ∃ x, m.find? owner = some x ∧ x.code = code)
    (keep : k = owner → a.code = code) :
    ∃ x, (m.insert k a).find? owner = some x ∧ x.code = code := by
  rw [Batteries.RBMap.find?_insert]
  by_cases e : compare owner k = .eq
  · rw [if_pos e]; exact ⟨a, rfl, keep (compare_eq_iff_eq.mp e).symm⟩
  · rw [if_neg e]; exact h

theorem transfer_related (owner : AccountAddress) (old new : ByteArray) (σ τ : AccountMap .EVM)
    (s r : AccountAddress) (v : UInt256) (rel : MapsRelated owner old new σ τ)
    (oldσ : ∃ a, σ.find? owner = some a ∧ a.code = old) :
    MapsRelated owner old new (transfer σ s r v) (transfer τ s r v) ∧
      ∃ a, (transfer σ s r v).find? owner = some a ∧ a.code = old := by
  have step1 : MapsRelated owner old new
      (match σ.find? r with
        | none => if v != ⟨0⟩ then σ.insert r { (default : Account .EVM) with balance := v } else σ
        | some acc => σ.insert r { acc with balance := acc.balance + v })
      (match τ.find? r with
        | none => if v != ⟨0⟩ then τ.insert r { (default : Account .EVM) with balance := v } else τ
        | some acc => τ.insert r { acc with balance := acc.balance + v }) ∧
      ∃ a, (match σ.find? r with
        | none => if v != ⟨0⟩ then σ.insert r { (default : Account .EVM) with balance := v } else σ
        | some acc => σ.insert r { acc with balance := acc.balance + v }).find? owner = some a ∧
        a.code = old := by
    rcases related_find rel r with ⟨e, e'⟩ | ⟨a, a', e, e', h⟩
    · rw [e, e']
      have ne : r ≠ owner := by
        intro hr; subst hr; obtain ⟨a, ha, -⟩ := oldσ; rw [e] at ha; cases ha
      by_cases hv : (v != ⟨0⟩) = true
      · simp only [if_pos hv]
        refine ⟨maps_insert_at owner r old new σ τ _ _ rel ?_, owner_insert owner r old σ _ oldσ (fun h => absurd h ne)⟩
        exact ⟨rfl, rfl, rfl, rfl, by rw [if_neg ne]⟩
      · simp only [if_neg hv]
        exact ⟨rel, oldσ⟩
    · rw [e, e']
      refine ⟨maps_insert_at owner r old new σ τ _ _ rel (related_balance _ _ _ _ _ _ (fun x => x + v) h), ?_⟩
      refine owner_insert owner r old σ _ oldσ (fun hr => ?_)
      subst hr
      obtain ⟨-, -, -, -, c⟩ := h
      rw [if_pos rfl] at c
      exact c.1
  obtain ⟨rel1, own1⟩ := step1
  unfold transfer
  simp only []
  generalize (match σ.find? r with
        | none => if v != ⟨0⟩ then σ.insert r { (default : Account .EVM) with balance := v } else σ
        | some acc => σ.insert r { acc with balance := acc.balance + v }) = σ1 at rel1 own1 ⊢
  generalize (match τ.find? r with
        | none => if v != ⟨0⟩ then τ.insert r { (default : Account .EVM) with balance := v } else τ
        | some acc => τ.insert r { acc with balance := acc.balance + v }) = τ1 at rel1 ⊢
  rcases related_find rel1 s with ⟨e, e'⟩ | ⟨a, a', e, e', h⟩
  · rw [e, e']; exact ⟨rel1, own1⟩
  · rw [e, e']
    refine ⟨maps_insert_at owner s old new σ1 τ1 _ _ rel1 (related_balance _ _ _ _ _ _ (fun x => x - v) h), ?_⟩
    refine owner_insert owner s old σ1 _ own1 (fun hs => ?_)
    subst hs
    obtain ⟨-, -, -, -, c⟩ := h
    rw [if_pos rfl] at c
    exact c.1

theorem transfer_linked (owner : AccountAddress) (code : ByteArray) (σ : AccountMap .EVM)
    (s r : AccountAddress) (v : UInt256) (h : ∃ a, σ.find? owner = some a ∧ a.code = code) :
    ∃ a, (transfer σ s r v).find? owner = some a ∧ a.code = code := by
  have rel : MapsRelated owner code code σ σ := by
    intro addr
    cases e : σ.find? addr with
    | none => trivial
    | some a => exact ⟨rfl, rfl, rfl, rfl, by split <;> simp_all⟩
  exact (transfer_related owner code code σ σ s r v rel h).2

theorem toList_nil_iff (m : AccountMap .EVM) : m.toList = [] ↔ ∀ k, m.find? k = none := by
  constructor
  · intro h k
    cases e : m.find? k with
    | none => rfl
    | some a =>
      obtain ⟨_, hm, _⟩ := Batteries.RBMap.find?_some_mem_toList e
      rw [h] at hm; cases hm
  · intro h
    cases e : m.toList with
    | nil => rfl
    | cons p l =>
      have mem : (p.1, p.2) ∈ m.toList := by rw [e]; exact List.mem_cons_self
      have : m.find? p.1 = some p.2 :=
        Batteries.RBMap.find?_some.mpr ⟨p.1, mem, compare_eq_iff_eq.mpr rfl⟩
      rw [h] at this; cases this

theorem beq_empty (m : AccountMap .EVM) : (m == ∅) = true ↔ m.toList = [] := by
  obtain ⟨t, wf⟩ := m
  change t.all₂ (· == ·) Batteries.RBNode.nil = true ↔ _
  unfold Batteries.RBNode.all₂
  rw [Batteries.RBNode.forM_eq_forM_toList]
  change _ ↔ t.toList = []
  cases t.toList with
  | nil => simp [List.forM, StateT.run, pure, StateT.pure, Batteries.RBNode.toStream]
  | cons x xs =>
    simp [List.forM, StateT.run, bind, StateT.bind, Batteries.RBNode.toStream,
      Batteries.RBNode.Stream.next?]

theorem related_empty {owner : AccountAddress} {old new : ByteArray} {m m' : AccountMap .EVM}
    (rel : MapsRelated owner old new m m') : (m == ∅) = (m' == ∅) := by
  have iff : (m == ∅) = true ↔ (m' == ∅) = true := by
    rw [beq_empty, beq_empty, toList_nil_iff, toList_nil_iff]
    constructor
    · intro h k; rcases related_find rel k with ⟨-, e⟩ | ⟨a, a', e, -, -⟩
      · exact e
      · rw [h k] at e; cases e
    · intro h k; rcases related_find rel k with ⟨e, -⟩ | ⟨a, a', -, e, -⟩
      · exact e
      · rw [h k] at e; cases e
  cases h1 : (m == ∅) <;> cases h2 : (m' == ∅) <;> simp_all

theorem toExecute_owner (σ : AccountMap .EVM) (owner : AccountAddress) (code : ByteArray)
    (notPre : owner ∉ π) (h : ∃ a, σ.find? owner = some a ∧ a.code = code) :
    toExecute .EVM σ owner = .Code code := by
  obtain ⟨a, ha, hc⟩ := h
  unfold toExecute
  rw [if_neg notPre]
  simp [ha, hc, Id.run]

/-- Θ on code: the value transfer, then Ξ, then the pinned result selection. -/
def thetaResult (created : Batteries.RBSet AccountAddress compare) (σ : AccountMap .EVM) (A : Substate)
    (x : Except EVM.ExecutionException
      (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate))) :
    Except EVM.ExecutionException
      (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate × Bool × ByteArray) :=
  match x with
  | .error e =>
    if e == .OutOfFuel then .error .OutOfFuel
    else .ok (created, if σ == ∅ then σ else σ, ⟨0⟩, if σ == ∅ then A else A, false, .empty)
  | .ok (.revert g' out) =>
    .ok (created, if σ == ∅ then σ else σ, g', if σ == ∅ then A else A, false, out)
  | .ok (.success (a, b, c, d) out) =>
    .ok (a, if b == ∅ then σ else b, c, if b == ∅ then A else d, true, out)

theorem theta_unfold (fuel : Nat) (bvh : List ByteArray)
    (created : Batteries.RBSet AccountAddress compare) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate) (s o r : AccountAddress)
    (code : ByteArray) (g p v v' : UInt256) (d : ByteArray) (e : Nat) (H : BlockHeader) (w : Bool) :
    Θ (fuel + 1) bvh created genesis blocks σ σ₀ A s o r (.Code code) g p v v' d e H w =
      thetaResult created σ A (Ξ fuel created genesis blocks (transfer σ s r v) σ₀ g A
          (thetaEnv bvh s o r code p v' d e H w)) := by
  rw [Θ.eq_13]
  split <;> rename_i heq <;>
    (have h2 : Ξ fuel created genesis blocks (transfer σ s r v) σ₀ g A
        (thetaEnv bvh s o r code p v' d e H w) = _ := heq
     rw [h2])
  · rename_i ex
    by_cases h : (ex == .OutOfFuel) = true <;>
      simp [thetaResult, h, bind, Except.bind, pure, Except.pure]
  · rfl
  · rfl

/-- Θ for a message call to the owner, with inner Ξ success or revert in the original:
the original's result, and the candidate's for every fuel at least the original's. -/
theorem theta_refines (owner : AccountAddress) (old new : ByteArray) (N : ℕ)
    (cert : Cert owner old new N) (fuel : Nat) (hN : fuel ≤ N) (bvh : List ByteArray)
    (created : Batteries.RBSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ τ τ₀ : AccountMap .EVM)
    (A : Substate) (s o : AccountAddress) (g gC : UInt256) (e : ℕ) (hg : gC.toNat = g.toNat + e)
    (p v v' : UInt256) (d : ByteArray) (depth : Nat) (H : BlockHeader) (w : Bool)
    (current : MapsRelated owner old new σ τ)
    (original : MapsRelated owner old new σ₀ τ₀)
    (oldCurrent : ∃ a, σ.find? owner = some a ∧ a.code = old)
    (oldOriginal : ∃ a, σ₀.find? owner = some a ∧ a.code = old)
    (newCurrent : ∃ a, τ.find? owner = some a ∧ a.code = new)
    (newOriginal : ∃ a, τ₀.find? owner = some a ∧ a.code = new)
    (R : ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate))
    (inner : Ξ fuel created genesis blocks (transfer σ s owner v) σ₀ g A
      (thetaEnv bvh s o owner old p v' d depth H w) = .ok R) :
    ∃ Q, Θ (fuel + 1) bvh created genesis blocks σ σ₀ A s o owner (.Code old) g p v v' d depth H w = .ok Q ∧
      ∀ fuel', fuel ≤ fuel' →
        ∃ Q', Θ (fuel' + 1) bvh created genesis blocks τ τ₀ A s o owner (.Code new) gC p v v' d depth H w = .ok Q' ∧
          ThetaRelated owner old new gC Q Q' := by
  obtain ⟨rel1, own1⟩ := transfer_related owner old new σ τ s owner v current oldCurrent
  have own1' := transfer_linked owner new τ s owner v newCurrent
  have envO : thetaEnv bvh s o owner old p v' d depth H w =
      { thetaEnv bvh s o owner old p v' d depth H w with codeOwner := owner, code := old } := rfl
  have envN : thetaEnv bvh s o owner new p v' d depth H w =
      { thetaEnv bvh s o owner old p v' d depth H w with codeOwner := owner, code := new } := rfl
  rw [envO] at inner
  have cand := xi_refines owner old new N cert fuel hN created genesis blocks
    (transfer σ s owner v) σ₀ (transfer τ s owner v) τ₀ g gC e hg A
    (thetaEnv bvh s o owner old p v' d depth H w)
    rel1 original own1 oldOriginal own1' newOriginal R inner
  rw [← envO] at inner
  have eO := theta_unfold fuel bvh created genesis blocks σ σ₀ A s o owner old g p v v' d depth H w
  rw [inner] at eO
  have eN : ∀ fuel', fuel ≤ fuel' → ∃ R',
      Θ (fuel' + 1) bvh created genesis blocks τ τ₀ A s o owner (.Code new) gC p v v' d depth H w =
        thetaResult created τ A (.ok R') ∧ XiRelated owner old new gC R R' := by
    intro fuel' hf
    obtain ⟨R', run', related⟩ := cand fuel' hf
    rw [← envN] at run'
    have e := theta_unfold fuel' bvh created genesis blocks τ τ₀ A s o owner new gC p v v' d depth H w
    rw [run'] at e
    exact ⟨R', e, related⟩
  cases R with
  | success q out =>
    obtain ⟨a, b, c, dd⟩ := q
    refine ⟨_, eO, fun fuel' hf => ?_⟩
    obtain ⟨R', e, related⟩ := eN fuel' hf
    cases R' with
    | success q' out' =>
      obtain ⟨a', b', c', dd'⟩ := q'
      obtain ⟨eo, ea, eA, hg, cap, hb, lo, ln⟩ := related
      subst eo ea eA
      refine ⟨_, e, rfl, ?_, ?_, ?_, hg, cap, ?_, rfl⟩
      · show MapsRelated owner old new (if b == ∅ then σ else b) (if b' == ∅ then τ else b')
        rw [related_empty hb]
        split
        · exact current
        · exact hb
      · show ∃ x, (if b == ∅ then σ else b).find? owner = some x ∧ x.code = old
        split
        · exact oldCurrent
        · exact lo
      · show ∃ x, (if b' == ∅ then τ else b').find? owner = some x ∧ x.code = new
        split
        · exact newCurrent
        · exact ln
      · show (if b == ∅ then A else dd) = (if b' == ∅ then A else dd)
        rw [related_empty hb]
    | revert _ _ => exact related.elim
  | revert gr out =>
    refine ⟨_, eO, fun fuel' hf => ?_⟩
    obtain ⟨R', e, related⟩ := eN fuel' hf
    cases R' with
    | success _ _ => exact related.elim
    | revert gr' out' =>
      obtain ⟨eo, hg, cap⟩ := related
      subst eo
      refine ⟨_, e, rfl, ?_, ?_, ?_, hg, cap, ?_, rfl⟩
      · show MapsRelated owner old new (if σ == ∅ then σ else σ) (if τ == ∅ then τ else τ)
        simp only [ite_self]; exact current
      · show ∃ x, (if σ == ∅ then σ else σ).find? owner = some x ∧ x.code = old
        simp only [ite_self]; exact oldCurrent
      · show ∃ x, (if τ == ∅ then τ else τ).find? owner = some x ∧ x.code = new
        simp only [ite_self]; exact newCurrent
      · show (if σ == ∅ then A else A) = (if τ == ∅ then A else A)
        simp only [ite_self]

#print axioms theta_refines

end GolfWhole
