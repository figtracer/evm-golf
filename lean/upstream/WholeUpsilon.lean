import WholeTheta
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition GolfXiEntry

/-! Lifting Θ refinement to the transaction function Υ for a message call to the owner. -/
namespace GolfWhole

/-- The priority fee of pinned Υ. -/
def txFee (H_f : ℕ) (T : Transaction) : UInt256 :=
  match T with
  | .legacy t | .access t => t.gasPrice - .ofNat H_f
  | .dynamic t | .blob t => min t.maxPriorityFeePerGas (t.maxFeePerGas - .ofNat H_f)

/-- The effective gas price of pinned Υ. -/
def txPrice (H_f : ℕ) (T : Transaction) : UInt256 :=
  match T with
  | .legacy t | .access t => t.gasPrice
  | .dynamic _ | .blob _ => txFee H_f T + .ofNat H_f

/-- The checkpoint state of pinned Υ: the sender is charged upfront and its nonce bumped. -/
def txCheckpoint (σ : AccountMap .EVM) (H_f : ℕ) (H : BlockHeader) (T : Transaction)
    (S_T : AccountAddress) : AccountMap .EVM :=
  σ.insert S_T { (σ.find? S_T).get! with
    balance := (σ.find? S_T).get!.balance - T.base.gasLimit * txPrice H_f T - .ofNat (calcBlobFee H T)
    nonce := (σ.find? S_T).get!.nonce + ⟨1⟩ }

/-- The initial substate of pinned Υ for a message call to `t`. -/
def txSubstate (H : BlockHeader) (T : Transaction) (S_T t : AccountAddress) : Substate :=
  { A0 with
    accessedAccounts :=
      ((A0.accessedAccounts.insert S_T |>.insert H.beneficiary).union
        (Batteries.RBSet.ofList (T.getAccessList.map Prod.fst) compare)).insert t
    accessedStorageKeys := Batteries.RBSet.ofList
      (do let ⟨Eₐ, Eₛ⟩ ← T.getAccessList; let eₛ ← Eₛ.toList; pure (Eₐ, eₛ))
      Substate.storageKeysCmp }

def txGas (T : Transaction) : UInt256 := .ofNat (T.base.gasLimit.toNat - intrinsicGas T)

/-- Refund, fee payment, deletions and transient-storage clearing of pinned Υ, from the
provisional state and remaining gas. Returns the final state and the gas used. -/
def finalize (σ_P : AccountMap .EVM) (g' : UInt256) (A : Substate) (H_f : ℕ) (H : BlockHeader)
    (T : Transaction) (S_T : AccountAddress) : AccountMap .EVM × UInt256 :=
  let gStar := g' + min ((T.base.gasLimit - g') / ⟨5⟩) A.refundBalance
  let σStar := σ_P.increaseBalance .EVM S_T (gStar * txPrice H_f T)
  let beneficiaryFee := (T.base.gasLimit - gStar) * txFee H_f T
  let σStar' :=
    if beneficiaryFee != ⟨0⟩ then σStar.increaseBalance .EVM H.beneficiary beneficiaryFee else σStar
  let σ' := A.selfDestructSet.1.foldl Batteries.RBMap.erase σStar'
  let deadAccounts := A.touchedAccounts.filter (State.dead σStar' ·)
  let σ' := deadAccounts.foldl Batteries.RBMap.erase σ'
  let σ' := σ'.map λ (addr, acc) ↦ (addr, { acc with tstorage := .empty })
  (σ', T.base.gasLimit - gStar)

theorem upsilon_unfold (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ) (H genesis : BlockHeader)
    (blocks : ProcessedBlocks) (T : Transaction) (S_T t : AccountAddress)
    (hr : T.base.recipient = some t) :
    Υ fuel σ H_f H genesis blocks T S_T =
      match Θ fuel T.blobVersionedHashes .empty genesis blocks (txCheckpoint σ H_f H T S_T)
          (txCheckpoint σ H_f H T S_T) (txSubstate H T S_T t) S_T S_T t
          (toExecute .EVM (txCheckpoint σ H_f H T S_T) t) (txGas T) (txPrice H_f T)
          T.base.value T.base.value T.base.data 0 H true with
      | .ok (_, σ_P, g', A, z, _) =>
        .ok ((finalize σ_P g' A H_f H T S_T).1, A, z, (finalize σ_P g' A H_f H T S_T).2)
      | .error e => .error (.ExecutionException e) := by
  unfold Υ
  simp only [hr]
  split <;> rename_i heq <;>
    (have h2 : Θ fuel T.blobVersionedHashes .empty genesis blocks (txCheckpoint σ H_f H T S_T)
          (txCheckpoint σ H_f H T S_T) (txSubstate H T S_T t) S_T S_T t
          (toExecute .EVM (txCheckpoint σ H_f H T S_T) t) (txGas T) (txPrice H_f T)
          T.base.value T.base.value T.base.data 0 H true = _ := heq
     rw [h2]) <;> rfl

/-- Charged gas `L - (g + min ((L - g) / 5) R)` does not increase with the remaining gas. -/
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

theorem refund_toNat (L R g : UInt256) (h : g.toNat ≤ L.toNat) :
    (g + min ((L - g) / ⟨5⟩) R).toNat = g.toNat + min ((L.toNat - g.toNat) / 5) R.toNat ∧
      g.toNat + min ((L.toNat - g.toNat) / 5) R.toNat ≤ L.toNat := by
  have hm : (min ((L - g) / ⟨5⟩) R).toNat = min ((L.toNat - g.toNat) / 5) R.toNat := by
    rw [min_toNat, div_toNat, sub_toNat _ _ h]; rfl
  have le : g.toNat + min ((L.toNat - g.toNat) / 5) R.toNat ≤ L.toNat := by
    have := Nat.min_le_left ((L.toNat - g.toNat) / 5) R.toNat
    have := Nat.div_le_self (L.toNat - g.toNat) 5
    omega
  refine ⟨?_, le⟩
  rw [add_toNat _ _ (by rw [hm]; exact lt_of_le_of_lt le L.val.isLt), hm]

theorem charged_mono (L R gO gN : UInt256) (hO : gO.toNat ≤ gN.toNat) (hN : gN.toNat ≤ L.toNat) :
    (L - (gN + min ((L - gN) / ⟨5⟩) R)).toNat ≤ (L - (gO + min ((L - gO) / ⟨5⟩) R)).toNat := by
  obtain ⟨eN, leN⟩ := refund_toNat L R gN hN
  obtain ⟨eO, leO⟩ := refund_toNat L R gO (le_trans hO hN)
  rw [sub_toNat _ _ (by rw [eN]; exact leN), sub_toNat _ _ (by rw [eO]; exact leO), eN, eO]
  have key : (L.toNat - gO.toNat) / 5 ≤ (L.toNat - gN.toNat) / 5 + (gN.toNat - gO.toNat) := by
    have : L.toNat - gO.toNat = (L.toNat - gN.toNat) + (gN.toNat - gO.toNat) := by omega
    rw [this]; omega
  have : min ((L.toNat - gO.toNat) / 5) R.toNat ≤ min ((L.toNat - gN.toNat) / 5) R.toNat + (gN.toNat - gO.toNat) := by
    rcases Nat.le_total ((L.toNat - gO.toNat) / 5) R.toNat with h | h <;>
      rcases Nat.le_total ((L.toNat - gN.toNat) / 5) R.toNat with h' | h' <;>
      simp only [Nat.min_eq_left, Nat.min_eq_right, h, h'] <;> omega
  omega

theorem checkpoint_related (owner : AccountAddress) (old new : ByteArray) (σ τ : AccountMap .EVM)
    (H_f : ℕ) (H : BlockHeader) (T : Transaction) (S_T : AccountAddress)
    (rel : MapsRelated owner old new σ τ) (oldσ : ∃ a, σ.find? owner = some a ∧ a.code = old) :
    MapsRelated owner old new (txCheckpoint σ H_f H T S_T) (txCheckpoint τ H_f H T S_T) ∧
      ∃ a, (txCheckpoint σ H_f H T S_T).find? owner = some a ∧ a.code = old := by
  unfold txCheckpoint
  rcases related_find rel S_T with ⟨e, e'⟩ | ⟨a, a', e, e', h⟩
  · rw [e, e']
    have ne : S_T ≠ owner := by
      intro hs; subst hs; obtain ⟨a, ha, -⟩ := oldσ; rw [e] at ha; cases ha
    refine ⟨maps_insert_at owner S_T old new σ τ _ _ rel ⟨rfl, rfl, rfl, rfl, by rw [if_neg ne]⟩,
      owner_insert owner S_T old σ _ oldσ (fun h => absurd h ne)⟩
  · rw [e, e']
    obtain ⟨n, b, st, ts, c⟩ := h
    refine ⟨maps_insert_at owner S_T old new σ τ _ _ rel ⟨by simp only [Option.get!_some, n],
      by simp only [Option.get!_some, b], st, ts, c⟩, ?_⟩
    refine owner_insert owner S_T old σ _ oldσ (fun hs => ?_)
    subst hs
    rw [if_pos rfl] at c
    exact c.1

theorem linked_checkpoint (owner : AccountAddress) (code : ByteArray) (σ : AccountMap .EVM)
    (H_f : ℕ) (H : BlockHeader) (T : Transaction) (S_T : AccountAddress)
    (h : ∃ a, σ.find? owner = some a ∧ a.code = code) :
    ∃ a, (txCheckpoint σ H_f H T S_T).find? owner = some a ∧ a.code = code := by
  have rel : MapsRelated owner code code σ σ := by
    intro addr
    cases e : σ.find? addr with
    | none => trivial
    | some a => exact ⟨rfl, rfl, rfl, rfl, by split <;> simp_all⟩
  exact (checkpoint_related owner code code σ σ H_f H T S_T rel h).2

theorem toExecute_owner (σ : AccountMap .EVM) (owner : AccountAddress) (code : ByteArray)
    (notPre : owner ∉ π) (h : ∃ a, σ.find? owner = some a ∧ a.code = code) :
    toExecute .EVM σ owner = .Code code := by
  obtain ⟨a, ha, hc⟩ := h
  unfold toExecute
  rw [if_neg notPre]
  simp [ha, hc, Id.run]

/-- Υ for a message-call transaction to the owner, when the original's inner Ξ returns
success or revert: both runs finalize related provisional states with the same substate
and status, and the candidate has at least as much remaining gas. -/
theorem upsilon_refines (owner : AccountAddress) (old new : ByteArray)
    (cert : ∀ (fuel : ℕ) (s t : State) (surplus skipped : ℕ) (r : ExecutionResult State),
      DeployedOffset owner old new surplus skipped s t → s.pc = UInt256.ofNat 0 →
      X fuel (D_J old (UInt256.ofNat 0)) s = .ok r →
      ∃ f r', X f (D_J new (UInt256.ofNat 0)) t = .ok r' ∧ OutcomeRelated owner old new r r')
    (fuel : ℕ) (σ τ : AccountMap .EVM) (H_f : ℕ) (H genesis : BlockHeader)
    (blocks : ProcessedBlocks) (T : Transaction) (S_T : AccountAddress)
    (rel : MapsRelated owner old new σ τ)
    (oldσ : ∃ a, σ.find? owner = some a ∧ a.code = old)
    (newτ : ∃ a, τ.find? owner = some a ∧ a.code = new)
    (hr : T.base.recipient = some owner) (notPre : owner ∉ π)
    (R : ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate))
    (inner : Ξ fuel .empty genesis blocks
      (transfer (txCheckpoint σ H_f H T S_T) S_T owner T.base.value) (txCheckpoint σ H_f H T S_T)
      (txGas T) (txSubstate H T S_T owner)
      (thetaEnv T.blobVersionedHashes S_T S_T owner old (txPrice H_f T) T.base.value T.base.data 0 H true) =
        .ok R) :
    ∃ f σP σP' g g' A z, MapsRelated owner old new σP σP' ∧ g.toNat ≤ g'.toNat ∧
      Υ (fuel + 1) σ H_f H genesis blocks T S_T =
        .ok ((finalize σP g A H_f H T S_T).1, A, z, (finalize σP g A H_f H T S_T).2) ∧
      Υ f τ H_f H genesis blocks T S_T =
        .ok ((finalize σP' g' A H_f H T S_T).1, A, z, (finalize σP' g' A H_f H T S_T).2) := by
  obtain ⟨crel, cown⟩ := checkpoint_related owner old new σ τ H_f H T S_T rel oldσ
  have cown' := linked_checkpoint owner new τ H_f H T S_T newτ
  obtain ⟨f, Q, Q', runO, runN, ec, hm, hg, eA, ez⟩ := theta_refines owner old new cert fuel
    T.blobVersionedHashes .empty genesis blocks _ _ _ _ (txSubstate H T S_T owner) S_T S_T (txGas T)
    (txPrice H_f T) T.base.value T.base.value T.base.data 0 H true crel crel cown cown cown' cown' R inner
  refine ⟨f, Q.2.1, Q'.2.1, Q.2.2.1, Q'.2.2.1, Q.2.2.2.1, Q.2.2.2.2.1, hm, hg, ?_, ?_⟩
  · rw [upsilon_unfold _ _ _ _ _ _ _ _ _ hr, toExecute_owner _ _ _ notPre cown, runO]
  · rw [upsilon_unfold _ _ _ _ _ _ _ _ _ hr, toExecute_owner _ _ _ notPre cown', runN, eA,
      show Q.2.2.2.2.1 = Q'.2.2.2.2.1 from congrArg Prod.fst ez]

#print axioms upsilon_refines
#print axioms charged_mono

end GolfWhole
