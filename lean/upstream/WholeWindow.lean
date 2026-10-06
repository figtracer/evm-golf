import WholeWFacts
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition

/-! Straight-line windows evaluated on a symbolic stack. -/
namespace GolfWhole

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


/-- Decidable window equivalence: the candidate needs no deeper stack, ends with
the same stack, costs no more gas, runs no more instructions and never grows
the stack above some height the original reaches. `env` bounds the bit length of
the entry stack slots. -/
def windowCheck (env : List Nat) (opsO opsN : List WOp) : Bool :=
  decide ((srun opsN ([], 0)).2 ≤ (srun opsO ([], 0)).2) &&
  decide (((srun opsN ([], 0)).1 ++ pulls (srun opsN ([], 0)).2
    ((srun opsO ([], 0)).2 - (srun opsN ([], 0)).2)).map (norm env) = (srun opsO ([], 0)).1.map (norm env)) &&
  decide (scost opsN ≤ scost opsO) && decide (opsN.length ≤ opsO.length) &&
  decide (0 < opsO.length) &&
  (sheights opsN ([], 0)).all (fun h => (sheights opsO ([], 0)).any (fun h' => decide (h ≤ h')))

theorem window_segment (owner : AccountAddress) (old new : ByteArray) (oj nj : Array UInt256)
    (Q : UInt256 → List UInt256 → Prop) (A : List UInt256 → Prop) (pc e : UInt256)
    (opsO opsN : List WOp) (env : List Nat)
    (wo : WCode old pc opsO e) (wn : WCode new pc opsN e) (check : windowCheck env opsO opsN = true)
    (fits : ∀ st, A st → Fits env st)
    (next : ∀ st, A st →
      Q e ((srun opsO ([], 0)).1.map (Sym.val st) ++ st.drop (srun opsO ([], 0)).2)) :
    Segment owner old new oj nj Q A pc := by
  intro fuel s t surplus skipped r rel hpc hA ok
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
    opsN.length, by omega, finO, next _ hA, ?_, fun g => cand g⟩
  have hstk : (srun opsO ([], 0)).1.map (Sym.val s.stack) ++ s.stack.drop (srun opsO ([], 0)).2 =
      (srun opsN ([], 0)).1.map (Sym.val s.stack) ++ s.stack.drop (srun opsN ([], 0)).2 := by
    have hd : s.stack.drop (srun opsO ([], 0)).2 = s.stack.drop ((srun opsN ([], 0)).2 +
        ((srun opsO ([], 0)).2 - (srun opsN ([], 0)).2)) := by congr 1; omega
    have vals : ∀ l : List Sym, l.map (Sym.val s.stack) = (l.map (norm env)).map (Sym.val s.stack) := by
      intro l; rw [List.map_map]; congr 1; funext x; exact (norm_val env _ (fits _ hA) x).symm
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
