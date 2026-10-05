/-! Jump threading in a bounded control-flow model. A PUSH of trampoline X
before JUMP or JUMPI becomes a PUSH of Y, where X holds `JUMPDEST; PUSH Y; JUMP`.
Gas is erased; every other instruction is outside this model. -/
namespace GolfThread

/-- Big-endian value of a PUSH immediate. -/
def immediate (bytes : List Nat) : Nat := bytes.foldl (fun value byte => value * 256 + byte) 0

inductive Outcome where
  | running (pc : Nat) (stack : List Nat)
  | overflow
  | underflow
  | invalidJump
  | unsupported
  deriving DecidableEq

/-- One PUSH, JUMPDEST, JUMP or JUMPI step; `dests` are the valid destinations. -/
def step (code dests : List Nat) (pc : Nat) (stack : List Nat) : Outcome :=
  match code[pc]? with
  | none => .unsupported
  | some op =>
    if 95 ≤ op ∧ op ≤ 127 then
      if 1024 ≤ stack.length then .overflow
      else .running (pc + 1 + (op - 95)) (immediate ((code.drop (pc + 1)).take (op - 95)) :: stack)
    else if op = 91 then .running (pc + 1) stack
    else if op = 86 then
      match stack with
      | d :: rest => if dests.contains d then .running d rest else .invalidJump
      | [] => .underflow
    else if op = 87 then
      match stack with
      | d :: c :: rest =>
        if c = 0 then .running (pc + 1) rest
        else if dests.contains d then .running d rest else .invalidJump
      | _ => .underflow
    else .unsupported

def run (code dests : List Nat) : Nat → Outcome → Outcome
  | 0, outcome => outcome
  | n + 1, .running pc stack => run code dests n (step code dests pc stack)
  | _ + 1, outcome => outcome

theorem run_running (code dests : List Nat) (n pc : Nat) (stack : List Nat) :
    run code dests (n + 1) (.running pc stack) = run code dests n (step code dests pc stack) := rfl

theorem run_zero (code dests : List Nat) (outcome : Outcome) : run code dests 0 outcome = outcome := rfl

theorem run_overflow (code dests : List Nat) (n : Nat) : run code dests n .overflow = .overflow := by
  cases n <;> rfl

theorem run_underflow (code dests : List Nat) (n : Nat) : run code dests n .underflow = .underflow := by
  cases n <;> rfl

theorem step_push {code dests stack : List Nat} {pc w : Nat} (h : code[pc]? = some (95 + w))
    (wb : w ≤ 32) (room : stack.length < 1024) :
    step code dests pc stack =
      .running (pc + 1 + w) (immediate ((code.drop (pc + 1)).take w) :: stack) := by
  have range : 95 ≤ 95 + w ∧ 95 + w ≤ 127 := by omega
  have full : ¬ 1024 ≤ stack.length := by omega
  simp [step, h, range, full]

theorem step_push_full {code dests stack : List Nat} {pc w : Nat} (h : code[pc]? = some (95 + w))
    (wb : w ≤ 32) (full : 1024 ≤ stack.length) : step code dests pc stack = .overflow := by
  have range : 95 ≤ 95 + w ∧ 95 + w ≤ 127 := by omega
  simp [step, h, range, full]

theorem step_jumpdest {code dests stack : List Nat} {pc : Nat} (h : code[pc]? = some 91) :
    step code dests pc stack = .running (pc + 1) stack := by
  simp [step, h]

theorem step_jump {code dests rest : List Nat} {pc d : Nat} (h : code[pc]? = some 86)
    (valid : dests.contains d = true) : step code dests pc (d :: rest) = .running d rest := by
  simp [step, h] at valid ⊢
  simp [valid]

theorem step_jumpi_taken {code dests rest : List Nat} {pc d c : Nat} (h : code[pc]? = some 87)
    (nonzero : c ≠ 0) (valid : dests.contains d = true) :
    step code dests pc (d :: c :: rest) = .running d rest := by
  simp [step, h] at valid ⊢
  simp [nonzero, valid]

theorem step_jumpi_zero {code dests rest : List Nat} {pc d : Nat} (h : code[pc]? = some 87) :
    step code dests pc (d :: 0 :: rest) = .running (pc + 1) rest := by
  simp [step, h]

theorem step_jumpi_short {code dests : List Nat} {pc d : Nat} (h : code[pc]? = some 87) :
    step code dests pc [d] = .underflow := by
  simp [step, h]

/-- Byte facts for one threaded site, checked on the concrete images. -/
structure Site (original candidate dests : List Nat) where
  pc : Nat
  width : Nat
  jump : Nat
  source : Nat
  target : Nat
  trampolineWidth : Nat
  isJump : jump = 86 ∨ jump = 87
  originalPush : original[pc]? = some (95 + width)
  candidatePush : candidate[pc]? = some (95 + width)
  originalValue : immediate ((original.drop (pc + 1)).take width) = source
  candidateValue : immediate ((candidate.drop (pc + 1)).take width) = target
  originalJump : original[pc + 1 + width]? = some jump
  candidateJump : candidate[pc + 1 + width]? = some jump
  widthBound : width ≤ 32
  trampolineBound : trampolineWidth ≤ 32
  jumpdest : original[source]? = some 91
  trampolinePush : original[source + 1]? = some (95 + trampolineWidth)
  trampolineValue :
    immediate ((original.drop (source + 2)).take trampolineWidth) = target
  trampolineJump : original[source + 2 + trampolineWidth]? = some 86
  sourceValid : dests.contains source = true
  targetValid : dests.contains target = true

/-- From the site, the candidate reaches in two steps the state the original
reaches in two to five steps, including equal stack faults. -/
theorem sound {original candidate dests : List Nat} (site : Site original candidate dests)
    (stack : List Nat) :
    ∃ k, k ≤ 3 ∧ run original dests (2 + k) (.running site.pc stack) =
      run candidate dests 2 (.running site.pc stack) := by
  obtain ⟨pc, w, j, x, y, v, isJump, op, cp, ov, cv, oj, cj, wb, vb, jd, tp, tv, tj, xs, ys⟩ := site
  by_cases full : 1024 ≤ stack.length
  · refine ⟨0, by omega, ?_⟩
    rw [run_running, run_running, step_push_full op wb full, step_push_full cp wb full,
      run_overflow, run_overflow]
  · have room : stack.length < 1024 := by omega
    have origPush := step_push (dests := dests) op wb room
    have candPush := step_push (dests := dests) cp wb room
    rw [ov] at origPush
    rw [cv] at candPush
    -- Trampoline: JUMPDEST at x, PUSH y at x + 1, JUMP at x + 2 + v.
    have trampoline : ∀ rest : List Nat, rest.length < 1024 →
        run original dests 3 (.running x rest) = .running y rest := by
      intro rest short
      have push := step_push (dests := dests) tp vb short
      rw [show x + 1 + 1 = x + 2 by omega, tv] at push
      rw [run_running, step_jumpdest jd, run_running, push, run_running,
        show x + 1 + 1 + v = x + 2 + v by omega, step_jump tj ys, run_zero]
    rcases isJump with rfl | rfl
    · refine ⟨3, by omega, ?_⟩
      rw [show 2 + 3 = 3 + 1 + 1 by rfl, run_running, origPush, run_running, step_jump oj xs,
        trampoline stack room, run_running, candPush, run_running, step_jump cj ys, run_zero]
    · cases stack with
      | nil =>
        refine ⟨0, by omega, ?_⟩
        rw [run_running, origPush, run_running, step_jumpi_short oj, run_running, candPush,
          run_running, step_jumpi_short cj, run_zero, run_zero]
      | cons c rest =>
        have short : rest.length < 1024 := by simp at room; omega
        by_cases zero : c = 0
        · subst zero
          refine ⟨0, by omega, ?_⟩
          rw [run_running, origPush, run_running, step_jumpi_zero oj, run_running, candPush,
            run_running, step_jumpi_zero cj, run_zero, run_zero]
        · refine ⟨3, by omega, ?_⟩
          rw [show 2 + 3 = 3 + 1 + 1 by rfl, run_running, origPush, run_running,
            step_jumpi_taken oj zero xs, trampoline rest short, run_running, candPush,
            run_running, step_jumpi_taken cj zero ys, run_zero]

end GolfThread
