/-!
Static gas for pure, completely decoded fragments. Each instruction is charged
before its stack transition. This is a local model, not a full-EVM or receipt-gas
proof. The schedule is explicit so later forks need a separate conformance check.
-/
namespace GolfGas

-- Only pure instructions with a fixed cost belong in this schedule.
def cancun (op : Nat) : Option Nat :=
  if op = 80 ∨ op = 95 then some 2
  else if op = 2 then some 5
  else if op = 1 ∨ op = 3 ∨ op = 22 ∨ op = 23 ∨ op = 24 ∨ op = 25 ∨ op = 27 ∨
      (96 ≤ op ∧ op ≤ 159) then some 3
  else none

def width (op : Nat) : Nat := if 96 ≤ op ∧ op ≤ 127 then op - 95 else 0

def costAux (price : Nat → Option Nat) : Nat → List Nat → Option Nat
  | 0, _ => none
  | _ + 1, [] => some 0
  | fuel + 1, op :: rest =>
    match price op with
    | none => none
    | some charge =>
      if width op ≤ rest.length then
        (costAux price fuel (rest.drop (width op))).map (charge + ·)
      else none

def cost (code : List Nat) : Option Nat := costAux cancun (code.length + 1) code

def run (price : Nat → Option Nat) :
    Nat → List Nat → List Golf.Word → Nat → Golf.Word → Golf.Word →
    Option (List Golf.Word × Nat)
  | 0, _, _, _, _, _ => none
  | fuel + 1, code, stack, gas, x, y =>
    if stack.length > 1024 then none
    else match code with
    | [] => some (stack, gas)
    | op :: rest =>
      match price op with
      | none => none
      | some charge =>
        if width op ≤ rest.length ∧ charge ≤ gas then
          match Golf.run 2 (op :: rest.take (width op)) stack x y with
          | none => none
          | some next => run price fuel (rest.drop (width op)) next (gas - charge) x y
        else none

-- Paying the total cost suffices for every prefix, since charges are natural numbers.
theorem sufficient (price : Nat → Option Nat) (fuel : Nat) (code : List Nat)
    (stack : List Golf.Word) (gas total : Nat) (x y : Golf.Word)
    (costed : costAux price fuel code = some total) (budget : total ≤ gas) :
    run price fuel code stack gas x y =
      (GolfBounded.run fuel code stack x y).map (fun output => (output, gas - total)) := by
  induction fuel generalizing code stack gas total with
  | zero => simp [costAux] at costed
  | succ fuel ih =>
    cases code with
    | nil =>
      have zero : total = 0 := by simpa [costAux] using costed.symm
      subst total
      by_cases overflow : 1024 < stack.length <;> simp [run, GolfBounded.run, overflow]
    | cons op rest =>
      cases priced : price op with
      | none => simp [costAux, priced] at costed
      | some charge =>
        by_cases complete : width op ≤ rest.length
        · cases tailCost : costAux price fuel (rest.drop (width op)) with
          | none => simp [costAux, priced, complete, tailCost] at costed
          | some tailTotal =>
            have totalEq : total = charge + tailTotal := by
              simpa [costAux, priced, complete, tailCost] using costed.symm
            subst total
            have enough : charge ≤ gas := by omega
            have tailBudget : tailTotal ≤ gas - charge := by omega
            simp only [run, GolfBounded.run, priced, complete, enough, and_self, ite_true]
            split
            · rfl
            · change (match Golf.run 2 (op :: rest.take (width op)) stack x y with
                | none => none
                | some next => run price fuel (rest.drop (width op)) next (gas-charge) x y) =
                  (match Golf.run 2 (op :: rest.take (width op)) stack x y with
                  | none => none
                  | some next => GolfBounded.run fuel (rest.drop (width op)) next x y).map
                    (fun output => (output, gas-(charge+tailTotal)))
              cases step : Golf.run 2 (op :: rest.take (width op)) stack x y with
              | none => rfl
              | some next =>
                dsimp only
                rw [ih (rest.drop (width op)) next (gas-charge) tailTotal tailCost tailBudget]
                change (GolfBounded.run fuel (rest.drop (width op)) next x y).map
                    (fun output => (output, gas-charge-tailTotal)) =
                  (GolfBounded.run fuel (rest.drop (width op)) next x y).map
                    (fun output => (output, gas-(charge+tailTotal)))
                congr 1
                funext output
                congr 1
                omega
        · simp [costAux, priced, complete] at costed

structure Improvement (before after : List Nat) where
  beforeCost : Nat
  afterCost : Nat
  beforeChecked : cost before = some beforeCost
  afterChecked : cost after = some afterCost
  cheaper : afterCost < beforeCost

-- Successful execution is preserved for the original budget. Lower budgets
-- may make only the candidate succeed; this is not equal failure behavior.
theorem Improvement.refines {before after : List Nat} (h : Improvement before after)
    (equal : ∀ stack x y,
      GolfBounded.run (before.length+1) before stack x y =
      GolfBounded.run (after.length+1) after stack x y)
    (stack : List Golf.Word) (gas : Nat) (x y : Golf.Word) (output : List Golf.Word)
    (budget : h.beforeCost ≤ gas)
    (success : GolfBounded.run (before.length+1) before stack x y = some output) :
    run cancun (before.length+1) before stack gas x y = some (output, gas-h.beforeCost) ∧
    run cancun (after.length+1) after stack gas x y = some (output, gas-h.afterCost) ∧
    gas-h.beforeCost < gas-h.afterCost ∧ gas-h.afterCost ≤ gas := by
  have afterBudget : h.afterCost ≤ gas := by have := h.cheaper; omega
  rw [sufficient cancun _ _ _ _ _ _ _ h.beforeChecked budget,
    sufficient cancun _ _ _ _ _ _ _ h.afterChecked afterBudget,
    ← equal stack x y, success]
  simp only [Option.map_some, true_and]
  have := h.cheaper
  omega

end GolfGas
