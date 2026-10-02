import Std

/-!
A deliberately small, pure EVM bytecode model. A program starts with an empty
stack and receives two calldata words. It supports PUSH0, PUSH1..32, CALLDATALOAD
at offsets 0 and 32, ADD, MUL, SUB, AND, OR, XOR, NOT, and SHL. The stack head is
the EVM top. Unsupported opcodes, truncated immediates and stack underflow fail.

This models the expression body, before the shared memory/RETURN wrapper. It
does not model gas, out-of-gas, transactions, accounts, or general EVM behavior.
-/

namespace Golf

abbrev Word := BitVec 256

def immediate (bytes : List Nat) : Nat :=
  bytes.foldl (fun acc byte => acc * 256 + byte) 0

def run (fuel : Nat) (code : List Nat) (stack : List Word) (x y : Word) :
    Option (List Word) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match code with
    | [] => some stack
    | op :: rest =>
      if op = 95 then run fuel rest (0 :: stack) x y
      else if 96 ≤ op ∧ op ≤ 127 then
        let size := op - 95
        if size ≤ rest.length then
          run fuel (rest.drop size)
            (BitVec.ofNat 256 (immediate (rest.take size)) :: stack) x y
        else none
      else if op = 53 then
        match stack with
        | offset :: tail =>
          if offset = 0 then run fuel rest (x :: tail) x y
          else if offset = 32 then run fuel rest (y :: tail) x y
          else none
        | _ => none
      else if op = 25 then
        match stack with
        | a :: tail => run fuel rest ((~~~a) :: tail) x y
        | _ => none
      else
        match stack with
        | a :: b :: tail =>
          if op = 1 then run fuel rest ((a + b) :: tail) x y
          else if op = 2 then run fuel rest ((a * b) :: tail) x y
          else if op = 3 then run fuel rest ((a - b) :: tail) x y
          else if op = 22 then run fuel rest ((a &&& b) :: tail) x y
          else if op = 23 then run fuel rest ((a ||| b) :: tail) x y
          else if op = 24 then run fuel rest ((a ^^^ b) :: tail) x y
          else if op = 27 then run fuel rest ((b <<< a.toNat) :: tail) x y
          else none
        | _ => none

end Golf

-- External wall-clock limits govern both Lean lanes.
set_option maxHeartbeats 0
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem claim (x y : Golf.Word) : (x + (0 : Golf.Word)) = x := by
  simp

theorem baseline_correct (x y : Golf.Word) : Golf.run 5 [95, 95, 53, 1] [] x y = some [(x + (0 : Golf.Word))] := by
  rfl

theorem candidate_correct (x y : Golf.Word) : Golf.run 3 [95, 53] [] x y = some [(x + (0 : Golf.Word))] := by
  change some [x] = some [(x + (0 : Golf.Word))]
  rw [claim x y]

#print axioms claim
#print axioms baseline_correct
#print axioms candidate_correct
