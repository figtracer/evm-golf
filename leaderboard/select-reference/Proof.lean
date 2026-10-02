-- Verification strategy: algebra.
import Std

/-!
A deliberately small, pure EVM bytecode model. A program starts with an empty
stack and receives two calldata words. It supports PUSH0, PUSH1..32, CALLDATALOAD
at offsets 0 and 32, DUP1, ADD, MUL, SUB, AND, OR, XOR, NOT, and SHL. The stack head is
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
      else if op = 128 then
        match stack with
        | a :: tail => run fuel rest (a :: a :: tail) x y
        | _ => none
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

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option pp.fullNames true
set_option maxRecDepth 4096

theorem expression_equivalent (x y : Golf.Word) : ((x &&& y) ||| ((~~~x) &&& (255 : Golf.Word))) = ((255 : Golf.Word) ^^^ (x &&& ((255 : Golf.Word) ^^^ y))) := by
  first | (solve | simp [BitVec.mul_comm]) | grind

theorem baseline_correct (x y : Golf.Word) :
    Golf.run 14 [96, 255, 95, 53, 25, 22, 96, 32, 53, 95, 53, 22, 23] [] x y = some [((x &&& y) ||| ((~~~x) &&& (255 : Golf.Word)))] := by
  rfl

theorem candidate_correct (x y : Golf.Word) :
    Golf.run 13 [96, 32, 53, 96, 255, 24, 95, 53, 22, 96, 255, 24] [] x y = some [((x &&& y) ||| ((~~~x) &&& (255 : Golf.Word)))] := by
  change some [((255 : Golf.Word) ^^^ (x &&& ((255 : Golf.Word) ^^^ y)))] = some [((x &&& y) ||| ((~~~x) &&& (255 : Golf.Word)))]
  exact congrArg (fun value : Golf.Word => some [value]) (expression_equivalent x y).symm

#print axioms expression_equivalent
#print axioms baseline_correct
#print axioms candidate_correct
