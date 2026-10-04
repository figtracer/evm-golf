import Std

/-!
A deliberately small, pure EVM bytecode model. A program starts with an empty
stack and receives two calldata words. It supports PUSH0, PUSH1..32, CALLDATALOAD
at offsets 0 and 32, DUP1..16, SWAP1..16, POP, ADD, MUL, SUB, AND, OR, XOR, NOT, and SHL. The stack head is
the EVM top. Unsupported opcodes, truncated immediates and stack underflow fail.

This models the expression body, before the shared memory/RETURN wrapper. It
does not model gas, out-of-gas, transactions, accounts, or general EVM behavior.
-/

namespace Golf

abbrev Word := BitVec 256

def immediate (bytes : List Nat) : Nat :=
  bytes.foldl (fun acc byte => acc * 256 + byte) 0

-- Checked one-based EVM stack depths; missing words return failure.
def dupAt (depth : Nat) (stack : List Word) : Option (List Word) :=
  if depth = 0 then none else
    match stack[depth - 1]? with
    | some value => some (value :: stack)
    | none => none

def swapAt (depth : Nat) (stack : List Word) : Option (List Word) :=
  if depth = 0 then none else
    match stack with
    | top :: tail =>
      match tail[depth - 1]? with
      | some value => some (value :: tail.set (depth - 1) top)
      | none => none
    | [] => none

-- One opcode transition; each successful result contains the unconsumed code.
def step (op : Nat) (rest : List Nat) (stack : List Word) (x y : Word) :
    Option (List Nat × List Word) :=
  if op = 95 then some (rest, 0 :: stack)
  else if 96 ≤ op ∧ op ≤ 127 then
    let size := op - 95
    if size ≤ rest.length then
      some (rest.drop size, BitVec.ofNat 256 (immediate (rest.take size)) :: stack)
    else none
  else if op = 80 then
    match stack with
    | _ :: tail => some (rest, tail)
    | _ => none
  else if op = 128 then
    match stack with
    | a :: tail => some (rest, a :: a :: tail)
    | _ => none
  else if op = 53 then
    match stack with
    | offset :: tail =>
      if offset = 0 then some (rest, x :: tail)
      else if offset = 32 then some (rest, y :: tail)
      else none
    | _ => none
  else if op = 25 then
    match stack with
    | a :: tail => some (rest, (~~~a) :: tail)
    | _ => none
  else
    match stack with
    | a :: b :: tail =>
      if op = 1 then some (rest, (a + b) :: tail)
      else if op = 2 then some (rest, (a * b) :: tail)
      else if op = 3 then some (rest, (a - b) :: tail)
      else if op = 22 then some (rest, (a &&& b) :: tail)
      else if op = 23 then some (rest, (a ||| b) :: tail)
      else if op = 24 then some (rest, (a ^^^ b) :: tail)
      else if op = 27 then some (rest, (b <<< a.toNat) :: tail)
      else if 129 ≤ op ∧ op ≤ 143 then
        match dupAt (op - 127) (a :: b :: tail) with
        | some next => some (rest, next)
        | none => none
      else if 144 ≤ op ∧ op ≤ 159 then
        match swapAt (op - 143) (a :: b :: tail) with
        | some next => some (rest, next)
        | none => none
      else none
    | _ => none

def run (fuel : Nat) (code : List Nat) (stack : List Word) (x y : Word) :
    Option (List Word) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match code with
    | [] => some stack
    | op :: rest =>
      match step op rest stack x y with
      | some (nextCode, nextStack) => run fuel nextCode nextStack x y
      | none => none

attribute [simp] step.eq_def

end Golf
