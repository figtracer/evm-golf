import TraceChunk
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfComposition GolfChunk
namespace GolfChunkSummary

-- Metadata uses output height at the minimum accepted input height.
-- This is equivalent to a signed stack delta but keeps proofs in Nat.
structure Summary (old new : ByteArray) where
  post : EVM.State → EVM.State
  stackMap : List UInt256 → List UInt256
  entry : UInt256
  exit : UInt256
  sourceSteps : Nat
  targetSteps : Nat
  powers : Nat
  masks : Nat
  gasCost : Nat
  required : Nat
  maximum : Nat
  produced : Nat
  feasible : required ≤ maximum
  count_eq : ∀ s, (post s).execLength = s.execLength + sourceSteps
  pc_eq : ∀ s, s.pc = entry → (post s).pc = exit
  stack_eq : ∀ s xs, s.stack = xs → (post s).stack = stackMap xs
  stack_length : ∀ xs, required ≤ xs.length →
    (stackMap xs).length = xs.length - required + produced
  gas_eq : ∀ s, gasCost ≤ s.gasAvailable.toNat →
    (post s).gasAvailable.toNat = s.gasAvailable.toNat - gasCost
  trace : ∀ s, s.pc = entry → required ≤ s.stack.length →
    s.stack.length ≤ maximum → gasCost ≤ s.gasAvailable.toNat →
    TraceChunk old new sourceSteps targetSteps powers masks s (post s)

theorem successor_bounds (rA maxA outA rB maxB n : Nat)
    (fits : outA ≤ maxB)
    (lower : rA + (rB-outA) ≤ n)
    (upper : n ≤ min maxA (rA+(maxB-outA))) :
    rA ≤ n ∧ n ≤ maxA ∧ rB ≤ n-rA+outA ∧ n-rA+outA ≤ maxB := by
  omega

-- The only extra hypotheses are static numeric feasibility and exact PC adjacency.
-- No successor execution, stack, PC, or gas obligation is assumed.
def compose {old new : ByteArray} (a b : Summary old new)
    (joins : a.exit = b.entry) (fits : a.produced ≤ b.maximum)
    (feasible : a.required + (b.required-a.produced) ≤
      min a.maximum (a.required+(b.maximum-a.produced))) : Summary old new where
  post := fun s => b.post (a.post s)
  stackMap := fun xs => b.stackMap (a.stackMap xs)
  entry := a.entry
  exit := b.exit
  sourceSteps := a.sourceSteps+b.sourceSteps
  targetSteps := a.targetSteps+b.targetSteps
  powers := a.powers+b.powers
  masks := a.masks+b.masks
  gasCost := a.gasCost+b.gasCost
  required := a.required+(b.required-a.produced)
  maximum := min a.maximum (a.required+(b.maximum-a.produced))
  produced := b.produced+(a.produced-b.required)
  feasible := feasible
  count_eq := by
    intro s
    rw [b.count_eq, a.count_eq]
    omega
  pc_eq := by
    intro s h
    apply b.pc_eq
    rw [a.pc_eq s h, joins]
  stack_eq := by
    intro s xs h
    rw [b.stack_eq (a.post s) (a.post s).stack rfl, a.stack_eq s xs h]
  stack_length := by
    intro xs h
    have lowA : a.required ≤ xs.length := by omega
    have lenA := a.stack_length xs lowA
    have lowB : b.required ≤ (a.stackMap xs).length := by omega
    rw [b.stack_length (a.stackMap xs) lowB, lenA]
    omega
  gas_eq := by
    intro s h
    have enoughA : a.gasCost ≤ s.gasAvailable.toNat := by omega
    have midGas := a.gas_eq s enoughA
    have enoughB : b.gasCost ≤ (a.post s).gasAvailable.toNat := by omega
    rw [b.gas_eq (a.post s) enoughB, midGas]
    omega
  trace := by
    intro s pc low high gas
    obtain ⟨lowA,highA,lowB,highB⟩ :=
      successor_bounds a.required a.maximum a.produced b.required b.maximum
        s.stack.length fits low high
    have enoughA : a.gasCost ≤ s.gasAvailable.toNat := by omega
    have midGas := a.gas_eq s enoughA
    have enoughB : b.gasCost ≤ (a.post s).gasAvailable.toNat := by omega
    have midPC : (a.post s).pc = b.entry := by rw [a.pc_eq s pc, joins]
    have midStack := a.stack_eq s s.stack rfl
    have midLength : (a.post s).stack.length = s.stack.length-a.required+a.produced := by
      rw [midStack, a.stack_length s.stack lowA]
    have left := a.trace s pc lowA highA enoughA
    have right := b.trace (a.post s) midPC (by omega) (by omega) enoughB
    exact GolfChunk.append left right

-- Projection roots preserve each ancillary claim's weaker premise set.
theorem composed_count {old new} (a b : Summary old new) joins fits feasible (s : EVM.State) :
    ((compose a b joins fits feasible).post s).execLength =
      s.execLength + (a.sourceSteps+b.sourceSteps) :=
  (compose a b joins fits feasible).count_eq s

theorem composed_pc {old new} (a b : Summary old new) joins fits feasible
    (s : EVM.State) (pc : s.pc = a.entry) :
    ((compose a b joins fits feasible).post s).pc = b.exit :=
  (compose a b joins fits feasible).pc_eq s pc

theorem composed_stack {old new} (a b : Summary old new) joins fits feasible
    (s : EVM.State) (xs : List UInt256) (stack : s.stack = xs) :
    ((compose a b joins fits feasible).post s).stack = b.stackMap (a.stackMap xs) :=
  (compose a b joins fits feasible).stack_eq s xs stack

theorem composed_gas {old new} (a b : Summary old new) joins fits feasible
    (s : EVM.State) (gas : a.gasCost+b.gasCost ≤ s.gasAvailable.toNat) :
    ((compose a b joins fits feasible).post s).gasAvailable.toNat =
      s.gasAvailable.toNat-(a.gasCost+b.gasCost) :=
  (compose a b joins fits feasible).gas_eq s gas

theorem composed_trace {old new} (a b : Summary old new) joins fits feasible
    (s : EVM.State) (pc : s.pc = a.entry)
    (low : a.required+(b.required-a.produced) ≤ s.stack.length)
    (high : s.stack.length ≤ min a.maximum (a.required+(b.maximum-a.produced)))
    (gas : a.gasCost+b.gasCost ≤ s.gasAvailable.toNat) :
    TraceChunk old new (a.sourceSteps+b.sourceSteps) (a.targetSteps+b.targetSteps)
      (a.powers+b.powers) (a.masks+b.masks) s ((compose a b joins fits feasible).post s) :=
  (compose a b joins fits feasible).trace s pc low high gas

#print axioms successor_bounds
#print axioms compose
#print axioms composed_count
#print axioms composed_pc
#print axioms composed_stack
#print axioms composed_gas
#print axioms composed_trace
end GolfChunkSummary
