import ChunkSummary
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfComposition GolfChunk
namespace GolfPathSummary

-- A checked path may charge memory expansion at an intermediate source state.
-- The evaluator remains the canonical post/TraceChunk witness; only cost is dynamic.
structure Summary (old new : ByteArray) where
  post : EVM.State → EVM.State
  stackMap : List UInt256 → List UInt256
  entry : UInt256
  exit : UInt256
  sourceSteps : Nat
  targetSteps : Nat
  powers : Nat
  masks : Nat
  cost : EVM.State → Nat
  required : Nat
  maximum : Nat
  produced : Nat
  feasible : required ≤ maximum
  count_eq : ∀ s, (post s).execLength = s.execLength + sourceSteps
  pc_eq : ∀ s, s.pc = entry → (post s).pc = exit
  stack_eq : ∀ s xs, s.stack = xs → (post s).stack = stackMap xs
  stack_length : ∀ xs, required ≤ xs.length →
    (stackMap xs).length = xs.length - required + produced
  gas_eq : ∀ s, cost s ≤ s.gasAvailable.toNat →
    (post s).gasAvailable.toNat = s.gasAvailable.toNat - cost s
  trace : ∀ s, s.pc = entry → required ≤ s.stack.length →
    s.stack.length ≤ maximum → cost s ≤ s.gasAvailable.toNat →
    TraceChunk old new sourceSteps targetSteps powers masks s (post s)

def ofPure {old new : ByteArray} (q : GolfChunkSummary.Summary old new) :
    Summary old new where
  post := q.post
  stackMap := q.stackMap
  entry := q.entry
  exit := q.exit
  sourceSteps := q.sourceSteps
  targetSteps := q.targetSteps
  powers := q.powers
  masks := q.masks
  cost := fun _ => q.gasCost
  required := q.required
  maximum := q.maximum
  produced := q.produced
  feasible := q.feasible
  count_eq := q.count_eq
  pc_eq := q.pc_eq
  stack_eq := q.stack_eq
  stack_length := q.stack_length
  gas_eq := q.gas_eq
  trace := q.trace

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
  cost := fun s => a.cost s + b.cost (a.post s)
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
    have enoughA : a.cost s ≤ s.gasAvailable.toNat := by omega
    have midGas := a.gas_eq s enoughA
    have enoughB : b.cost (a.post s) ≤ (a.post s).gasAvailable.toNat := by omega
    rw [b.gas_eq (a.post s) enoughB, midGas]
    omega
  trace := by
    intro s pc low high gas
    obtain ⟨lowA,highA,lowB,highB⟩ :=
      GolfChunkSummary.successor_bounds a.required a.maximum a.produced b.required b.maximum
        s.stack.length fits low high
    have enoughA : a.cost s ≤ s.gasAvailable.toNat := by omega
    have midGas := a.gas_eq s enoughA
    have enoughB : b.cost (a.post s) ≤ (a.post s).gasAvailable.toNat := by omega
    have midPC : (a.post s).pc = b.entry := by rw [a.pc_eq s pc, joins]
    have midStack := a.stack_eq s s.stack rfl
    have midLength : (a.post s).stack.length = s.stack.length-a.required+a.produced := by
      rw [midStack, a.stack_length s.stack lowA]
    have left := a.trace s pc lowA highA enoughA
    have right := b.trace (a.post s) midPC (by omega) (by omega) enoughB
    exact GolfChunk.append left right

def mstorePost (s : EVM.State) : EVM.State :=
  CanonicalMemory.memoryPost s
    ((s.stack[0]?).getD (UInt256.ofNat 0))
    ((s.stack[1]?).getD (UInt256.ofNat 0)) (s.stack.drop 2)

private theorem two_words (xs : List UInt256) (enough : 2 ≤ xs.length) :
    xs = ((xs[0]?).getD (UInt256.ofNat 0)) ::
      ((xs[1]?).getD (UInt256.ofNat 0)) :: xs.drop 2 := by
  cases xs with
  | nil => simp at enough
  | cons a xs =>
    cases xs with
    | nil => simp at enough
    | cons b tail => rfl

theorem mstore_gas (s : EVM.State)
    (gas : memoryExpansionCost s .MSTORE + 3 ≤ s.gasAvailable.toNat) :
    (mstorePost s).gasAvailable.toNat =
      s.gasAvailable.toNat-(memoryExpansionCost s .MSTORE + 3) := by
  have bounds := CanonicalMemory.expansion_charge_bounds s gas
  have opcodeGas : 3 ≤ (s.gasAvailable -
      UInt256.ofNat (memoryExpansionCost s .MSTORE)).toNat := bounds.2
  change (s.gasAvailable - UInt256.ofNat (memoryExpansionCost s .MSTORE) -
    UInt256.ofNat 3).toNat = _
  rw [word_sub_toNat (s.gasAvailable - UInt256.ofNat (memoryExpansionCost s .MSTORE))
      3 (by decide) opcodeGas,
    word_sub_toNat _ _ bounds.1 (by omega)]
  omega

def mstore {old new : ByteArray} (pc : UInt256)
    (oldDecoded : decode old pc = some (.MSTORE,none))
    (newDecoded : decode new pc = some (.MSTORE,none)) : Summary old new where
  post := mstorePost
  stackMap := fun xs => xs.drop 2
  entry := pc
  exit := pc + UInt256.ofNat 1
  sourceSteps := 1
  targetSteps := 1
  powers := 0
  masks := 0
  cost := fun s => memoryExpansionCost s .MSTORE + 3
  required := 2
  maximum := 1024
  produced := 0
  feasible := by decide
  count_eq := by intro s; rfl
  pc_eq := by
    intro s h
    change s.pc + UInt256.ofNat 1 = pc + UInt256.ofNat 1
    rw [h]
  stack_eq := by
    intro s xs h
    change s.stack.drop 2 = xs.drop 2
    rw [h]
  stack_length := by
    intro xs _
    simp only [List.length_drop,Nat.add_zero]
  gas_eq := mstore_gas
  trace := by
    intro s hpc low high gas
    have shape := two_words s.stack low
    have height : (s.stack.drop 2).length ≤ 1022 := by
      rw [List.length_drop]
      omega
    exact GolfChunk.mstore s ((s.stack[0]?).getD (UInt256.ofNat 0))
      ((s.stack[1]?).getD (UInt256.ofNat 0)) (s.stack.drop 2)
      (by rw [hpc]; exact oldDecoded) (by rw [hpc]; exact newDecoded)
      shape gas height

#print axioms ofPure
#print axioms compose
#print axioms mstore_gas
#print axioms mstore
end GolfPathSummary
