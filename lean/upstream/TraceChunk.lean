import MixedTrace
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset CanonicalMaskWindow GolfComposition
namespace GolfChunk

-- A finite source witness with an arbitrary, independently indexed continuation.
def TraceChunk (old new : ByteArray) (sourceSteps targetSteps powers masks : Nat)
    (start finish : EVM.State) : Prop :=
  ∀ (residual sourceTail targetTail suffixPowers suffixMasks : Nat) (final : EVM.State),
    MixedTrace old new residual (sourceTail+1) (targetTail+1)
      suffixPowers suffixMasks finish final →
    MixedTrace old new residual (sourceTail+sourceSteps+1) (targetTail+targetSteps+1)
      (powers+suffixPowers) (masks+suffixMasks) start final

theorem identity (old new : ByteArray) (s : EVM.State) :
    TraceChunk old new 0 0 0 0 s s := by
  intro residual sf tf p m final rest
  simpa only [Nat.add_zero, Nat.zero_add] using rest

theorem append {old new : ByteArray} {aS aT aP aM bS bT bP bM : Nat}
    {s u v : EVM.State}
    (left : TraceChunk old new aS aT aP aM s u)
    (right : TraceChunk old new bS bT bP bM u v) :
    TraceChunk old new (aS+bS) (aT+bT) (aP+bP) (aM+bM) s v := by
  intro residual sf tf p m final rest
  have tail := right residual sf tf p m final rest
  have whole := left residual (sf+bS) (tf+bT) (bP+p) (bM+m) final tail
  convert whole using 1 <;> omega

theorem recover {old new : ByteArray} {nS nT p m : Nat} {s u : EVM.State}
    (chunk : TraceChunk old new nS nT p m s u) (fuel : Nat) :
    MixedTrace old new (fuel+1) (fuel+nS+1) (fuel+nT+1) p m s u := by
  simpa only [Nat.add_zero] using chunk (fuel+1) fuel fuel 0 0 u (MixedTrace.done u)

theorem fuel_gap {old new : ByteArray} {nS nT p m : Nat} {s u : EVM.State}
    (chunk : TraceChunk old new nS nT p m s u) : nS = nT + 3*m := by
  have h := GolfComposition.fuel_gap (recover chunk 0)
  omega

theorem mask {old new : ByteArray} (s : EVM.State) (a : UInt256) (tail : List UInt256)
    (oldDecoded : BeforeDecoded (withCode s old))
    (newDecoded : AfterDecoded (withCode s new))
    (stack : s.stack = a::tail) (gas : 36 ≤ s.gasAvailable.toNat)
    (height : tail.length ≤ 1020) :
    TraceChunk old new 12 9 0 1 s (snapshot s (finalStack a tail) 18 12) := by
  intro residual sf tf p m final rest
  have h := MixedTrace.mask s final sf tf p m a tail oldDecoded newDecoded stack gas height rest
  convert h using 1 <;> omega

theorem power {old new : ByteArray} (s : EVM.State) (op : Operation.POp)
    (width k : Nat) (a : UInt256) (tail : List UInt256)
    (nonzero : op ≠ .PUSH0) (range : k < 256)
    (oldDecoded : MulPowerAt old s.pc op width k)
    (newDecoded : ShiftPowerAt new s.pc op width k)
    (stack : s.stack = a::tail) (gas : 8 ≤ s.gasAvailable.toNat)
    (height : s.stack.length < 1024) :
    TraceChunk old new 2 2 1 0 s (mulPowerPost s old width k a tail) := by
  intro residual sf tf p m final rest
  have h := MixedTrace.power s final sf tf p m op width k a tail nonzero range
    oldDecoded newDecoded stack gas height rest
  convert h using 1 <;> omega

theorem same {old new : ByteArray} (s next : EVM.State)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (allowed : NonterminalStackOp op)
    (oldDecoded : decode old s.pc = some (op,arg))
    (newDecoded : decode new s.pc = some (op,arg))
    (bounds : FullXBounds s op)
    (canonical : ∀ fuel, EVM.step (fuel+1) (C' s op) (some (op,arg)) s = .ok next) :
    TraceChunk old new 1 1 0 0 s next := by
  intro residual sf tf p m final rest
  have h := MixedTrace.same s next final sf tf p m op arg allowed oldDecoded
    newDecoded bounds (canonical sf) rest
  convert h using 1 <;> omega

theorem extended {old new : ByteArray} (s next : EVM.State)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (allowed : ExtendedStackOp op)
    (oldDecoded : decode old s.pc = some (op,arg))
    (newDecoded : decode new s.pc = some (op,arg))
    (bounds : FullXBounds s op)
    (canonical : ∀ fuel, EVM.step (fuel+1) (C' s op) (some (op,arg)) s = .ok next) :
    TraceChunk old new 1 1 0 0 s next := by
  intro residual sf tf p m final rest
  have h := MixedTrace.extended s next final sf tf p m op arg allowed oldDecoded
    newDecoded bounds (canonical sf) rest
  convert h using 1 <;> omega

theorem extra {old new : ByteArray} (s next : EVM.State)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (allowed : ExtraOp op)
    (oldDecoded : decode old s.pc = some (op,arg))
    (newDecoded : decode new s.pc = some (op,arg))
    (bounds : FullXBounds s op)
    (canonical : ∀ fuel, EVM.step (fuel+1) (C' s op) (some (op,arg)) s = .ok next) :
    TraceChunk old new 1 1 0 0 s next := by
  intro residual sf tf p m final rest
  have h := MixedTrace.extra s next final sf tf p m op arg allowed oldDecoded
    newDecoded bounds (canonical sf) rest
  convert h using 1 <;> omega

theorem mstore {old new : ByteArray} (s : EVM.State)
    (address value : UInt256) (tail : List UInt256)
    (oldDecoded : decode old s.pc = some (.MSTORE,none))
    (newDecoded : decode new s.pc = some (.MSTORE,none))
    (stack : s.stack = address :: value :: tail)
    (gas : memoryExpansionCost s .MSTORE + 3 ≤ s.gasAvailable.toNat)
    (height : tail.length ≤ 1022) :
    TraceChunk old new 1 1 0 0 s (CanonicalMemory.memoryPost s address value tail) := by
  intro residual sf tf p m final rest
  have h := MixedTrace.mstore s final sf tf p m address value tail oldDecoded newDecoded
    stack gas height rest
  convert h using 1 <;> omega

#print axioms mstore
#print axioms identity
#print axioms append
#print axioms recover
#print axioms fuel_gap
#print axioms mask
#print axioms power
#print axioms same
#print axioms extended
#print axioms extra
end GolfChunk
