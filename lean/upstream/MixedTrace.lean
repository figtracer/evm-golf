import OffsetTransport
import CanonicalMask
import MemoryDriver
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset CanonicalMaskWindow
namespace GolfComposition

theorem before_decoded_transfer {s t : EVM.State} {code : ByteArray}
 (h : BeforeDecoded (withCode s code)) (hc : t.executionEnv.code = code) (hp : t.pc = s.pc) :
 BeforeDecoded t := by
 constructor
 · simpa only [withCode,hc,hp] using h.d0
 · simpa only [withCode,hc,hp] using h.d1
 · simpa only [withCode,hc,hp] using h.d2
 · simpa only [withCode,hc,hp] using h.d3
 · simpa only [withCode,hc,hp] using h.d4
 · simpa only [withCode,hc,hp] using h.d5
 · simpa only [withCode,hc,hp] using h.d6
 · simpa only [withCode,hc,hp] using h.d7
 · simpa only [withCode,hc,hp] using h.d8
 · simpa only [withCode,hc,hp] using h.d9
 · simpa only [withCode,hc,hp] using h.d10
 · simpa only [withCode,hc,hp] using h.d11
theorem after_decoded_transfer {s t : EVM.State} {code : ByteArray}
 (h : AfterDecoded (withCode s code)) (hc : t.executionEnv.code = code) (hp : t.pc = s.pc) :
 AfterDecoded t := by
 constructor
 · simpa only [withCode,hc,hp] using h.d0
 · simpa only [withCode,hc,hp] using h.d1
 · simpa only [withCode,hc,hp] using h.d2
 · simpa only [withCode,hc,hp] using h.d3
 · simpa only [withCode,hc,hp] using h.d4
 · simpa only [withCode,hc,hp] using h.d5
 · simpa only [withCode,hc,hp] using h.d6
 · simpa only [withCode,hc,hp] using h.d7
 · simpa only [withCode,hc,hp] using h.d8

-- A source-only finite witness: candidate states/steps/success are not fields.
-- The separate fuel indices account for eliminated instructions.
inductive MixedTrace (old new : ByteArray) (residualFuel : Nat) :
 Nat → Nat → Nat → Nat → EVM.State → EVM.State → Prop where
 | done (s : EVM.State) : MixedTrace old new residualFuel residualFuel residualFuel 0 0 s s
 | same (s next final : EVM.State) (sourceFuel targetFuel powers masks : Nat)
   (op : Operation .EVM) (arg : Option (UInt256 × Nat))
   (allowed : NonterminalStackOp op)
   (oldDecode : decode old s.pc = some (op,arg))
   (newDecode : decode new s.pc = some (op,arg))
   (bounds : FullXBounds s op)
   (canonical : EVM.step (sourceFuel+1) (C' s op) (some (op,arg)) s = .ok next)
   (rest : MixedTrace old new residualFuel (sourceFuel+1) (targetFuel+1) powers masks next final) :
   MixedTrace old new residualFuel (sourceFuel+2) (targetFuel+2) powers masks s final
 | extended (s next final : EVM.State) (sourceFuel targetFuel powers masks : Nat)
   (op : Operation .EVM) (arg : Option (UInt256 × Nat))
   (allowed : ExtendedStackOp op)
   (oldDecode : decode old s.pc = some (op,arg))
   (newDecode : decode new s.pc = some (op,arg))
   (bounds : FullXBounds s op)
   (canonical : EVM.step (sourceFuel+1) (C' s op) (some (op,arg)) s = .ok next)
   (rest : MixedTrace old new residualFuel (sourceFuel+1) (targetFuel+1) powers masks next final) :
   MixedTrace old new residualFuel (sourceFuel+2) (targetFuel+2) powers masks s final
 | extra (s next final : EVM.State) (sourceFuel targetFuel powers masks : Nat)
   (op : Operation .EVM) (arg : Option (UInt256 × Nat))
   (allowed : ExtraOp op)
   (oldDecode : decode old s.pc = some (op,arg))
   (newDecode : decode new s.pc = some (op,arg))
   (bounds : FullXBounds s op)
   (canonical : EVM.step (sourceFuel+1) (C' s op) (some (op,arg)) s = .ok next)
   (rest : MixedTrace old new residualFuel (sourceFuel+1) (targetFuel+1) powers masks next final) :
   MixedTrace old new residualFuel (sourceFuel+2) (targetFuel+2) powers masks s final
 | mstore (s final : EVM.State) (sourceFuel targetFuel powers masks : Nat)
   (address value : UInt256) (tail : List UInt256)
   (oldDecode : decode old s.pc = some (.MSTORE,none))
   (newDecode : decode new s.pc = some (.MSTORE,none))
   (stack : s.stack = address :: value :: tail)
   (gas : memoryExpansionCost s .MSTORE + 3 ≤ s.gasAvailable.toNat)
   (height : tail.length ≤ 1022)
   (rest : MixedTrace old new residualFuel (sourceFuel+1) (targetFuel+1) powers masks
     (CanonicalMemory.memoryPost s address value tail) final) :
   MixedTrace old new residualFuel (sourceFuel+2) (targetFuel+2) powers masks s final
 | mask (s final : EVM.State) (sourceFuel targetFuel powers masks : Nat)
   (a : UInt256) (tail : List UInt256)
   (oldDecoded : BeforeDecoded (withCode s old))
   (newDecoded : AfterDecoded (withCode s new))
   (stack : s.stack = a::tail) (gas : 36 ≤ s.gasAvailable.toNat)
   (height : tail.length ≤ 1020)
   (rest : MixedTrace old new residualFuel (sourceFuel+1) (targetFuel+1) powers masks
     (snapshot s (finalStack a tail) 18 12) final) :
   MixedTrace old new residualFuel (sourceFuel+13) (targetFuel+10) powers (masks+1) s final

 | power (s final : EVM.State) (sourceFuel targetFuel powers masks : Nat)
   (p : Operation.POp) (width k : Nat) (a : UInt256) (tail : List UInt256)
   (nonzero : p ≠ .PUSH0) (range : k < 256)
   (oldFragment : MulPowerAt old s.pc p width k)
   (newFragment : ShiftPowerAt new s.pc p width k)
   (stack : s.stack = a :: tail) (gas : 8 ≤ s.gasAvailable.toNat)
   (height : s.stack.length < 1024)
   (rest : MixedTrace old new residualFuel (sourceFuel+1) (targetFuel+1) powers masks
      (mulPowerPost s old width k a tail) final) :
   MixedTrace old new residualFuel (sourceFuel+3) (targetFuel+3) (powers+1) masks s final

theorem fuel_gap {old new residualFuel sourceFuel targetFuel powers masks s final}
 (trace : MixedTrace old new residualFuel sourceFuel targetFuel powers masks s final) :
 sourceFuel = targetFuel + 3*masks := by
 induction trace <;> omega

-- Canonical prefix equations only; no equality of the two remaining suffix calls.
-- Supplied jump arrays are arbitrary and are unused by these opcode families.
theorem mixed_simulation {owner old new residualFuel sourceFuel targetFuel powers masks s final}
 (trace : MixedTrace old new residualFuel sourceFuel targetFuel powers masks s final)
 (candidate : EVM.State) (surplus skipped : Nat)
 (oldJumps newJumps : Array UInt256)
 (related : DeployedOffset owner old new surplus skipped s candidate) :
 ∃ candidateFinal : EVM.State,
   X sourceFuel oldJumps s = X residualFuel oldJumps final ∧
   X targetFuel newJumps candidate = X residualFuel newJumps candidateFinal ∧
   DeployedOffset owner old new (surplus+2*powers+9*masks) (skipped+3*masks)
     final candidateFinal := by
 induction trace generalizing candidate surplus skipped with
 | done s => exact ⟨candidate,rfl,rfl,by simpa using related⟩
 | same s next final sf tf powers masks op arg allowed oldDecode newDecode bounds canonical rest ih =>
   obtain ⟨cn,cb,cstep,nextRelated,_,_⟩ :=
     offset_step_transport s candidate next sf tf surplus skipped owner old new
       op arg allowed bounds related canonical
   have sourceDecode : decode s.executionEnv.code s.pc = some (op,arg) := by
     rw [related.maps.2.2.1.2.1]; exact oldDecode
   have targetDecode : decode candidate.executionEnv.code candidate.pc = some (op,arg) := by
     rw [related.maps.2.2.2.2.1,←offset_pc related]; exact newDecode
   obtain ⟨cf,sourceRun,targetRun,finalRelated⟩ := ih cn surplus skipped nextRelated
   exact ⟨cf,(X_next s next sf oldJumps op arg allowed sourceDecode bounds canonical).trans sourceRun,
     (X_next candidate cn tf newJumps op arg allowed targetDecode cb cstep).trans targetRun,finalRelated⟩
 | extended s next final sf tf powers masks op arg allowed oldDecode newDecode bounds canonical rest ih =>
   obtain ⟨cn,cb,cstep,nextRelated,_,_⟩ :=
     offset_extended_transport s candidate next sf tf surplus skipped owner old new
       op arg allowed bounds related canonical
   have sourceDecode : decode s.executionEnv.code s.pc = some (op,arg) := by
     rw [related.maps.2.2.1.2.1]; exact oldDecode
   have targetDecode : decode candidate.executionEnv.code candidate.pc = some (op,arg) := by
     rw [related.maps.2.2.2.2.1,←offset_pc related]; exact newDecode
   obtain ⟨cf,sourceRun,targetRun,finalRelated⟩ := ih cn surplus skipped nextRelated
   exact ⟨cf,(X_next_extended s next sf oldJumps op arg allowed sourceDecode bounds canonical).trans sourceRun,
     (X_next_extended candidate cn tf newJumps op arg allowed targetDecode cb cstep).trans targetRun,finalRelated⟩
 | extra s next final sf tf powers masks op arg allowed oldDecode newDecode bounds canonical rest ih =>
   obtain ⟨cn,cb,cstep,nextRelated,_,_⟩ :=
     offset_extra_transport s candidate next sf tf surplus skipped owner old new
       op arg allowed bounds related canonical
   have sourceDecode : decode s.executionEnv.code s.pc = some (op,arg) := by
     rw [related.maps.2.2.1.2.1]; exact oldDecode
   have targetDecode : decode candidate.executionEnv.code candidate.pc = some (op,arg) := by
     rw [related.maps.2.2.2.2.1,←offset_pc related]; exact newDecode
   obtain ⟨cf,sourceRun,targetRun,finalRelated⟩ := ih cn surplus skipped nextRelated
   exact ⟨cf,(X_next_extra s next sf oldJumps op arg allowed sourceDecode bounds canonical).trans sourceRun,
     (X_next_extra candidate cn tf newJumps op arg allowed targetDecode cb cstep).trans targetRun,finalRelated⟩
 | mstore s final sf tf powers masks address value tail oldDecode newDecode stack gas height rest ih =>
   have sourceDecode : decode s.executionEnv.code s.pc = some (.MSTORE,none) := by
     rw [related.maps.2.2.1.2.1]
     exact oldDecode
   have targetDecode : decode candidate.executionEnv.code candidate.pc = some (.MSTORE,none) := by
     rw [related.maps.2.2.2.2.1,←offset_pc related]
     exact newDecode
   obtain ⟨sourceStep,targetStep,nextRelated⟩ :=
     CanonicalMemory.mstore_pair related address value tail sf tf oldJumps newJumps
       sourceDecode targetDecode stack gas (by omega)
   obtain ⟨cf,sourceRun,targetRun,finalRelated⟩ :=
     ih (CanonicalMemory.memoryPost candidate address value tail) surplus skipped nextRelated
   exact ⟨cf,sourceStep.trans sourceRun,targetStep.trans targetRun,finalRelated⟩
 | mask s final sf tf powers masks a tail oldDecoded newDecoded stack gas height rest ih =>
   have sourceDecoded : BeforeDecoded s := before_decoded_transfer oldDecoded related.maps.2.2.1.2.1 rfl
   have targetDecoded : AfterDecoded candidate := after_decoded_transfer newDecoded related.maps.2.2.2.2.1 (offset_pc related).symm
   have sourceBoundary := canonical_mask_replacement related a tail sf oldJumps newJumps sourceDecoded targetDecoded stack gas height
   have targetBoundary := canonical_mask_replacement related a tail tf oldJumps newJumps sourceDecoded targetDecoded stack gas height
   obtain ⟨cf,sourceRun,targetRun,finalRelated⟩ :=
     ih (snapshot candidate (finalStack a tail) 18 9) (surplus+9) (skipped+3) sourceBoundary.2.2
   refine ⟨cf,sourceBoundary.1.trans sourceRun,targetBoundary.2.1.trans targetRun,?_⟩
   convert finalRelated using 1 <;> omega

 | power s final sf tf powers masks p width k a tail nz range oldFragment newFragment stack gas height rest ih =>
   have boundary := offset_power_boundary owner old new s candidate p width k surplus skipped a tail
     sf tf oldJumps newJumps related nz range oldFragment
     (by rw [←offset_pc related]; exact newFragment) stack gas height
   obtain ⟨cf,sourceRun,targetRun,finalRelated⟩ := ih
     (shiftPowerPost candidate new width k a tail) (surplus+2) skipped boundary.2.2
   refine ⟨cf,boundary.1.trans sourceRun,boundary.2.1.trans targetRun,?_⟩
   convert finalRelated using 1 <;> omega

#print axioms fuel_gap
#print axioms mixed_simulation
end GolfComposition
