import PathSummary
import OffsetJump

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition GolfChunk GolfPathSummary
namespace GolfPathJump

def terminalPost {old new : ByteArray} (q : Summary old new)
    (destination : UInt256) (xs : List UInt256) (s : EVM.State) : EVM.State :=
  GolfJump.jumpPost (q.post s) destination (q.stackMap xs).tail

theorem source_count {old new : ByteArray} (q : Summary old new)
    (destination : UInt256) (xs : List UInt256) (s : EVM.State) :
    (terminalPost q destination xs s).execLength = s.execLength+q.sourceSteps+1 := by
  change (q.post s).execLength+1 = _
  rw [q.count_eq]

theorem source_gas {old new : ByteArray} (q : Summary old new)
    (destination : UInt256) (xs : List UInt256) (s : EVM.State)
    (gas : q.cost s+8 ≤ s.gasAvailable.toNat) :
    (terminalPost q destination xs s).gasAvailable.toNat =
      s.gasAvailable.toNat-(q.cost s+8) := by
  have before := q.gas_eq s (by omega)
  change ((q.post s).gasAvailable-UInt256.ofNat 8).toNat = _
  rw [word_sub_toNat _ 8 (by decide) (by omega), before]
  omega

-- The following static obligations are static generated facts, discharged by the final wrapper.
-- They are not additional caller-supplied hypotheses in a concrete certificate.
theorem summary_jump {old new : ByteArray} (q : Summary old new)
    (destination : UInt256)
    (head : ∀ xs : List UInt256, q.required ≤ xs.length → xs.length ≤ q.maximum →
      q.stackMap xs = destination :: (q.stackMap xs).tail)
    (outputBound : q.maximum-q.required+q.produced ≤ 1024)
    (oldDecoded : decode old q.exit = some (.JUMP,none))
    (newDecoded : decode new q.exit = some (.JUMP,none))
    (oldValid : (D_J old (UInt256.ofNat 0)).contains destination = true)
    (newValid : (D_J new (UInt256.ofNat 0)).contains destination = true)
    {owner surplus skipped s t}
    (related : DeployedOffset owner old new surplus skipped s t)
    (xs : List UInt256) (fuel : Nat)
    (pc : s.pc = q.entry) (stack : s.stack = xs)
    (gas : q.cost s+8 ≤ s.gasAvailable.toNat)
    (low : q.required ≤ xs.length) (height : xs.length ≤ q.maximum) :
    ∃ ce : EVM.State,
      X (fuel+q.sourceSteps+2) (D_J old (UInt256.ofNat 0)) s =
        X (fuel+1) (D_J old (UInt256.ofNat 0)) (terminalPost q destination xs s) ∧
      X (fuel+q.targetSteps+2) (D_J new (UInt256.ofNat 0)) t =
        X (fuel+1) (D_J new (UInt256.ofNat 0)) ce ∧
      DeployedOffset owner old new (surplus+2*q.powers+9*q.masks)
        (skipped+3*q.masks) (terminalPost q destination xs s) ce ∧
      (terminalPost q destination xs s).pc = destination ∧ ce.pc = destination ∧
      (terminalPost q destination xs s).stack = (q.stackMap xs).tail ∧
      ce.stack = (q.stackMap xs).tail ∧
      (terminalPost q destination xs s).gasAvailable.toNat =
        s.gasAvailable.toNat-(q.cost s+8) ∧
      (terminalPost q destination xs s).execLength = s.execLength+q.sourceSteps+1 ∧
      ce.execLength = t.execLength+q.targetSteps+1 := by
  have chunk := q.trace s pc (by simpa only [stack] using low)
    (by simpa only [stack] using height) (by omega)
  have trace : MixedTrace old new (fuel+2) (fuel+q.sourceSteps+2)
      (fuel+q.targetSteps+2) q.powers q.masks s (q.post s) := by
    convert GolfChunk.recover chunk (fuel+1) using 1 <;> omega
  obtain ⟨mid,sourceRun,targetRun,midRelated⟩ :=
    mixed_simulation trace t surplus skipped (D_J old (UInt256.ofNat 0))
      (D_J new (UInt256.ofNat 0)) related
  have midPC := q.pc_eq s pc
  have midStack : (q.post s).stack = destination :: (q.stackMap xs).tail :=
    (q.stack_eq s xs stack).trans (head xs low height)
  have midGas := q.gas_eq s (by omega)
  have lengthEq := q.stack_length xs low
  have headLength := congrArg List.length (head xs low height)
  simp only [List.length_cons] at headLength
  have physical : (q.stackMap xs).length ≤ 1024 := by omega
  have tailHeight : (q.stackMap xs).tail.length ≤ 1023 := by omega
  have sourceDecode : decode old (q.post s).pc = some (.JUMP,none) := by
    rw [midPC]
    exact oldDecoded
  have targetDecode : decode new mid.pc = some (.JUMP,none) := by
    rw [← offset_pc midRelated,midPC]
    exact newDecoded
  obtain ⟨sourceJump,targetJump,finalRelated⟩ :=
    GolfOffsetJump.paired_jump midRelated destination (q.stackMap xs).tail fuel fuel
      sourceDecode targetDecode midStack (by omega) (by omega) oldValid newValid
  have countSource := source_count q destination xs s
  have gap := GolfChunk.fuel_gap chunk
  have countTarget : (GolfJump.jumpPost mid destination (q.stackMap xs).tail).execLength =
      t.execLength+q.targetSteps+1 := by
    have startCount := related.count
    have endCount := finalRelated.count
    change (terminalPost q destination xs s).execLength =
      (GolfJump.jumpPost mid destination (q.stackMap xs).tail).execLength+
        (skipped+3*q.masks) at endCount
    omega
  exact ⟨GolfJump.jumpPost mid destination (q.stackMap xs).tail,
    sourceRun.trans sourceJump,targetRun.trans targetJump,finalRelated,
    rfl,rfl,rfl,rfl,source_gas q destination xs s gas,countSource,countTarget⟩

#print axioms source_count
#print axioms source_gas
#print axioms summary_jump
end GolfPathJump
