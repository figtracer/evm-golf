import Regions
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream
namespace GolfPowerRegion
theorem pc_add (m n : Nat) :
    UInt256.ofNat m + UInt256.ofNat n = UInt256.ofNat (m+n) := by
  change UInt256.mk (Fin.ofNat _ m + Fin.ofNat _ n) = UInt256.mk (Fin.ofNat _ (m+n))
  congr 1
  apply Fin.ext
  simp [Fin.add_def, Fin.ofNat]

def compilerPower (originalCode : ByteArray) (s : EVM.State) (a b c : UInt256) (tail : List UInt256) : EVM.State :=
  mulPowerPost s originalCode 1 5 a (b :: c :: tail)

def compilerAdd (originalCode : ByteArray) (s : EVM.State) (a b c : UInt256) (tail : List UInt256) : EVM.State :=
  binaryPost (compilerPower originalCode s a b c tail) (UInt256.add (UInt256.mul (UInt256.ofNat 32) a) b) (c :: tail) 3

def compilerSwap (originalCode : ByteArray) (s : EVM.State) (a b c : UInt256) (tail : List UInt256) : EVM.State :=
  binaryPost (compilerAdd originalCode s a b c tail) c ((UInt256.add (UInt256.mul (UInt256.ofNat 32) a) b) :: tail) 3

def compilerZero (originalCode : ByteArray) (s : EVM.State) (a b c : UInt256) (tail : List UInt256) : EVM.State :=
  binaryPost (compilerSwap originalCode s a b c tail) (UInt256.ofNat 0) (compilerSwap originalCode s a b c tail).stack 2

def compilerDupA (originalCode : ByteArray) (s : EVM.State) (a b c : UInt256) (tail : List UInt256) : EVM.State :=
  binaryPost (compilerZero originalCode s a b c tail) (UInt256.ofNat 0) ((UInt256.ofNat 0) :: c :: (UInt256.add (UInt256.mul (UInt256.ofNat 32) a) b) :: tail) 3

def compilerDupB (originalCode : ByteArray) (s : EVM.State) (a b c : UInt256) (tail : List UInt256) : EVM.State :=
  binaryPost (compilerDupA originalCode s a b c tail) (UInt256.ofNat 0) ((UInt256.ofNat 0) :: (UInt256.ofNat 0) :: c :: (UInt256.add (UInt256.mul (UInt256.ofNat 32) a) b) :: tail) 3

def compilerExit (originalCode : ByteArray) (destination : Nat) (s : EVM.State) (a b c : UInt256) (tail : List UInt256) : EVM.State :=
  pushedWidth (compilerDupB originalCode s a b c tail) (UInt256.ofNat destination) 2

theorem compilerTrace (originalCode candidateCode : ByteArray) (entry destination : Nat)
    (originalAddDecoded : decode originalCode (UInt256.ofNat (entry+3)) = some ((Operation.ADD : Operation .EVM), none))
    (originalSwapDecoded : decode originalCode (UInt256.ofNat (entry+4)) = some ((Operation.SWAP1 : Operation .EVM), none))
    (originalZeroDecoded : decode originalCode (UInt256.ofNat (entry+5)) = some ((Operation.PUSH0 : Operation .EVM), none))
    (originalDupADecoded : decode originalCode (UInt256.ofNat (entry+6)) = some ((Operation.DUP1 : Operation .EVM), none))
    (originalDupBDecoded : decode originalCode (UInt256.ofNat (entry+7)) = some ((Operation.DUP1 : Operation .EVM), none))
    (originalTargetDecoded : decode originalCode (UInt256.ofNat (entry+8)) = some ((Operation.Push .PUSH2 : Operation .EVM), some (UInt256.ofNat destination, 2)))
    (candidateAddDecoded : decode candidateCode (UInt256.ofNat (entry+3)) = some ((Operation.ADD : Operation .EVM), none))
    (candidateSwapDecoded : decode candidateCode (UInt256.ofNat (entry+4)) = some ((Operation.SWAP1 : Operation .EVM), none))
    (candidateZeroDecoded : decode candidateCode (UInt256.ofNat (entry+5)) = some ((Operation.PUSH0 : Operation .EVM), none))
    (candidateDupADecoded : decode candidateCode (UInt256.ofNat (entry+6)) = some ((Operation.DUP1 : Operation .EVM), none))
    (candidateDupBDecoded : decode candidateCode (UInt256.ofNat (entry+7)) = some ((Operation.DUP1 : Operation .EVM), none))
    (candidateTargetDecoded : decode candidateCode (UInt256.ofNat (entry+8)) = some ((Operation.Push .PUSH2 : Operation .EVM), some (UInt256.ofNat destination, 2)))
    (originalSite : MulPowerAt originalCode (UInt256.ofNat entry) .PUSH1 1 5)
    (candidateSite : ShiftPowerAt candidateCode (UInt256.ofNat entry) .PUSH1 1 5)
    (s : EVM.State) (a b c : UInt256) (tail : List UInt256) (fuel : Nat)
    (pc : s.pc = UInt256.ofNat entry) (stack : s.stack = a :: b :: c :: tail)
    (gas : 25 ≤ s.gasAvailable.toNat) (peak : tail.length + 6 ≤ 1024) :
    OpenRegionTrace originalCode candidateCode (fuel+1) (fuel+9) 1 s (compilerExit originalCode destination s a b c tail) := by
  have g1 := word_sub_toNat (s.gasAvailable) 3 (by decide) (by omega)
  have g2 := word_sub_toNat (s.gasAvailable - UInt256.ofNat 3) 5 (by decide) (by omega)
  have g3 := word_sub_toNat (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5) 3 (by decide) (by omega)
  have g4 := word_sub_toNat (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5 - UInt256.ofNat 3) 3 (by decide) (by omega)
  have g5 := word_sub_toNat (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5 - UInt256.ofNat 3 - UInt256.ofNat 3) 2 (by decide) (by omega)
  have g6 := word_sub_toNat (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5 - UInt256.ofNat 3 - UInt256.ofNat 3 - UInt256.ofNat 2) 3 (by decide) (by omega)
  have g7 := word_sub_toNat (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5 - UInt256.ofNat 3 - UInt256.ofNat 3 - UInt256.ofNat 2 - UInt256.ofNat 3) 3 (by decide) (by omega)
  apply OpenRegionTrace.power s _ (fuel+6) 0 .PUSH1 1 5 a (b :: c :: tail) (by decide) (by decide)
  · rw [pc]; exact originalSite
  · rw [pc]; exact candidateSite
  · exact stack
  · omega
  · simp [stack]; omega
  change OpenRegionTrace originalCode candidateCode (fuel+1) (fuel+7) 0 (compilerPower originalCode s a b c tail) (compilerExit originalCode destination s a b c tail)
  apply OpenRegionTrace.extended (compilerPower originalCode s a b c tail) (compilerAdd originalCode s a b c tail) _ (fuel+5) 0 .ADD (none) .add
  · simp only [compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode,pc,pc_add,Nat.add_assoc]; exact originalAddDecoded
  · simp only [compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode,pc,pc_add,Nat.add_assoc]; exact candidateAddDecoded
  · constructor
    · change 3 ≤ (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5).toNat
      omega
    · simp [δ,compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode]
    · simp [δ,α,compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode]; omega
  · exact step_add _ (fuel+5) 3 none b (UInt256.mul (UInt256.ofNat 32) a) (c :: tail) rfl
  change OpenRegionTrace originalCode candidateCode (fuel+1) (fuel+6) 0 (compilerAdd originalCode s a b c tail) (compilerExit originalCode destination s a b c tail)
  apply OpenRegionTrace.extended (compilerAdd originalCode s a b c tail) (compilerSwap originalCode s a b c tail) _ (fuel+4) 0 .SWAP1 (none) .swap1
  · simp only [compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode,pc,pc_add,Nat.add_assoc]; exact originalSwapDecoded
  · simp only [compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode,pc,pc_add,Nat.add_assoc]; exact candidateSwapDecoded
  · constructor
    · change 3 ≤ (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5 - UInt256.ofNat 3).toNat
      omega
    · simp [δ,compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode]
    · simp [δ,α,compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode]; omega
  · exact step_swap1 _ (fuel+4) 3 none c (UInt256.add (UInt256.mul (UInt256.ofNat 32) a) b) tail rfl
  change OpenRegionTrace originalCode candidateCode (fuel+1) (fuel+5) 0 (compilerSwap originalCode s a b c tail) (compilerExit originalCode destination s a b c tail)
  apply OpenRegionTrace.extended (compilerSwap originalCode s a b c tail) (compilerZero originalCode s a b c tail) _ (fuel+3) 0 .PUSH0 (none) .push0
  · simp only [compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode,pc,pc_add,Nat.add_assoc]; exact originalZeroDecoded
  · simp only [compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode,pc,pc_add,Nat.add_assoc]; exact candidateZeroDecoded
  · constructor
    · change 2 ≤ (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5 - UInt256.ofNat 3 - UInt256.ofNat 3).toNat
      omega
    · simp [δ,compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode]
    · simp [δ,α,compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode]; omega
  · exact step_push0 _ (fuel+3) 2 none
  change OpenRegionTrace originalCode candidateCode (fuel+1) (fuel+4) 0 (compilerZero originalCode s a b c tail) (compilerExit originalCode destination s a b c tail)
  apply OpenRegionTrace.extended (compilerZero originalCode s a b c tail) (compilerDupA originalCode s a b c tail) _ (fuel+2) 0 .DUP1 (none) .dup1
  · simp only [compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode,pc,pc_add,Nat.add_assoc]; exact originalDupADecoded
  · simp only [compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode,pc,pc_add,Nat.add_assoc]; exact candidateDupADecoded
  · constructor
    · change 3 ≤ (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5 - UInt256.ofNat 3 - UInt256.ofNat 3 - UInt256.ofNat 2).toNat
      omega
    · simp [δ,compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode]
    · simp [δ,α,compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode]; omega
  · exact step_dup1 _ (fuel+2) 3 none (UInt256.ofNat 0) (c :: (UInt256.add (UInt256.mul (UInt256.ofNat 32) a) b) :: tail) rfl
  change OpenRegionTrace originalCode candidateCode (fuel+1) (fuel+3) 0 (compilerDupA originalCode s a b c tail) (compilerExit originalCode destination s a b c tail)
  apply OpenRegionTrace.extended (compilerDupA originalCode s a b c tail) (compilerDupB originalCode s a b c tail) _ (fuel+1) 0 .DUP1 (none) .dup1
  · simp only [compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode,pc,pc_add,Nat.add_assoc]; exact originalDupBDecoded
  · simp only [compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode,pc,pc_add,Nat.add_assoc]; exact candidateDupBDecoded
  · constructor
    · change 3 ≤ (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5 - UInt256.ofNat 3 - UInt256.ofNat 3 - UInt256.ofNat 2 - UInt256.ofNat 3).toNat
      omega
    · simp [δ,compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode]
    · simp [δ,α,compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode]; omega
  · exact step_dup1 _ (fuel+1) 3 none (UInt256.ofNat 0) ((UInt256.ofNat 0) :: c :: (UInt256.add (UInt256.mul (UInt256.ofNat 32) a) b) :: tail) rfl
  change OpenRegionTrace originalCode candidateCode (fuel+1) (fuel+2) 0 (compilerDupB originalCode s a b c tail) (compilerExit originalCode destination s a b c tail)
  apply OpenRegionTrace.same (compilerDupB originalCode s a b c tail) (compilerExit originalCode destination s a b c tail) _ fuel 0 .PUSH2 (some (UInt256.ofNat destination,2)) (.push .PUSH2 (by decide))
  · simp only [compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode,pc,pc_add,Nat.add_assoc]; exact originalTargetDecoded
  · simp only [compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode,pc,pc_add,Nat.add_assoc]; exact candidateTargetDecoded
  · constructor
    · change 3 ≤ (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5 - UInt256.ofNat 3 - UInt256.ofNat 3 - UInt256.ofNat 2 - UInt256.ofNat 3 - UInt256.ofNat 3).toNat
      omega
    · simp [δ,compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode]
    · simp [δ,α,compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode]; omega
  · exact step_push _ .PUSH2 (UInt256.ofNat destination) 2 fuel 3 (by decide)
  exact OpenRegionTrace.done _

theorem compilerExitPC (originalCode : ByteArray) (entry destination : Nat) (s : EVM.State) (a b c : UInt256) (tail : List UInt256) (pc : s.pc = UInt256.ofNat entry) :
    (compilerExit originalCode destination s a b c tail).pc = UInt256.ofNat (entry+11) := by
  simp only [compilerPower,compilerAdd,compilerSwap,compilerZero,compilerDupA,compilerDupB,compilerExit,mulPowerPost,binaryPost,pushedWidth,withCode,pc,pc_add,Nat.add_assoc]


theorem compilerExitStack (originalCode : ByteArray) (destination : Nat) (s : EVM.State) (a b c : UInt256) (tail : List UInt256) :
    (compilerExit originalCode destination s a b c tail).stack =
      UInt256.ofNat destination :: UInt256.ofNat 0 :: UInt256.ofNat 0 :: UInt256.ofNat 0 :: c ::
        (UInt256.add (UInt256.mul (UInt256.ofNat 32) a) b) :: tail := rfl

theorem compilerExitGas (originalCode : ByteArray) (destination : Nat) (s : EVM.State) (a b c : UInt256) (tail : List UInt256)
    (gas : 25 ≤ s.gasAvailable.toNat) :
    (compilerExit originalCode destination s a b c tail).gasAvailable.toNat = s.gasAvailable.toNat - 25 := by
  have g1 := word_sub_toNat (s.gasAvailable) 3 (by decide) (by omega)
  have g2 := word_sub_toNat (s.gasAvailable - UInt256.ofNat 3) 5 (by decide) (by omega)
  have g3 := word_sub_toNat (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5) 3 (by decide) (by omega)
  have g4 := word_sub_toNat (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5 - UInt256.ofNat 3) 3 (by decide) (by omega)
  have g5 := word_sub_toNat (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5 - UInt256.ofNat 3 - UInt256.ofNat 3) 2 (by decide) (by omega)
  have g6 := word_sub_toNat (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5 - UInt256.ofNat 3 - UInt256.ofNat 3 - UInt256.ofNat 2) 3 (by decide) (by omega)
  have g7 := word_sub_toNat (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5 - UInt256.ofNat 3 - UInt256.ofNat 3 - UInt256.ofNat 2 - UInt256.ofNat 3) 3 (by decide) (by omega)
  have g8 := word_sub_toNat (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5 - UInt256.ofNat 3 - UInt256.ofNat 3 - UInt256.ofNat 2 - UInt256.ofNat 3 - UInt256.ofNat 3) 3 (by decide) (by omega)
  change (s.gasAvailable - UInt256.ofNat 3 - UInt256.ofNat 5 - UInt256.ofNat 3 - UInt256.ofNat 3 - UInt256.ofNat 2 - UInt256.ofNat 3 - UInt256.ofNat 3 - UInt256.ofNat 3).toNat = _
  omega

theorem compiler_region_boundary (originalCode candidateCode : ByteArray) (entry destination : Nat)
    (originalAddDecoded : decode originalCode (UInt256.ofNat (entry+3)) = some ((Operation.ADD : Operation .EVM), none))
    (originalSwapDecoded : decode originalCode (UInt256.ofNat (entry+4)) = some ((Operation.SWAP1 : Operation .EVM), none))
    (originalZeroDecoded : decode originalCode (UInt256.ofNat (entry+5)) = some ((Operation.PUSH0 : Operation .EVM), none))
    (originalDupADecoded : decode originalCode (UInt256.ofNat (entry+6)) = some ((Operation.DUP1 : Operation .EVM), none))
    (originalDupBDecoded : decode originalCode (UInt256.ofNat (entry+7)) = some ((Operation.DUP1 : Operation .EVM), none))
    (originalTargetDecoded : decode originalCode (UInt256.ofNat (entry+8)) = some ((Operation.Push .PUSH2 : Operation .EVM), some (UInt256.ofNat destination, 2)))
    (candidateAddDecoded : decode candidateCode (UInt256.ofNat (entry+3)) = some ((Operation.ADD : Operation .EVM), none))
    (candidateSwapDecoded : decode candidateCode (UInt256.ofNat (entry+4)) = some ((Operation.SWAP1 : Operation .EVM), none))
    (candidateZeroDecoded : decode candidateCode (UInt256.ofNat (entry+5)) = some ((Operation.PUSH0 : Operation .EVM), none))
    (candidateDupADecoded : decode candidateCode (UInt256.ofNat (entry+6)) = some ((Operation.DUP1 : Operation .EVM), none))
    (candidateDupBDecoded : decode candidateCode (UInt256.ofNat (entry+7)) = some ((Operation.DUP1 : Operation .EVM), none))
    (candidateTargetDecoded : decode candidateCode (UInt256.ofNat (entry+8)) = some ((Operation.Push .PUSH2 : Operation .EVM), some (UInt256.ofNat destination, 2)))
    (originalSite : MulPowerAt originalCode (UInt256.ofNat entry) .PUSH1 1 5)
    (candidateSite : ShiftPowerAt candidateCode (UInt256.ofNat entry) .PUSH1 1 5)
    (originalJumpDecoded : decode originalCode (UInt256.ofNat (entry+11)) = some ((Operation.JUMP : Operation .EVM), none))
    (candidateJumpDecoded : decode candidateCode (UInt256.ofNat (entry+11)) = some ((Operation.JUMP : Operation .EVM), none))
    (owner : AccountAddress) (s t : EVM.State)
    (a b c : UInt256) (tail : List UInt256) (fuel surplus : Nat)
    (oldJumps newJumps : Array UInt256)
    (related : DeployedFrameWithGas owner originalCode candidateCode surplus s t)
    (pc : s.pc = UInt256.ofNat entry) (stack : s.stack = a :: b :: c :: tail)
    (gas : 25 ≤ s.gasAvailable.toNat) (peak : tail.length + 6 ≤ 1024) :
    ∃ candidateExit : EVM.State,
      X (fuel+9) oldJumps s = X (fuel+1) oldJumps (compilerExit originalCode destination s a b c tail) ∧
      X (fuel+9) newJumps t = X (fuel+1) newJumps candidateExit ∧
      DeployedFrameWithGas owner originalCode candidateCode (surplus+2) (compilerExit originalCode destination s a b c tail) candidateExit ∧
      (compilerExit originalCode destination s a b c tail).pc = UInt256.ofNat (entry+11) ∧
      candidateExit.pc = UInt256.ofNat (entry+11) ∧
      decode originalCode (compilerExit originalCode destination s a b c tail).pc = some (.JUMP,none) ∧
      decode candidateCode candidateExit.pc = some (.JUMP,none) := by
  obtain ⟨ce, sourceRun, targetRun, exitRelation⟩ := open_region_simulation owner originalCode candidateCode
    (fuel+9) (fuel+1) 1 s t (compilerExit originalCode destination s a b c tail) surplus oldJumps newJumps
    (compilerTrace originalCode candidateCode entry destination originalAddDecoded originalSwapDecoded originalZeroDecoded originalDupADecoded originalDupBDecoded originalTargetDecoded candidateAddDecoded candidateSwapDecoded candidateZeroDecoded candidateDupADecoded candidateDupBDecoded candidateTargetDecoded originalSite candidateSite s a b c tail fuel pc stack gas peak) related
  have epc := compilerExitPC originalCode entry destination s a b c tail pc
  have cpc := (deployed_frame_pc exitRelation).symm.trans epc
  exact ⟨ce,sourceRun,targetRun,exitRelation,epc,cpc,
    by rw [epc]; exact originalJumpDecoded,
    by rw [cpc]; exact candidateJumpDecoded⟩

#print axioms pc_add
#print axioms compilerExitPC
#print axioms compilerExitStack
#print axioms compilerExitGas
#print axioms compilerTrace
#print axioms compiler_region_boundary
end GolfPowerRegion
