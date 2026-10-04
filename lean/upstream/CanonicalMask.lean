import MaskSupport
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfUpstream GolfCountOffset
namespace CanonicalMaskWindow

def one : UInt256 := UInt256.ofNat 1
def shift : UInt256 := UInt256.ofNat 224
def power : UInt256 := UInt256.shiftLeft one shift
def low : UInt256 := UInt256.sub power one
def high : UInt256 := UInt256.lnot low
def narrow : UInt256 := UInt256.ofNat 4294967295

theorem mask_identity : UInt256.shiftLeft narrow shift = high := by decide

def finalStack (a : UInt256) (tail : List UInt256) := high :: (low &&& a) :: tail

theorem snapshot_gas (s : EVM.State) (stack : List UInt256) (bytes steps : Nat)
 (enough : 3*(steps+1) ≤ s.gasAvailable.toNat) :
 3 ≤ (snapshot s stack bytes steps).gasAvailable.toNat := by
 change 3 ≤ (spend s.gasAvailable steps).toNat
 rw [spend_nat _ _ (by omega)]
 omega

structure BeforeDecoded (s : EVM.State) : Prop where
 d0 : decode s.executionEnv.code (s.pc + UInt256.ofNat 0) = some (.Push .PUSH1,some (one,1))
 d1 : decode s.executionEnv.code (s.pc + UInt256.ofNat 2) = some (.Push .PUSH1,some (one,1))
 d2 : decode s.executionEnv.code (s.pc + UInt256.ofNat 4) = some (.Push .PUSH1,some (shift,1))
 d3 : decode s.executionEnv.code (s.pc + UInt256.ofNat 6) = some (.SHL,none)
 d4 : decode s.executionEnv.code (s.pc + UInt256.ofNat 7) = some (.SUB,none)
 d5 : decode s.executionEnv.code (s.pc + UInt256.ofNat 8) = some (.AND,none)
 d6 : decode s.executionEnv.code (s.pc + UInt256.ofNat 9) = some (.Push .PUSH1,some (one,1))
 d7 : decode s.executionEnv.code (s.pc + UInt256.ofNat 11) = some (.Push .PUSH1,some (one,1))
 d8 : decode s.executionEnv.code (s.pc + UInt256.ofNat 13) = some (.Push .PUSH1,some (shift,1))
 d9 : decode s.executionEnv.code (s.pc + UInt256.ofNat 15) = some (.SHL,none)
 d10 : decode s.executionEnv.code (s.pc + UInt256.ofNat 16) = some (.SUB,none)
 d11 : decode s.executionEnv.code (s.pc + UInt256.ofNat 17) = some (.NOT,none)

theorem before_step0 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : BeforeDecoded s)
 (gas : 36 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s (a :: tail) 0 0) =
 X (fuel+1) jumps (snapshot s (one :: a :: tail) 2 1) := by
 have h := X_push_width (snapshot s (a :: tail) 0 0) .PUSH1 one 1 fuel jumps
   (by decide) decoded.d0 (snapshot_gas s _ 0 0 (by omega))
   (by simp [snapshot]; omega)
 simpa only [snapshot_push] using h
theorem before_step1 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : BeforeDecoded s)
 (gas : 36 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s (one :: a :: tail) 2 1) =
 X (fuel+1) jumps (snapshot s (one :: one :: a :: tail) 4 2) := by
 have h := X_push_width (snapshot s (one :: a :: tail) 2 1) .PUSH1 one 1 fuel jumps
   (by decide) decoded.d1 (snapshot_gas s _ 2 1 (by omega))
   (by simp [snapshot]; omega)
 simpa only [snapshot_push] using h
theorem before_step2 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : BeforeDecoded s)
 (gas : 36 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s (one :: one :: a :: tail) 4 2) =
 X (fuel+1) jumps (snapshot s (shift :: one :: one :: a :: tail) 6 3) := by
 have h := X_push_width (snapshot s (one :: one :: a :: tail) 4 2) .PUSH1 shift 1 fuel jumps
   (by decide) decoded.d2 (snapshot_gas s _ 4 2 (by omega))
   (by simp [snapshot]; omega)
 simpa only [snapshot_push] using h
theorem before_step3 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : BeforeDecoded s)
 (gas : 36 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s (shift :: one :: one :: a :: tail) 6 3) =
 X (fuel+1) jumps (snapshot s (power :: one :: a :: tail) 7 4) := by
 have h := X_next (snapshot s (shift :: one :: one :: a :: tail) 6 3)
   (binaryPost (snapshot s (shift :: one :: one :: a :: tail) 6 3) (UInt256.shiftLeft one shift) (one :: a :: tail) 3)
   fuel jumps .SHL none .shl decoded.d3
   ⟨snapshot_gas s _ 6 3 (by omega),by simp [δ,snapshot],by simp [δ,α,snapshot]; omega⟩
   (GolfUpstream.step_shl _ fuel 3 none one shift (one :: a :: tail) rfl)
 simpa only [snapshot_binary,mask_identity] using h
theorem before_step4 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : BeforeDecoded s)
 (gas : 36 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s (power :: one :: a :: tail) 7 4) =
 X (fuel+1) jumps (snapshot s (low :: a :: tail) 8 5) := by
 have h := X_next_extra (snapshot s (power :: one :: a :: tail) 7 4)
   (binaryPost (snapshot s (power :: one :: a :: tail) 7 4) (UInt256.sub power one) (a :: tail) 3)
   fuel jumps .SUB none .sub decoded.d4
   ⟨snapshot_gas s _ 7 4 (by omega),by simp [δ,snapshot],by simp [δ,α,snapshot]; omega⟩
   (GolfCountOffset.step_sub _ fuel 3 none one power (a :: tail) rfl)
 simpa only [snapshot_binary,mask_identity] using h
theorem before_step5 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : BeforeDecoded s)
 (gas : 36 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s (low :: a :: tail) 8 5) =
 X (fuel+1) jumps (snapshot s ((low &&& a) :: tail) 9 6) := by
 have h := X_next_extra (snapshot s (low :: a :: tail) 8 5)
   (binaryPost (snapshot s (low :: a :: tail) 8 5) (low &&& a) (tail) 3)
   fuel jumps .AND none .and decoded.d5
   ⟨snapshot_gas s _ 8 5 (by omega),by simp [δ,snapshot],by simp [δ,α,snapshot]; omega⟩
   (GolfCountOffset.step_and _ fuel 3 none a low (tail) rfl)
 simpa only [snapshot_binary,mask_identity] using h
theorem before_step6 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : BeforeDecoded s)
 (gas : 36 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s ((low &&& a) :: tail) 9 6) =
 X (fuel+1) jumps (snapshot s (one :: (low &&& a) :: tail) 11 7) := by
 have h := X_push_width (snapshot s ((low &&& a) :: tail) 9 6) .PUSH1 one 1 fuel jumps
   (by decide) decoded.d6 (snapshot_gas s _ 9 6 (by omega))
   (by simp [snapshot]; omega)
 simpa only [snapshot_push] using h
theorem before_step7 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : BeforeDecoded s)
 (gas : 36 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s (one :: (low &&& a) :: tail) 11 7) =
 X (fuel+1) jumps (snapshot s (one :: one :: (low &&& a) :: tail) 13 8) := by
 have h := X_push_width (snapshot s (one :: (low &&& a) :: tail) 11 7) .PUSH1 one 1 fuel jumps
   (by decide) decoded.d7 (snapshot_gas s _ 11 7 (by omega))
   (by simp [snapshot]; omega)
 simpa only [snapshot_push] using h
theorem before_step8 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : BeforeDecoded s)
 (gas : 36 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s (one :: one :: (low &&& a) :: tail) 13 8) =
 X (fuel+1) jumps (snapshot s (shift :: one :: one :: (low &&& a) :: tail) 15 9) := by
 have h := X_push_width (snapshot s (one :: one :: (low &&& a) :: tail) 13 8) .PUSH1 shift 1 fuel jumps
   (by decide) decoded.d8 (snapshot_gas s _ 13 8 (by omega))
   (by simp [snapshot]; omega)
 simpa only [snapshot_push] using h
theorem before_step9 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : BeforeDecoded s)
 (gas : 36 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s (shift :: one :: one :: (low &&& a) :: tail) 15 9) =
 X (fuel+1) jumps (snapshot s (power :: one :: (low &&& a) :: tail) 16 10) := by
 have h := X_next (snapshot s (shift :: one :: one :: (low &&& a) :: tail) 15 9)
   (binaryPost (snapshot s (shift :: one :: one :: (low &&& a) :: tail) 15 9) (UInt256.shiftLeft one shift) (one :: (low &&& a) :: tail) 3)
   fuel jumps .SHL none .shl decoded.d9
   ⟨snapshot_gas s _ 15 9 (by omega),by simp [δ,snapshot],by simp [δ,α,snapshot]; omega⟩
   (GolfUpstream.step_shl _ fuel 3 none one shift (one :: (low &&& a) :: tail) rfl)
 simpa only [snapshot_binary,mask_identity] using h
theorem before_step10 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : BeforeDecoded s)
 (gas : 36 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s (power :: one :: (low &&& a) :: tail) 16 10) =
 X (fuel+1) jumps (snapshot s (low :: (low &&& a) :: tail) 17 11) := by
 have h := X_next_extra (snapshot s (power :: one :: (low &&& a) :: tail) 16 10)
   (binaryPost (snapshot s (power :: one :: (low &&& a) :: tail) 16 10) (UInt256.sub power one) ((low &&& a) :: tail) 3)
   fuel jumps .SUB none .sub decoded.d10
   ⟨snapshot_gas s _ 16 10 (by omega),by simp [δ,snapshot],by simp [δ,α,snapshot]; omega⟩
   (GolfCountOffset.step_sub _ fuel 3 none one power ((low &&& a) :: tail) rfl)
 simpa only [snapshot_binary,mask_identity] using h
theorem before_step11 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : BeforeDecoded s)
 (gas : 36 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s (low :: (low &&& a) :: tail) 17 11) =
 X (fuel+1) jumps (snapshot s (high :: (low &&& a) :: tail) 18 12) := by
 have h := X_next_extra (snapshot s (low :: (low &&& a) :: tail) 17 11)
   (binaryPost (snapshot s (low :: (low &&& a) :: tail) 17 11) (UInt256.lnot low) ((low &&& a) :: tail) 3)
   fuel jumps .NOT none .not decoded.d11
   ⟨snapshot_gas s _ 17 11 (by omega),by simp [δ,snapshot],by simp [δ,α,snapshot]; omega⟩
   (GolfCountOffset.step_not _ fuel 3 none low ((low &&& a) :: tail) rfl)
 simpa only [snapshot_binary,mask_identity] using h

theorem before_execution (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : BeforeDecoded s)
 (stack : s.stack = a::tail) (gas : 36 ≤ s.gasAvailable.toNat)
 (height : tail.length ≤ 1020) :
 X (fuel+13) jumps s =
 X (fuel+1) jumps (snapshot s (finalStack a tail) 18 12) := by
 have start : snapshot s (a::tail) 0 0 = s := by rw [←stack,snapshot_zero]
 have h0 := before_step0 s a tail (fuel+11) jumps decoded gas height
 have h1 := before_step1 s a tail (fuel+10) jumps decoded gas height
 have h2 := before_step2 s a tail (fuel+9) jumps decoded gas height
 have h3 := before_step3 s a tail (fuel+8) jumps decoded gas height
 have h4 := before_step4 s a tail (fuel+7) jumps decoded gas height
 have h5 := before_step5 s a tail (fuel+6) jumps decoded gas height
 have h6 := before_step6 s a tail (fuel+5) jumps decoded gas height
 have h7 := before_step7 s a tail (fuel+4) jumps decoded gas height
 have h8 := before_step8 s a tail (fuel+3) jumps decoded gas height
 have h9 := before_step9 s a tail (fuel+2) jumps decoded gas height
 have h10 := before_step10 s a tail (fuel+1) jumps decoded gas height
 have h11 := before_step11 s a tail (fuel+0) jumps decoded gas height
 simpa only [Nat.add_assoc,Nat.add_zero,finalStack,start] using
  h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans (h9.trans (h10.trans (h11)))))))))))
#print axioms before_execution

structure AfterDecoded (s : EVM.State) : Prop where
 d0 : decode s.executionEnv.code (s.pc + UInt256.ofNat 0) = some (.Push .PUSH1,some (one,1))
 d1 : decode s.executionEnv.code (s.pc + UInt256.ofNat 2) = some (.Push .PUSH1,some (one,1))
 d2 : decode s.executionEnv.code (s.pc + UInt256.ofNat 4) = some (.Push .PUSH1,some (shift,1))
 d3 : decode s.executionEnv.code (s.pc + UInt256.ofNat 6) = some (.SHL,none)
 d4 : decode s.executionEnv.code (s.pc + UInt256.ofNat 7) = some (.SUB,none)
 d5 : decode s.executionEnv.code (s.pc + UInt256.ofNat 8) = some (.AND,none)
 d6 : decode s.executionEnv.code (s.pc + UInt256.ofNat 9) = some (.Push .PUSH5,some (narrow,5))
 d7 : decode s.executionEnv.code (s.pc + UInt256.ofNat 15) = some (.Push .PUSH1,some (shift,1))
 d8 : decode s.executionEnv.code (s.pc + UInt256.ofNat 17) = some (.SHL,none)

theorem after_step0 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : AfterDecoded s)
 (gas : 27 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s (a :: tail) 0 0) =
 X (fuel+1) jumps (snapshot s (one :: a :: tail) 2 1) := by
 have h := X_push_width (snapshot s (a :: tail) 0 0) .PUSH1 one 1 fuel jumps
   (by decide) decoded.d0 (snapshot_gas s _ 0 0 (by omega))
   (by simp [snapshot]; omega)
 simpa only [snapshot_push] using h
theorem after_step1 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : AfterDecoded s)
 (gas : 27 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s (one :: a :: tail) 2 1) =
 X (fuel+1) jumps (snapshot s (one :: one :: a :: tail) 4 2) := by
 have h := X_push_width (snapshot s (one :: a :: tail) 2 1) .PUSH1 one 1 fuel jumps
   (by decide) decoded.d1 (snapshot_gas s _ 2 1 (by omega))
   (by simp [snapshot]; omega)
 simpa only [snapshot_push] using h
theorem after_step2 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : AfterDecoded s)
 (gas : 27 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s (one :: one :: a :: tail) 4 2) =
 X (fuel+1) jumps (snapshot s (shift :: one :: one :: a :: tail) 6 3) := by
 have h := X_push_width (snapshot s (one :: one :: a :: tail) 4 2) .PUSH1 shift 1 fuel jumps
   (by decide) decoded.d2 (snapshot_gas s _ 4 2 (by omega))
   (by simp [snapshot]; omega)
 simpa only [snapshot_push] using h
theorem after_step3 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : AfterDecoded s)
 (gas : 27 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s (shift :: one :: one :: a :: tail) 6 3) =
 X (fuel+1) jumps (snapshot s (power :: one :: a :: tail) 7 4) := by
 have h := X_next (snapshot s (shift :: one :: one :: a :: tail) 6 3)
   (binaryPost (snapshot s (shift :: one :: one :: a :: tail) 6 3) (UInt256.shiftLeft one shift) (one :: a :: tail) 3)
   fuel jumps .SHL none .shl decoded.d3
   ⟨snapshot_gas s _ 6 3 (by omega),by simp [δ,snapshot],by simp [δ,α,snapshot]; omega⟩
   (GolfUpstream.step_shl _ fuel 3 none one shift (one :: a :: tail) rfl)
 simpa only [snapshot_binary,mask_identity] using h
theorem after_step4 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : AfterDecoded s)
 (gas : 27 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s (power :: one :: a :: tail) 7 4) =
 X (fuel+1) jumps (snapshot s (low :: a :: tail) 8 5) := by
 have h := X_next_extra (snapshot s (power :: one :: a :: tail) 7 4)
   (binaryPost (snapshot s (power :: one :: a :: tail) 7 4) (UInt256.sub power one) (a :: tail) 3)
   fuel jumps .SUB none .sub decoded.d4
   ⟨snapshot_gas s _ 7 4 (by omega),by simp [δ,snapshot],by simp [δ,α,snapshot]; omega⟩
   (GolfCountOffset.step_sub _ fuel 3 none one power (a :: tail) rfl)
 simpa only [snapshot_binary,mask_identity] using h
theorem after_step5 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : AfterDecoded s)
 (gas : 27 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s (low :: a :: tail) 8 5) =
 X (fuel+1) jumps (snapshot s ((low &&& a) :: tail) 9 6) := by
 have h := X_next_extra (snapshot s (low :: a :: tail) 8 5)
   (binaryPost (snapshot s (low :: a :: tail) 8 5) (low &&& a) (tail) 3)
   fuel jumps .AND none .and decoded.d5
   ⟨snapshot_gas s _ 8 5 (by omega),by simp [δ,snapshot],by simp [δ,α,snapshot]; omega⟩
   (GolfCountOffset.step_and _ fuel 3 none a low (tail) rfl)
 simpa only [snapshot_binary,mask_identity] using h
theorem after_step6 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : AfterDecoded s)
 (gas : 27 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s ((low &&& a) :: tail) 9 6) =
 X (fuel+1) jumps (snapshot s (narrow :: (low &&& a) :: tail) 15 7) := by
 have h := X_push_width (snapshot s ((low &&& a) :: tail) 9 6) .PUSH5 narrow 5 fuel jumps
   (by decide) decoded.d6 (snapshot_gas s _ 9 6 (by omega))
   (by simp [snapshot]; omega)
 simpa only [snapshot_push] using h
theorem after_step7 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : AfterDecoded s)
 (gas : 27 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s (narrow :: (low &&& a) :: tail) 15 7) =
 X (fuel+1) jumps (snapshot s (shift :: narrow :: (low &&& a) :: tail) 17 8) := by
 have h := X_push_width (snapshot s (narrow :: (low &&& a) :: tail) 15 7) .PUSH1 shift 1 fuel jumps
   (by decide) decoded.d7 (snapshot_gas s _ 15 7 (by omega))
   (by simp [snapshot]; omega)
 simpa only [snapshot_push] using h
theorem after_step8 (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : AfterDecoded s)
 (gas : 27 ≤ s.gasAvailable.toNat) (height : tail.length ≤ 1020) :
 X (fuel+2) jumps (snapshot s (shift :: narrow :: (low &&& a) :: tail) 17 8) =
 X (fuel+1) jumps (snapshot s (high :: (low &&& a) :: tail) 18 9) := by
 have h := X_next (snapshot s (shift :: narrow :: (low &&& a) :: tail) 17 8)
   (binaryPost (snapshot s (shift :: narrow :: (low &&& a) :: tail) 17 8) (UInt256.shiftLeft narrow shift) ((low &&& a) :: tail) 3)
   fuel jumps .SHL none .shl decoded.d8
   ⟨snapshot_gas s _ 17 8 (by omega),by simp [δ,snapshot],by simp [δ,α,snapshot]; omega⟩
   (GolfUpstream.step_shl _ fuel 3 none narrow shift ((low &&& a) :: tail) rfl)
 simpa only [snapshot_binary,mask_identity] using h

theorem after_execution (s : EVM.State) (a : UInt256) (tail : List UInt256)
 (fuel : Nat) (jumps : Array UInt256) (decoded : AfterDecoded s)
 (stack : s.stack = a::tail) (gas : 27 ≤ s.gasAvailable.toNat)
 (height : tail.length ≤ 1020) :
 X (fuel+10) jumps s =
 X (fuel+1) jumps (snapshot s (finalStack a tail) 18 9) := by
 have start : snapshot s (a::tail) 0 0 = s := by rw [←stack,snapshot_zero]
 have h0 := after_step0 s a tail (fuel+8) jumps decoded gas height
 have h1 := after_step1 s a tail (fuel+7) jumps decoded gas height
 have h2 := after_step2 s a tail (fuel+6) jumps decoded gas height
 have h3 := after_step3 s a tail (fuel+5) jumps decoded gas height
 have h4 := after_step4 s a tail (fuel+4) jumps decoded gas height
 have h5 := after_step5 s a tail (fuel+3) jumps decoded gas height
 have h6 := after_step6 s a tail (fuel+2) jumps decoded gas height
 have h7 := after_step7 s a tail (fuel+1) jumps decoded gas height
 have h8 := after_step8 s a tail (fuel+0) jumps decoded gas height
 simpa only [Nat.add_assoc,Nat.add_zero,finalStack,start] using
  h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8))))))))
#print axioms after_execution

theorem final_relation {owner old new surplus skipped s t}
 (related : DeployedOffset owner old new surplus skipped s t)
 (a : UInt256) (tail : List UInt256) (gas : 36 ≤ s.gasAvailable.toNat) :
 DeployedOffset owner old new (surplus+9) (skipped+3)
   (snapshot s (finalStack a tail) 18 12) (snapshot t (finalStack a tail) 18 9) := by
 refine ⟨?_,?_,?_,related.maps⟩
 · have h := congrArg (fun st : EVM.State =>
     {st with stack := finalStack a tail,pc := st.pc + UInt256.ofNat 18}) related.frame
   simpa only [snapshot,eraseCount,deployedFrame,eraseMaps,eraseCodeGas] using h
 · change s.execLength+12 = (t.execLength+9)+(skipped+3)
   have h := related.count
   omega
 · change (spend t.gasAvailable 9).toNat = (spend s.gasAvailable 12).toNat + (surplus+9)
   have hgas := related.gas
   rw [spend_nat _ 9 (by omega),spend_nat _ 12 gas]
   omega

-- Entry is the certified window start. This leaves both suffix calls unevaluated.
-- Fuel budgets intentionally differ by the three eliminated instructions.
theorem canonical_mask_replacement {owner old new surplus skipped s t}
 (related : DeployedOffset owner old new surplus skipped s t)
 (a : UInt256) (tail : List UInt256) (fuel : Nat)
 (oldJumps newJumps : Array UInt256)
 (beforeCode : BeforeDecoded s) (afterCode : AfterDecoded t)
 (stack : s.stack = a::tail) (gas : 36 ≤ s.gasAvailable.toNat)
 (height : tail.length ≤ 1020) :
 X (fuel+13) oldJumps s = X (fuel+1) oldJumps (snapshot s (finalStack a tail) 18 12) ∧
 X (fuel+10) newJumps t = X (fuel+1) newJumps (snapshot t (finalStack a tail) 18 9) ∧
 DeployedOffset owner old new (surplus+9) (skipped+3)
   (snapshot s (finalStack a tail) 18 12) (snapshot t (finalStack a tail) 18 9) := by
 have sameStack := congrArg EVM.State.stack related.frame
 change s.stack = t.stack at sameStack
 have candidateStack : t.stack = a::tail := sameStack.symm.trans stack
 have hgas := related.gas
 exact ⟨before_execution s a tail fuel oldJumps beforeCode stack gas height,
   after_execution t a tail fuel newJumps afterCode candidateStack (by omega) height,
   final_relation related a tail gas⟩

#print axioms canonical_mask_replacement

#print axioms mask_identity
#print axioms final_relation
end CanonicalMaskWindow
