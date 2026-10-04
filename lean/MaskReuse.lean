/-! Exact fixed-length reuse of 128-bit and 160-bit masks, including every input stack height. -/
namespace GolfMaskReuse
def before7 : List Nat := [96, 1, 96, 1, 96, 160, 27, 3, 22, 134, 96, 1, 96, 1, 96, 160, 27, 3, 22]
def after7 : List Nat := [99, 0, 0, 0, 1, 96, 1, 96, 160, 95, 80, 27, 3, 128, 145, 22, 144, 135, 22]
def mask7 : Golf.Word := BitVec.ofNat 256 (2^160-1)
def output7 (a b c d e f g : Golf.Word) (tail : List Golf.Word) := (mask7 &&& g) :: (mask7 &&& a) :: b::c::d::e::f::g::tail
theorem before7_output (a b c d e f g x y : Golf.Word) (tail : List Golf.Word) :
 Golf.run 20 before7 (a::b::c::d::e::f::g::tail) x y = some (output7 a b c d e f g tail) := by
 rfl
theorem after7_output (a b c d e f g x y : Golf.Word) (tail : List Golf.Word) :
 Golf.run 20 after7 (a::b::c::d::e::f::g::tail) x y = some (output7 a b c d e f g tail) := by
 change some ((g &&& mask7) :: (a &&& mask7) :: b::c::d::e::f::g::tail) = some ((mask7 &&& g) :: (mask7 &&& a) :: b::c::d::e::f::g::tail)
 rw [BitVec.and_comm g mask7, BitVec.and_comm a mask7]
def before2 : List Nat := [96, 1, 96, 1, 96, 128, 27, 3, 22, 129, 96, 1, 96, 1, 96, 128, 27, 3, 22]
def after2 : List Nat := [99, 0, 0, 0, 1, 96, 1, 96, 128, 95, 80, 27, 3, 128, 145, 22, 144, 130, 22]
def mask2 : Golf.Word := BitVec.ofNat 256 (2^128-1)
def output2 (a b : Golf.Word) (tail : List Golf.Word) := (mask2 &&& b) :: (mask2 &&& a) :: b::tail
theorem before2_output (a b x y : Golf.Word) (tail : List Golf.Word) :
 Golf.run 20 before2 (a::b::tail) x y = some (output2 a b tail) := by
 rfl
theorem after2_output (a b x y : Golf.Word) (tail : List Golf.Word) :
 Golf.run 20 after2 (a::b::tail) x y = some (output2 a b tail) := by
 change some ((b &&& mask2) :: (a &&& mask2) :: b::tail) = some ((mask2 &&& b) :: (mask2 &&& a) :: b::tail)
 rw [BitVec.and_comm b mask2, BitVec.and_comm a mask2]
theorem before2_success (a b x y : Golf.Word) (tail : List Golf.Word) (height : tail.length ≤ 1018) :
 GolfBounded.run 20 before2 (a :: b :: tail) x y = some (output2 a b tail) := by
 unfold before2
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: a :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 128) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 340282366920938463463374607431768211456) :: (BitVec.ofNat 256 1) :: a :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 340282366920938463463374607431768211455) :: a :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := (((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& a) :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := (b :: ((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& a) :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: b :: ((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& a) :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: b :: ((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& a) :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 128) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: b :: ((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& a) :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 340282366920938463463374607431768211456) :: (BitVec.ofNat 256 1) :: b :: ((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& a) :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 340282366920938463463374607431768211455) :: b :: ((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& a) :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := (((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& b) :: ((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& a) :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.empty_success
 simp only [List.length_cons]
 omega
theorem after2_success (a b x y : Golf.Word) (tail : List Golf.Word) (height : tail.length ≤ 1018) :
 GolfBounded.run 20 after2 (a :: b :: tail) x y = some (output2 a b tail) := by
 unfold after2
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: a :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 128) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 0) :: (BitVec.ofNat 256 128) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 128) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 340282366920938463463374607431768211456) :: (BitVec.ofNat 256 1) :: a :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 340282366920938463463374607431768211455) :: a :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 340282366920938463463374607431768211455) :: (BitVec.ofNat 256 340282366920938463463374607431768211455) :: a :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := (a :: (BitVec.ofNat 256 340282366920938463463374607431768211455) :: (BitVec.ofNat 256 340282366920938463463374607431768211455) :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := (((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& a) :: (BitVec.ofNat 256 340282366920938463463374607431768211455) :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by change some ((a &&& (BitVec.ofNat 256 340282366920938463463374607431768211455)) :: (BitVec.ofNat 256 340282366920938463463374607431768211455) :: b :: tail) = some (((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& a) :: (BitVec.ofNat 256 340282366920938463463374607431768211455) :: b :: tail); rw [BitVec.and_comm a (BitVec.ofNat 256 340282366920938463463374607431768211455)])
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 340282366920938463463374607431768211455) :: ((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& a) :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := (b :: (BitVec.ofNat 256 340282366920938463463374607431768211455) :: ((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& a) :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := (((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& b) :: ((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& a) :: b :: tail)) (height := by simp only [List.length_cons]; omega) (step := by change some ((b &&& (BitVec.ofNat 256 340282366920938463463374607431768211455)) :: ((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& a) :: b :: tail) = some (((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& b) :: ((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& a) :: b :: tail); rw [BitVec.and_comm b (BitVec.ofNat 256 340282366920938463463374607431768211455)])
 apply GolfBounded.empty_success
 simp only [List.length_cons]
 omega
theorem before7_success (a b c d e f g x y : Golf.Word) (tail : List Golf.Word) (height : tail.length ≤ 1013) :
 GolfBounded.run 20 before7 (a :: b :: c :: d :: e :: f :: g :: tail) x y = some (output7 a b c d e f g tail) := by
 unfold before7
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: a :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 160) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542976) :: (BitVec.ofNat 256 1) :: a :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) :: a :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := (((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := (g :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: g :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: g :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 160) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: g :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542976) :: (BitVec.ofNat 256 1) :: g :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) :: g :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := (((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& g) :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.empty_success
 simp only [List.length_cons]
 omega
theorem after7_success (a b c d e f g x y : Golf.Word) (tail : List Golf.Word) (height : tail.length ≤ 1013) :
 GolfBounded.run 20 after7 (a :: b :: c :: d :: e :: f :: g :: tail) x y = some (output7 a b c d e f g tail) := by
 unfold after7
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: a :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 160) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 0) :: (BitVec.ofNat 256 160) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 160) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542976) :: (BitVec.ofNat 256 1) :: a :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) :: a :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) :: (BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) :: a :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := (a :: (BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) :: (BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := (((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: (BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by change some ((a &&& (BitVec.ofNat 256 1461501637330902918203684832716283019655932542975)) :: (BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) :: b :: c :: d :: e :: f :: g :: tail) = some (((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: (BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) :: b :: c :: d :: e :: f :: g :: tail); rw [BitVec.and_comm a (BitVec.ofNat 256 1461501637330902918203684832716283019655932542975)])
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := (g :: (BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := (((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& g) :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: b :: c :: d :: e :: f :: g :: tail)) (height := by simp only [List.length_cons]; omega) (step := by change some ((g &&& (BitVec.ofNat 256 1461501637330902918203684832716283019655932542975)) :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: b :: c :: d :: e :: f :: g :: tail) = some (((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& g) :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: b :: c :: d :: e :: f :: g :: tail); rw [BitVec.and_comm g (BitVec.ofNat 256 1461501637330902918203684832716283019655932542975)])
 apply GolfBounded.empty_success
 simp only [List.length_cons]
 omega
theorem underflow2 (stack : List Golf.Word) (x y : Golf.Word) (height : stack.length < 2) :
 GolfBounded.run 20 before2 stack x y = none ∧ GolfBounded.run 20 after2 stack x y = none := by
 cases stack with
 | nil => exact ⟨rfl,rfl⟩
 | cons a0 tail0 =>
   cases tail0 with
   | nil => exact ⟨rfl,rfl⟩
   | cons a1 tail1 =>
     simp only [List.length_cons] at height
     omega
theorem underflow7 (stack : List Golf.Word) (x y : Golf.Word) (height : stack.length < 7) :
 GolfBounded.run 20 before7 stack x y = none ∧ GolfBounded.run 20 after7 stack x y = none := by
 cases stack with
 | nil => exact ⟨rfl,rfl⟩
 | cons a0 tail0 =>
   cases tail0 with
   | nil => exact ⟨rfl,rfl⟩
   | cons a1 tail1 =>
     cases tail1 with
     | nil => exact ⟨rfl,rfl⟩
     | cons a2 tail2 =>
       cases tail2 with
       | nil => exact ⟨rfl,rfl⟩
       | cons a3 tail3 =>
         cases tail3 with
         | nil => exact ⟨rfl,rfl⟩
         | cons a4 tail4 =>
           cases tail4 with
           | nil => exact ⟨rfl,rfl⟩
           | cons a5 tail5 =>
             cases tail5 with
             | nil => exact ⟨rfl,rfl⟩
             | cons a6 tail6 =>
               simp only [List.length_cons] at height
               omega

theorem before2_overflow (a b x y : Golf.Word) (tail : List Golf.Word) (height : 1021 ≤ (a::b::tail).length) :
 GolfBounded.run 20 before2 (a::b::tail) x y = none := by
 unfold before2
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1) :: a :: b :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 128) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 340282366920938463463374607431768211456) :: (BitVec.ofNat 256 1) :: a :: b :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 340282366920938463463374607431768211455) :: a :: b :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := (((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& a) :: b :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := (b :: ((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& a) :: b :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1) :: b :: ((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& a) :: b :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: b :: ((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& a) :: b :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 128) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: b :: ((BitVec.ofNat 256 340282366920938463463374607431768211455) &&& a) :: b :: tail)) (step := by rfl)
 apply GolfBounded.overflow_failure
 simp only [List.length_cons] at *
 omega
theorem after2_overflow (a b x y : Golf.Word) (tail : List Golf.Word) (height : 1021 ≤ (a::b::tail).length) :
 GolfBounded.run 20 after2 (a::b::tail) x y = none := by
 unfold after2
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1) :: a :: b :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 128) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 0) :: (BitVec.ofNat 256 128) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: tail)) (step := by rfl)
 apply GolfBounded.overflow_failure
 simp only [List.length_cons] at *
 omega
theorem all_height2 (stack : List Golf.Word) (x y : Golf.Word) :
 GolfBounded.run 20 before2 stack x y = GolfBounded.run 20 after2 stack x y := by
 cases stack with
 | nil => rfl
 | cons a tail0 =>
   cases tail0 with
   | nil => rfl
   | cons b tail =>
     by_cases good : tail.length ≤ 1018
     · rw [before2_success a b x y tail good, after2_success a b x y tail good]
     · have high : 1021 ≤ (a::b::tail).length := by simp only [List.length_cons]; omega
       rw [before2_overflow a b x y tail high, after2_overflow a b x y tail high]
theorem before7_overflow (a b c d e f g x y : Golf.Word) (tail : List Golf.Word) (height : 1021 ≤ (a::b::c::d::e::f::g::tail).length) :
 GolfBounded.run 20 before7 (a::b::c::d::e::f::g::tail) x y = none := by
 unfold before7
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1) :: a :: b :: c :: d :: e :: f :: g :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: c :: d :: e :: f :: g :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 160) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: c :: d :: e :: f :: g :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542976) :: (BitVec.ofNat 256 1) :: a :: b :: c :: d :: e :: f :: g :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) :: a :: b :: c :: d :: e :: f :: g :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := (((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: b :: c :: d :: e :: f :: g :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := (g :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: b :: c :: d :: e :: f :: g :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1) :: g :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: b :: c :: d :: e :: f :: g :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: g :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: b :: c :: d :: e :: f :: g :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 160) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: g :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: b :: c :: d :: e :: f :: g :: tail)) (step := by rfl)
 apply GolfBounded.overflow_failure
 simp only [List.length_cons] at *
 omega
theorem after7_overflow (a b c d e f g x y : Golf.Word) (tail : List Golf.Word) (height : 1021 ≤ (a::b::c::d::e::f::g::tail).length) :
 GolfBounded.run 20 after7 (a::b::c::d::e::f::g::tail) x y = none := by
 unfold after7
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1) :: a :: b :: c :: d :: e :: f :: g :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: c :: d :: e :: f :: g :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 160) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: c :: d :: e :: f :: g :: tail)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 0) :: (BitVec.ofNat 256 160) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: b :: c :: d :: e :: f :: g :: tail)) (step := by rfl)
 apply GolfBounded.overflow_failure
 simp only [List.length_cons] at *
 omega
theorem all_height7 (stack : List Golf.Word) (x y : Golf.Word) :
 GolfBounded.run 20 before7 stack x y = GolfBounded.run 20 after7 stack x y := by
 cases stack with
 | nil => rfl
 | cons a tail0 =>
   cases tail0 with
   | nil => rfl
   | cons b tail1 =>
     cases tail1 with
     | nil => rfl
     | cons c tail2 =>
       cases tail2 with
       | nil => rfl
       | cons d tail3 =>
         cases tail3 with
         | nil => rfl
         | cons e tail4 =>
           cases tail4 with
           | nil => rfl
           | cons f tail5 =>
             cases tail5 with
             | nil => rfl
             | cons g tail =>
               by_cases good : tail.length ≤ 1013
               · rw [before7_success a b c d e f g x y tail good, after7_success a b c d e f g x y tail good]
               · have high : 1021 ≤ (a::b::c::d::e::f::g::tail).length := by simp only [List.length_cons]; omega
                 rw [before7_overflow a b c d e f g x y tail high, after7_overflow a b c d e f g x y tail high]

theorem before2_complete : GolfComposition.Complete before2 13 := by
 exact (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [128]) (by decide +kernel) (GolfComposition.Complete.step (op := 27) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 3) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 22) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 129) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [128]) (by decide +kernel) (GolfComposition.Complete.step (op := 27) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 3) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 22) (immediate := []) (by decide +kernel) GolfComposition.Complete.nil)))))))))))))
theorem after2_complete : GolfComposition.Complete after2 13 := by
 exact (GolfComposition.Complete.step (op := 99) (immediate := [0, 0, 0, 1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [128]) (by decide +kernel) (GolfComposition.Complete.step (op := 95) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 80) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 27) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 3) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 128) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 145) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 22) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 144) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 130) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 22) (immediate := []) (by decide +kernel) GolfComposition.Complete.nil)))))))))))))
theorem context2 : GolfComposition.ContextEquivalent before2 after2 :=
 GolfComposition.context_of_equal before2_complete after2_complete all_height2
theorem before7_complete : GolfComposition.Complete before7 13 := by
 exact (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [160]) (by decide +kernel) (GolfComposition.Complete.step (op := 27) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 3) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 22) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 134) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [160]) (by decide +kernel) (GolfComposition.Complete.step (op := 27) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 3) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 22) (immediate := []) (by decide +kernel) GolfComposition.Complete.nil)))))))))))))
theorem after7_complete : GolfComposition.Complete after7 13 := by
 exact (GolfComposition.Complete.step (op := 99) (immediate := [0, 0, 0, 1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [160]) (by decide +kernel) (GolfComposition.Complete.step (op := 95) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 80) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 27) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 3) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 128) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 145) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 22) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 144) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 135) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 22) (immediate := []) (by decide +kernel) GolfComposition.Complete.nil)))))))))))))
theorem context7 : GolfComposition.ContextEquivalent before7 after7 :=
 GolfComposition.context_of_equal before7_complete after7_complete all_height7

theorem success2 (stack : List Golf.Word) (x y : Golf.Word) (lower : 2 ≤ stack.length) (upper : stack.length ≤ 1020) :
 ∃ output, GolfBounded.run 20 before2 stack x y = some output ∧ GolfBounded.run 20 after2 stack x y = some output := by
 cases stack with
 | nil => simp only [List.length_cons, List.length_nil] at lower; omega
 | cons a tail0 =>
   cases tail0 with
   | nil => simp only [List.length_cons, List.length_nil] at lower; omega
   | cons b tail =>
     exact ⟨output2 a b tail, before2_success a b x y tail (by simp only [List.length_cons] at upper; omega), after2_success a b x y tail (by simp only [List.length_cons] at upper; omega)⟩
theorem overflow2 (stack : List Golf.Word) (x y : Golf.Word) (height : 1021 ≤ stack.length) :
 GolfBounded.run 20 before2 stack x y = none ∧ GolfBounded.run 20 after2 stack x y = none := by
 cases stack with
 | nil => simp only [List.length_cons, List.length_nil] at height; omega
 | cons a tail0 =>
   cases tail0 with
   | nil => simp only [List.length_cons, List.length_nil] at height; omega
   | cons b tail =>
     exact ⟨before2_overflow a b x y tail height, after2_overflow a b x y tail height⟩
theorem success7 (stack : List Golf.Word) (x y : Golf.Word) (lower : 7 ≤ stack.length) (upper : stack.length ≤ 1020) :
 ∃ output, GolfBounded.run 20 before7 stack x y = some output ∧ GolfBounded.run 20 after7 stack x y = some output := by
 cases stack with
 | nil => simp only [List.length_cons, List.length_nil] at lower; omega
 | cons a tail0 =>
   cases tail0 with
   | nil => simp only [List.length_cons, List.length_nil] at lower; omega
   | cons b tail1 =>
     cases tail1 with
     | nil => simp only [List.length_cons, List.length_nil] at lower; omega
     | cons c tail2 =>
       cases tail2 with
       | nil => simp only [List.length_cons, List.length_nil] at lower; omega
       | cons d tail3 =>
         cases tail3 with
         | nil => simp only [List.length_cons, List.length_nil] at lower; omega
         | cons e tail4 =>
           cases tail4 with
           | nil => simp only [List.length_cons, List.length_nil] at lower; omega
           | cons f tail5 =>
             cases tail5 with
             | nil => simp only [List.length_cons, List.length_nil] at lower; omega
             | cons g tail =>
               exact ⟨output7 a b c d e f g tail, before7_success a b c d e f g x y tail (by simp only [List.length_cons] at upper; omega), after7_success a b c d e f g x y tail (by simp only [List.length_cons] at upper; omega)⟩
theorem overflow7 (stack : List Golf.Word) (x y : Golf.Word) (height : 1021 ≤ stack.length) :
 GolfBounded.run 20 before7 stack x y = none ∧ GolfBounded.run 20 after7 stack x y = none := by
 cases stack with
 | nil => simp only [List.length_cons, List.length_nil] at height; omega
 | cons a tail0 =>
   cases tail0 with
   | nil => simp only [List.length_cons, List.length_nil] at height; omega
   | cons b tail1 =>
     cases tail1 with
     | nil => simp only [List.length_cons, List.length_nil] at height; omega
     | cons c tail2 =>
       cases tail2 with
       | nil => simp only [List.length_cons, List.length_nil] at height; omega
       | cons d tail3 =>
         cases tail3 with
         | nil => simp only [List.length_cons, List.length_nil] at height; omega
         | cons e tail4 =>
           cases tail4 with
           | nil => simp only [List.length_cons, List.length_nil] at height; omega
           | cons f tail5 =>
             cases tail5 with
             | nil => simp only [List.length_cons, List.length_nil] at height; omega
             | cons g tail =>
               exact ⟨before7_overflow a b c d e f g x y tail height, after7_overflow a b c d e f g x y tail height⟩
end GolfMaskReuse
