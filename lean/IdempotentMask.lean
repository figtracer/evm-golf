namespace GolfIdempotentMask
def before : List Nat := [96, 1, 96, 1, 96, 160, 27, 3, 22, 96, 1, 96, 1, 96, 160, 27, 3, 22]
def after : List Nat := [104, 0, 0, 0, 0, 0, 0, 0, 0, 1, 97, 0, 1, 96, 160, 27, 3, 22]
def lowMask : Golf.Word := BitVec.ofNat 256 (2^160-1)
def output (a : Golf.Word) (tail : List Golf.Word) := (lowMask &&& a) :: tail
private theorem before_success (a x y : Golf.Word) (tail : List Golf.Word) (height : tail.length ≤ 1020) :
 GolfBounded.run 19 before (a::tail) x y = some (output a tail) := by
 unfold before
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: a :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 160) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542976) :: (BitVec.ofNat 256 1) :: a :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) :: a :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := (((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 160) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542976) :: (BitVec.ofNat 256 1) :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) :: ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := (((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: tail)) (height := by simp only [List.length_cons]; omega) (step := by change some (((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a)) :: tail) = some (((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: tail); simp only [← BitVec.and_assoc, BitVec.and_self])
 apply GolfBounded.empty_success
 simp only [List.length_cons]
 omega
private theorem before_overflow (stack : List Golf.Word) (x y : Golf.Word) (height : 1022 ≤ stack.length) :
 GolfBounded.run 19 before stack x y = none := by
 unfold before
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1) :: stack)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: stack)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 160) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: stack)) (step := by rfl)
 apply GolfBounded.overflow_failure
 simp only [List.length_cons] at *
 omega
private theorem after_success (a x y : Golf.Word) (tail : List Golf.Word) (height : tail.length ≤ 1020) :
 GolfBounded.run 19 after (a::tail) x y = some (output a tail) := by
 unfold after
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: a :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 160) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542976) :: (BitVec.ofNat 256 1) :: a :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) :: a :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := (((BitVec.ofNat 256 1461501637330902918203684832716283019655932542975) &&& a) :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.empty_success
 simp only [List.length_cons]
 omega
private theorem after_overflow (stack : List Golf.Word) (x y : Golf.Word) (height : 1022 ≤ stack.length) :
 GolfBounded.run 19 after stack x y = none := by
 unfold after
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1) :: stack)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: stack)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 160) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: stack)) (step := by rfl)
 apply GolfBounded.overflow_failure
 simp only [List.length_cons] at *
 omega

theorem unbounded (a x y : Golf.Word) (tail : List Golf.Word) :
  Golf.run 19 before (a::tail) x y = Golf.run 19 after (a::tail) x y := by
 change some ((lowMask &&& (lowMask &&& a)) :: tail) = some ((lowMask &&& a) :: tail)
 simp only [← BitVec.and_assoc, BitVec.and_self]

theorem bounded (stack : List Golf.Word) (x y : Golf.Word) :
  GolfBounded.run 19 before stack x y = GolfBounded.run 19 after stack x y := by
 cases stack with
 | nil => rfl
 | cons a tail =>
   by_cases height : tail.length ≤ 1020
   · rw [before_success a x y tail height, after_success a x y tail height]
   · have high : 1022 ≤ (a::tail).length := by simp only [List.length_cons]; omega
     rw [before_overflow (a::tail) x y high, after_overflow (a::tail) x y high]

theorem before_complete : GolfComposition.Complete before 12 := by
 exact (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [160]) (by decide +kernel) (GolfComposition.Complete.step (op := 27) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 3) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 22) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [160]) (by decide +kernel) (GolfComposition.Complete.step (op := 27) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 3) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 22) (immediate := []) (by decide +kernel) GolfComposition.Complete.nil))))))))))))

theorem after_complete : GolfComposition.Complete after 6 := by
 exact (GolfComposition.Complete.step (op := 104) (immediate := [0, 0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel) (GolfComposition.Complete.step (op := 97) (immediate := [0, 1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [160]) (by decide +kernel) (GolfComposition.Complete.step (op := 27) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 3) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 22) (immediate := []) (by decide +kernel) GolfComposition.Complete.nil))))))

theorem context : GolfComposition.ContextEquivalent before after :=
 GolfComposition.context_of_equal before_complete after_complete bounded

theorem before_output (a x y : Golf.Word) (tail : List Golf.Word) :
 Golf.run 19 before (a::tail) x y = some (output a tail) := by
 change some ((lowMask &&& (lowMask &&& a)) :: tail) = some ((lowMask &&& a) :: tail)
 simp only [← BitVec.and_assoc, BitVec.and_self]

theorem after_output (a x y : Golf.Word) (tail : List Golf.Word) :
 Golf.run 19 after (a::tail) x y = some (output a tail) := by
 rfl

theorem success (a x y : Golf.Word) (tail : List Golf.Word) (height : tail.length ≤ 1020) :
 GolfBounded.run 19 before (a::tail) x y = some (output a tail) ∧
 GolfBounded.run 19 after (a::tail) x y = some (output a tail) := by
 exact ⟨before_success a x y tail height, after_success a x y tail height⟩

theorem underflow (x y : Golf.Word) :
 GolfBounded.run 19 before [] x y = none ∧ GolfBounded.run 19 after [] x y = none := by
 constructor <;> rfl

theorem overflow (stack : List Golf.Word) (x y : Golf.Word) (height : 1022 ≤ stack.length) :
 GolfBounded.run 19 before stack x y = none ∧ GolfBounded.run 19 after stack x y = none := by
 exact ⟨before_overflow stack x y height, after_overflow stack x y height⟩

end GolfIdempotentMask
