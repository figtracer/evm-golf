namespace GolfMaskWindow
def before : List Nat := [96, 1, 96, 1, 96, 224, 27, 3, 22, 96, 1, 96, 1, 96, 224, 27, 3, 25]
def after : List Nat := [96, 1, 96, 1, 96, 224, 27, 3, 22, 100, 0, 255, 255, 255, 255, 96, 224, 27]
def lowMask : Golf.Word := BitVec.ofNat 256 (2^224-1)
def highMask : Golf.Word := ~~~lowMask
def output (a : Golf.Word) (tail : List Golf.Word) := highMask :: (lowMask &&& a) :: tail
private theorem before_success (a x y : Golf.Word) (tail : List Golf.Word) (height : tail.length ≤ 1020) :
 GolfBounded.run 19 before (a::tail) x y = some (output a tail) := by
 unfold before
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: a :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 224) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 26959946667150639794667015087019630673637144422540572481103610249216) :: (BitVec.ofNat 256 1) :: a :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 26959946667150639794667015087019630673637144422540572481103610249215) :: a :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := (((BitVec.ofNat 256 26959946667150639794667015087019630673637144422540572481103610249215) &&& a) :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: ((BitVec.ofNat 256 26959946667150639794667015087019630673637144422540572481103610249215) &&& a) :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: ((BitVec.ofNat 256 26959946667150639794667015087019630673637144422540572481103610249215) &&& a) :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 224) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: ((BitVec.ofNat 256 26959946667150639794667015087019630673637144422540572481103610249215) &&& a) :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 26959946667150639794667015087019630673637144422540572481103610249216) :: (BitVec.ofNat 256 1) :: ((BitVec.ofNat 256 26959946667150639794667015087019630673637144422540572481103610249215) &&& a) :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 26959946667150639794667015087019630673637144422540572481103610249215) :: ((BitVec.ofNat 256 26959946667150639794667015087019630673637144422540572481103610249215) &&& a) :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 115792089210356248756420345214020892766250353992003419616917011526809519390720) :: ((BitVec.ofNat 256 26959946667150639794667015087019630673637144422540572481103610249215) &&& a) :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.empty_success
 simp only [List.length_cons]
 omega
private theorem before_overflow (stack : List Golf.Word) (x y : Golf.Word) (height : 1022 ≤ stack.length) :
 GolfBounded.run 19 before stack x y = none := by
 unfold before
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1) :: stack)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: stack)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 224) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: stack)) (step := by rfl)
 apply GolfBounded.overflow_failure
 simp only [List.length_cons] at *
 omega
private theorem after_success (a x y : Golf.Word) (tail : List Golf.Word) (height : tail.length ≤ 1020) :
 GolfBounded.run 19 after (a::tail) x y = some (output a tail) := by
 unfold after
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: a :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 224) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: a :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 26959946667150639794667015087019630673637144422540572481103610249216) :: (BitVec.ofNat 256 1) :: a :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 26959946667150639794667015087019630673637144422540572481103610249215) :: a :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := (((BitVec.ofNat 256 26959946667150639794667015087019630673637144422540572481103610249215) &&& a) :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 4294967295) :: ((BitVec.ofNat 256 26959946667150639794667015087019630673637144422540572481103610249215) &&& a) :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 224) :: (BitVec.ofNat 256 4294967295) :: ((BitVec.ofNat 256 26959946667150639794667015087019630673637144422540572481103610249215) &&& a) :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.step_success (next := ((BitVec.ofNat 256 115792089210356248756420345214020892766250353992003419616917011526809519390720) :: ((BitVec.ofNat 256 26959946667150639794667015087019630673637144422540572481103610249215) &&& a) :: tail)) (height := by simp only [List.length_cons]; omega) (step := by rfl)
 apply GolfBounded.empty_success
 simp only [List.length_cons]
 omega
private theorem after_overflow (stack : List Golf.Word) (x y : Golf.Word) (height : 1022 ≤ stack.length) :
 GolfBounded.run 19 after stack x y = none := by
 unfold after
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1) :: stack)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: stack)) (step := by rfl)
 apply GolfBounded.step_failure (next := ((BitVec.ofNat 256 224) :: (BitVec.ofNat 256 1) :: (BitVec.ofNat 256 1) :: stack)) (step := by rfl)
 apply GolfBounded.overflow_failure
 simp only [List.length_cons] at *
 omega

theorem unbounded (a x y : Golf.Word) (tail : List Golf.Word) :
 Golf.run 19 before (a::tail) x y = Golf.run 19 after (a::tail) x y := by
 rfl

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
 exact (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [224]) (by decide +kernel) (GolfComposition.Complete.step (op := 27) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 3) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 22) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [224]) (by decide +kernel) (GolfComposition.Complete.step (op := 27) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 3) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 25) (immediate := []) (by decide +kernel) GolfComposition.Complete.nil))))))))))))

theorem after_complete : GolfComposition.Complete after 9 := by
 exact (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [224]) (by decide +kernel) (GolfComposition.Complete.step (op := 27) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 3) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 22) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 100) (immediate := [0, 255, 255, 255, 255]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [224]) (by decide +kernel) (GolfComposition.Complete.step (op := 27) (immediate := []) (by decide +kernel) GolfComposition.Complete.nil)))))))))

theorem context : GolfComposition.ContextEquivalent before after :=
 GolfComposition.context_of_equal before_complete after_complete bounded

theorem before_output (a x y : Golf.Word) (tail : List Golf.Word) :
 Golf.run 19 before (a::tail) x y = some (output a tail) := by
 rfl

theorem after_output (a x y : Golf.Word) (tail : List Golf.Word) :
 Golf.run 19 after (a::tail) x y = some (output a tail) := by
 rfl

theorem success (a x y : Golf.Word) (tail : List Golf.Word)
 (height : tail.length ≤ 1020) :
 GolfBounded.run 19 before (a::tail) x y = some (output a tail) ∧
 GolfBounded.run 19 after (a::tail) x y = some (output a tail) := by
 exact ⟨before_success a x y tail height, after_success a x y tail height⟩

theorem underflow (x y : Golf.Word) :
 GolfBounded.run 19 before [] x y = none ∧ GolfBounded.run 19 after [] x y = none := by
 constructor <;> rfl

theorem overflow (stack : List Golf.Word) (x y : Golf.Word) (height : 1022 ≤ stack.length) :
 GolfBounded.run 19 before stack x y = none ∧ GolfBounded.run 19 after stack x y = none := by
 exact ⟨before_overflow stack x y height, after_overflow stack x y height⟩

end GolfMaskWindow
