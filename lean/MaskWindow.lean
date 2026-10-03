namespace GolfMaskWindow
def before : List Nat := [96, 1, 96, 1, 96, 224, 27, 3, 22, 96, 1, 96, 1, 96, 224, 27, 3, 25]
def after : List Nat := [96, 1, 96, 1, 96, 224, 27, 3, 22, 100, 0, 255, 255, 255, 255, 96, 224, 27]
theorem unbounded (a x y : Golf.Word) (tail : List Golf.Word) :
 Golf.run 19 before (a::tail) x y = Golf.run 19 after (a::tail) x y := by
 simp [before, after, Golf.run, Golf.immediate]

theorem bounded (stack : List Golf.Word) (x y : Golf.Word) :
 GolfBounded.run 19 before stack x y = GolfBounded.run 19 after stack x y := by
 cases stack with
 | nil => simp [before, after, GolfBounded.run, Golf.run, Golf.immediate]
 | cons a tail =>
   simp [before, after, GolfBounded.run, Golf.run, Golf.immediate]
   <;> (repeat' split) <;> simp_all <;> omega

theorem before_complete : GolfComposition.Complete before 12 := by
 exact (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [224]) (by decide +kernel) (GolfComposition.Complete.step (op := 27) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 3) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 22) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [224]) (by decide +kernel) (GolfComposition.Complete.step (op := 27) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 3) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 25) (immediate := []) (by decide +kernel) GolfComposition.Complete.nil))))))))))))

theorem after_complete : GolfComposition.Complete after 9 := by
 exact (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [1]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [224]) (by decide +kernel) (GolfComposition.Complete.step (op := 27) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 3) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 22) (immediate := []) (by decide +kernel) (GolfComposition.Complete.step (op := 100) (immediate := [0, 255, 255, 255, 255]) (by decide +kernel) (GolfComposition.Complete.step (op := 96) (immediate := [224]) (by decide +kernel) (GolfComposition.Complete.step (op := 27) (immediate := []) (by decide +kernel) GolfComposition.Complete.nil)))))))))

theorem context : GolfComposition.ContextEquivalent before after :=
 GolfComposition.context_of_equal before_complete after_complete bounded


def lowMask : Golf.Word := BitVec.ofNat 256 (2^224-1)
def highMask : Golf.Word := ~~~lowMask
def output (a : Golf.Word) (tail : List Golf.Word) := highMask :: (lowMask &&& a) :: tail

theorem before_output (a x y : Golf.Word) (tail : List Golf.Word) :
 Golf.run 19 before (a::tail) x y = some (output a tail) := by
 simp [before, Golf.run, Golf.immediate, output, lowMask, highMask]

theorem after_output (a x y : Golf.Word) (tail : List Golf.Word) :
 Golf.run 19 after (a::tail) x y = some (output a tail) := by
 rw [← unbounded]
 exact before_output a x y tail

theorem success (a x y : Golf.Word) (tail : List Golf.Word)
 (height : tail.length ≤ 1020) :
 GolfBounded.run 19 before (a::tail) x y = some (output a tail) ∧
 GolfBounded.run 19 after (a::tail) x y = some (output a tail) := by
 have old : GolfBounded.run 19 before (a::tail) x y = some (output a tail) := by
   simp [before, GolfBounded.run, Golf.run, Golf.immediate, output, lowMask, highMask]
   <;> (repeat' split) <;> simp_all <;> omega
 exact ⟨old, by rw [← bounded]; exact old⟩

theorem underflow (x y : Golf.Word) :
 GolfBounded.run 19 before [] x y = none ∧ GolfBounded.run 19 after [] x y = none := by
 simp [before, after, GolfBounded.run, Golf.run, Golf.immediate]

theorem overflow (stack : List Golf.Word) (x y : Golf.Word) (height : 1022 ≤ stack.length) :
 GolfBounded.run 19 before stack x y = none ∧ GolfBounded.run 19 after stack x y = none := by
 have old : GolfBounded.run 19 before stack x y = none := by
   simp [before, GolfBounded.run, Golf.run, Golf.immediate]
   <;> (repeat' split) <;> simp_all <;> omega
 exact ⟨old, by rw [← bounded]; exact old⟩
end GolfMaskWindow
