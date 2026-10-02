import Std

namespace Golf
abbrev Word := BitVec 256
end Golf

-- External wall-clock limits govern both Lean lanes.
set_option maxHeartbeats 0
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem claim (x y : Golf.Word) : (((x + y) * (x + y)) - ((x * x) + (y * y))) = ((2 : Golf.Word) * (x * y)) := by
  change ((x+y)*(x+y))-((x*x)+(y*y)) = 2#256*(x*y)
  apply BitVec.sub_eq_iff_eq_add.mpr
  rw [BitVec.two_mul]
  simp only [BitVec.add_mul, BitVec.mul_add]
  ac_rfl

#print axioms claim
