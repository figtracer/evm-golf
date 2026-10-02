import Std

namespace Golf
abbrev Word := BitVec 256
end Golf

-- External wall-clock limits govern both Lean lanes.
set_option maxHeartbeats 0
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem claim (x y : Golf.Word) : ((x * x) - (y * y)) = ((x - y) * (x + y)) := by
  rw [BitVec.mul_comm (x-y) (x+y), BitVec.mul_sub, BitVec.add_mul,
      BitVec.add_mul, BitVec.mul_comm y x, ← BitVec.sub_sub, BitVec.add_sub_cancel]

#print axioms claim
