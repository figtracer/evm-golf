import Std

namespace Golf
abbrev Word := BitVec 256
end Golf

-- External wall-clock limits govern both Lean lanes.
set_option maxHeartbeats 0
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem claim (x y : Golf.Word) : ((x * (y + (1 : Golf.Word))) - (x * y)) = x := by
  change (x * (y + 1#256)) - (x * y) = x
  rw [BitVec.mul_add, BitVec.mul_one, BitVec.add_comm (x*y) x, BitVec.add_sub_cancel]

#print axioms claim
