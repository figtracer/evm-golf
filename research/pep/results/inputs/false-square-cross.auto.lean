import Std

namespace Golf
abbrev Word := BitVec 256
end Golf

-- External wall-clock limits govern both Lean lanes.
set_option maxHeartbeats 0
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem claim (x y : Golf.Word) : (((x + y) * (x + y)) - ((x * x) + (y * y))) = (x * y) := by
  (try simp [BitVec.mul_comm]) <;> bv_decide (config := { timeout := 15 })

#print axioms claim
