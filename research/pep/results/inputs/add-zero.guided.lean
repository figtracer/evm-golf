import Std

namespace Golf
abbrev Word := BitVec 256
end Golf

-- External wall-clock limits govern both Lean lanes.
set_option maxHeartbeats 0
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem claim (x y : Golf.Word) : (x + (0 : Golf.Word)) = x := by
  simp

#print axioms claim
