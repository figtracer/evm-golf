; Exact wrapping 256-bit equality; unsat proves the claim.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 256))
(declare-fun y () (_ BitVec 256))
(assert (not (= (bvsub (bvmul x x) (bvmul y y)) (bvmul (bvsub x y) (bvadd x y)))))
(check-sat)
