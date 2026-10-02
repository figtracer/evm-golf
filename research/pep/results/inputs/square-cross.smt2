; Exact wrapping 256-bit equality; unsat proves the claim.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 256))
(declare-fun y () (_ BitVec 256))
(assert (not (= (bvsub (bvmul (bvadd x y) (bvadd x y)) (bvadd (bvmul x x) (bvmul y y))) (bvmul (_ bv2 256) (bvmul x y)))))
(check-sat)
