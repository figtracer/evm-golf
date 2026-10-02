; Exact wrapping 256-bit equality; unsat proves the claim.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 256))
(declare-fun y () (_ BitVec 256))
(assert (not (= (bvsub (bvmul x (bvadd y (_ bv1 256))) (bvmul x y)) x)))
(check-sat)
