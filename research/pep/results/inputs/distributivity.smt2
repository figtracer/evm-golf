; Exact wrapping 256-bit equality; unsat proves the claim.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 256))
(declare-fun y () (_ BitVec 256))
(assert (not (= (bvadd (bvmul x y) (bvmul x x)) (bvmul x (bvadd y x)))))
(check-sat)
