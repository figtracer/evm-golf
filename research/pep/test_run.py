"""Regression checks for evidence classification, without installed provers."""

import unittest

from run import classify


class EvidenceTests(unittest.TestCase):
    def test_timeouts_and_solver_errors_do_not_prove_a_claim(self):
        for result in [dict(status="timeout", exit_code=None), dict(status="finished", exit_code=1)]:
            self.assertNotEqual(classify("z3", result, "unsat\n")["status"], "unsat")
        self.assertEqual(classify("z3", dict(status="finished", exit_code=0), "unknown\n")["status"], "unknown")

    def test_internal_solver_timeout_is_unresolved(self):
        result = classify("lean-auto", dict(status="finished", exit_code=1), "error: The SAT solver timed out")
        self.assertEqual(result["status"], "solver-timeout")

    def test_lean_requires_all_requested_axiom_reports(self):
        output = "'claim' depends on axioms: [propext]\n"
        result = dict(status="finished", exit_code=0)
        self.assertEqual(classify("lean-guided", result, output, ("claim", "candidate_correct"))["status"], "error")
        for axiom in ("sorryAx", "my_false_assumption", "claim._native.other.ax_1"):
            result = dict(status="finished", exit_code=0)
            self.assertEqual(classify("lean-guided", result, f"'claim' depends on axioms: [{axiom}]")["status"], "rejected-axioms")

    def test_native_evaluation_is_explicit_and_failed_proofs_stay_unverified(self):
        output = "'claim' depends on axioms: [propext, claim._native.bv_decide.ax_1_5]"
        result = classify("lean-auto", dict(status="finished", exit_code=0), output)
        self.assertEqual(result["status"], "checked")
        self.assertTrue(result["native_evaluation"])
        output = "error: The prover found a counterexample\n'claim' depends on axioms: [sorryAx]"
        result = classify("lean-auto", dict(status="finished", exit_code=1), output)
        self.assertEqual(result["status"], "counterexample-reported")


if __name__ == "__main__":
    unittest.main()
