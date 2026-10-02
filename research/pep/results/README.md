# Pep proof experiment

2 repetitions, 15s wall limit per process. Width: 256 bits.

Cells show status and median observed wall time (including startup). Timeouts are censored; Lean errors are unresolved proofs.

| Case | Z3 | cvc5 | Lean automatic | Lean guided replay |
| --- | --- | --- | --- | --- |
| add-zero | unsat 0.009s | unsat 0.012s | checked 0.338s | checked 0.341s |
| carry-add | unsat 0.141s | unsat 0.084s | checked 0.681s | checked 0.687s |
| distributivity | unsat 0.011s | unsat 0.011s | timeout 15.045s | checked 0.353s |
| mul-cancel | unsat 0.011s | unsat 0.011s | timeout 15.046s | checked 0.325s |
| difference-squares | unsat 0.022s | timeout 15.025s | timeout 15.047s | checked 0.381s |
| square-cross | unsat 0.031s | timeout 15.027s | timeout 15.078s | checked 0.379s |
| false-square-cross | timeout 15.016s | sat 4.639s | counterexample 3.956s | counterexample 3.950s |

Guided proof discovery is excluded from these timings; see the corpus discovery record. Expression timings exclude bytecode proofs. Separate bytecode-results.json records full three-theorem checks with the guided proof.

Raw SMT unsat answers have not been certificate-checked. Lean axiom dependencies are recorded in results.json. Native evaluation remains part of the automatic lane's trust boundary.

All six valid cases passed the separate bytecode checks. The add-zero bytecode proof was rechecked after explicitly binding both theorem arguments; timed expression/SMT inputs were unchanged. See metadata.json for the repair record.
