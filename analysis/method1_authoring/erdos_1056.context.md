# Context pack for erdos_1056

## KNOWN DEAD ENDS — do NOT re-propose any of these:
(from `mk failed`):
[math-forge] Failed approaches
---
title                                 why_failed                                                                                                                     avoid_pattern                                              slot  problem_id
------------------------------------  -----------------------------------------------------------------------------------------------------------------------------  ---------------------------------------------------------  ----  ----------
FALSE: least_N_5_eq_16                OEIS A276661 uses different definition. Actual minimum is 13, not 16.                                                                                                                           erdos_1   
FALSE: sum_distinct_implies_sidon     Sidon definition in the file allows repeated elements in the tuple (a,b,c,d). The counterexample shows the implication fails.  Do not assume sum-distinct implies Sidon                         erdos_1   
FALSE: discrete_entropy_power_naive   Statement has free X_entropy variable with no constraint linking it to variance                                                Do not assume continuous EPI applies without proper setup        erdos_1   
FALSE: erdos_1_empty_set_formulation  Empty set and N=0 satisfy IsSumDistinctSet vacuously but violate C*1 ≤ 0                                                       Always require non-empty set in Erdős formulations               erdos_1   
FALSE: hcn_tau_near

## Knowledge-base context (`mk context`):
[math-forge] Context files for 'erdos_1056':
---
  (No prior results found)

This is the first submission for this problem.
