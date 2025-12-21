# Aristotle Submission Triage (Dec 20, 2025)

## 🟢 TRUST (Clean definitions, take results seriously)

| UUID | Filename | Purpose | Notes |
|------|----------|---------|-------|
| bb81e3dc | tuza_tau_Te_packing_CORRECTED.lean | τ(T_e) ≤ 2 for packing elements | Fixes flowerGraph misunderstanding |
| e23a4af3 | tuza_tau_Te_packing_SCAFFOLDED.lean | Same with helper structure | Includes S_e analysis |
| 9b6083eb | tuza_nu2_dichotomy.lean | ν=2 dichotomy approach | Fixes false `exists_good_packing_nu2` |
| 05f5bd44 | nu2_vertexdisjoint_pessimist.lean | Proves false lemma is FALSE | Expected counterexample |
| nu4_prime | tuza_nu4_v1_boris_prime.lean | ν=4 direct attempt | Boris minimal pattern |
| nu4_pess | tuza_nu4_v6_pessimist.lean | ν=4 counterexample hunt | Tests if Tuza fails at ν=4 |

## 🟡 INFORMAL (Proof sketches, no Lean audit)

| UUID | Filename | Purpose |
|------|----------|---------|
| f7f90a6c | tuza_nu_le_3_final.md | ν≤3 informal proof |
| 72aaa595 | tuza_tau_Te_packing_INFORMAL.md | τ(T_e) proof sketch |
| 82c1041b | tuza_nu3_flower_exclusion.md | Flower exclusion sketch |

## ⚠️ CHECK (Files may be missing)

| UUID | Filename | Issue |
|------|----------|-------|
| f9473ebd | tuza_nu_le_3_final.lean | Formal version - file missing? |
| b17bf01d | tuza_nu3_flower_exclusion.lean | File not found in submissions/ |
| f45bfea3 | tuza_nu3_case_by_case.lean | File not found in submissions/ |

## 🔴 COMPLETED

| UUID | Filename | Result |
|------|----------|--------|
| 827eacfc | tuza_nu2_assembly.lean | Clean failure (too minimal) |

## Validation Summary

All audited .lean files use **CORRECT** definitions:
- `G.edgeFinset.powerset.filter(...)` for covering
- `t.offDiag.image` for triangle edges (no self-loops)
- No unrestricted `sInf`
- No `axiom` declarations

## When Results Return

```bash
# Analyze output
python3 scripts/workflow.py analyze <output-file>

# Update database
python3 -c "UPDATE submissions SET status='completed' WHERE uuid='...'"
```
