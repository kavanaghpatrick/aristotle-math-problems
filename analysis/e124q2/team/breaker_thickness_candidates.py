import numpy as np
from fractions import Fraction
# Pre-test natural candidate discrete-thickness definitions against ground truth.
# Ground truth: cofinite (β>=1) vs not (β<1).
COFINITE=[(3,4,7),(3,4,5),(3,5,7,13),(3,4,11,16),(3,4,6),(4,5,6,7,8),(3,5,6,21)]
NOT_COF=[(3,4),(3,5),(3,4,9),(3,4,11),(3,4,10),(3,4,12),(3,5,7),(3,4,13),(3,11),(4,11)]
def beta(D): return sum(Fraction(1,d-1) for d in D)

# Candidate 1: tau1 = sum_d 1/(d-1)  (the harmonic / Pomerance mass). This is just beta — trivially exact.
def tau_harmonic(D): return float(beta(D))
# Candidate 2: Newhouse thickness of single B_d = bridge/gap. For B_d self-similar, bridge=1 (the {0,1}),
#   gap at scale d^m is d^m - (d^m-1)/(d-1). Astels: thickness of d-adic 0/1 Cantor set.
#   The standard thickness of the set with ratio: each level, interval splits; thickness tau_d = ?
#   For B_d (digits 0/1 in base d), it's a self-similar set with 2 pieces, gap ratio. 
#   tau = (bridge)/(gap). Smallest bridge=1, largest gap ~ (d-2)/(d-1)*d^m... thickness -> 1/(d-2).
def tau_newhouse_single(d): return Fraction(1,d-2) if d>2 else None
# Candidate 2 combined: Astels sum of thicknesses: sum_d tau_d >= 1 ?  with tau_d=1/(d-2)
def tau_astels_sum(D): return float(sum(Fraction(1,d-2) for d in D))
# Candidate 3: sum_d log2/log d  (box-counting dim) — maverick says WRONG, include to confirm
import math
def tau_boxdim(D): return sum(math.log(2)/math.log(d) for d in D)

defs={'harmonic β=Σ1/(d-1)':tau_harmonic, 'Astels Σ1/(d-2)':tau_astels_sum, 'boxdim Σlog2/logd':tau_boxdim}
print("Candidate thickness defs vs ground truth. CORRECT iff (value>=crit) matches (β>=1).")
print("Using crit=1 for each (Astels/harmonic), report separation:\n")
for name,f in defs.items():
    print(f"## {name} (crit=1)")
    # find if a single threshold separates the two classes
    cof_vals=[(D,f(D)) for D in COFINITE]
    not_vals=[(D,f(D)) for D in NOT_COF]
    min_cof=min(v for _,v in cof_vals); max_not=max(v for _,v in not_vals)
    sep = min_cof > max_not
    print(f"   min over COFINITE = {min_cof:.4f} ; max over NOT_COF = {max_not:.4f} ; SEPARATES={sep}")
    if not sep:
        # which not-cofinite has value >= min_cof (the false positives)
        fp=[(D,round(v,4)) for D,v in not_vals if v>=min_cof]
        print(f"   FALSE POSITIVES (not-cofinite but value>=min cofinite): {fp}")
    print()
