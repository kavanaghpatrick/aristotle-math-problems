from fractions import Fraction
import math
# Verify maverick's tau(D) = sum 1/(d-1) on the FULL gauntlet (the definitive task #14 check).
# Also verify the derivation chain: Newhouse tau_N = 1/(d-2); Astels normalized gamma = tau_N/(1+tau_N) = 1/(d-1).
def gamma_from_newhouse(d):
    tauN = Fraction(1, d-2)
    return tauN/(1+tauN)  # should equal 1/(d-1)
print("Derivation check: Astels normalized gamma(C_d) = tau_N/(1+tau_N) =?= 1/(d-1):")
for d in [3,4,5,6,7,11]:
    g = gamma_from_newhouse(d); target = Fraction(1,d-1)
    print(f"  d={d}: tau_N=1/(d-2)={Fraction(1,d-2)}, gamma={g}, 1/(d-1)={target}, MATCH={g==target}")

# Full gauntlet: tau>=1 <=> cofinite
COF=[(3,4,7),(3,4,5),(3,5,7,13),(3,4,11,16),(4,5,6,7,8),(3,4,8,9),(3,5,6,21),(3,4,6)]
NOTCOF=[(3,4),(3,5),(3,4,11),(3,4,10),(3,4,12),(3,5,7),(3,4,9),(3,4,13),(4,5,6,7)]
def tau(D): return sum(Fraction(1,d-1) for d in D)
print("\nGauntlet: tau(D)>=1 <=> cofinite:")
allok=True
for D in COF:
    t=tau(D); ok=t>=1
    if not ok: allok=False
    print(f"  COF {str(D):<14} tau={float(t):.4f} >=1? {ok} {'' if ok else 'FAIL'}")
for D in NOTCOF:
    t=tau(D); ok=t<1
    if not ok: allok=False
    print(f"  NOT {str(D):<14} tau={float(t):.4f} <1? {ok} {'' if ok else 'FAIL'}")
print(f"\nFULL GAUNTLET PASS: {allok}  (tau = sum 1/(d-1) = Astels normalized thickness; tau_crit=1)")
