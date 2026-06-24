"""
Evaluate the ACTUAL BEGL96/MW displayed bound vs reality:
  |3^p - 4^q| > exp{ ln3 * (p - 500*ln4*(8 + ln p)^2) }       (BEGL96 line 231, MW Cor 10.1)
Questions a verifier must answer BEFORE any 'known result discharges it' claim:
  (1) Is it actually a valid lower bound on the real gaps? (sanity)
  (2) Where does it become NON-VACUOUS (RHS exponent > 0, i.e. p > 500 ln4 (8+ln p)^2)?
  (3) How does the bound's exponent compare to the NEEDED exponent for the bridge?
"""
from math import log, exp

ln3, ln4 = log(3), log(4)

def begl_rhs_exponent(p):
    # exponent E(p) such that bound = exp(E(p)); also = ln3*(p - 500 ln4 (8+ln p)^2)
    return ln3*(p - 500*ln4*(8 + log(p))**2)

# (2) non-vacuous threshold: smallest p with E(p) > 0
print("=== BEGL96/MW bound exponent E(p) = ln3*(p - 500 ln4 (8+ln p)^2) ===")
print("p, E(p), bound=exp(E(p)) [bound<1 means VACUOUS: any gap>=1 beats it]")
prev_sign = None
threshold = None
for p in [5,10,53,100,500,1000,2000,5000,10000,20000,50000,100000]:
    E = begl_rhs_exponent(p)
    vac = "VACUOUS" if E < 0 else "useful"
    print(f"  p={p:7d}: E={E:14.1f}  ({vac})")
# find exact crossover
import numpy as np
ps = np.arange(2, 200000)
Es = ln3*(ps - 500*ln4*(8+np.log(ps))**2)
pos = np.where(Es>0)[0]
if len(pos):
    print(f"\n>>> Bound becomes NON-VACUOUS (E>0) first at p = {ps[pos[0]]}")
else:
    print("\n>>> Bound NEVER becomes non-vacuous in p<200000")

# (1) sanity: at the non-vacuous p's, is exp(E) actually < actual gap? (must be, if it's a real LB)
print("\n=== sanity: actual gap vs bound at large p (must have gap >= bound) ===")
for p in [ps[pos[0]] if len(pos) else 100000, 100000]:
    P = 3**p
    q = round(p*ln3/ln4)
    gap = min(abs(P-4**qq) for qq in (q-1,q,q+1) if qq>=1)
    E = begl_rhs_exponent(p)
    # compare logs: ln(gap) vs E
    lngap = log(gap)
    print(f"  p={p}: ln(actual gap)={lngap:.1f}, bound exponent E={E:.1f}, LB valid={lngap>=E}")

print("\n=== where does E(p)>0 eventually? (penalty ~ (ln p)^2 vs linear p) ===")
import numpy as np
# search much higher
for hi in [10**6, 10**7, 10**8]:
    ps = np.arange(2, hi, max(1,hi//2000000))
    Es = ln3*(ps - 500*ln4*(8+np.log(ps))**2)
    pos = np.where(Es>0)[0]
    if len(pos):
        print(f">>> first E>0 at p ~ {ps[pos[0]]} (searched to {hi})")
        break
    else:
        print(f"    still vacuous to p={hi}")

# The crossover: p = 500 ln4 (8+ln p)^2. Solve by iteration.
import math
p = 1e6
for _ in range(200):
    p = 500*ln4*(8+math.log(p))**2
print(f">>> fixed point p* = 500 ln4 (8+ln p)^2  ~=  {p:.1f}  (bound non-vacuous for p > p*)")
print(f"    at p* the gap 3^p has ~ {p*ln3/math.log(10):.0f} decimal digits -- astronomically beyond any computed N")
