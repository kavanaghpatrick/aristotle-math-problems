"""
NEEDED side, step 1: the CF-convergent geometry of log4/log3 and the actual
cross-base spacings |3^p - 4^q| at the near-coincidences. Pure exact arithmetic.
"""
from fractions import Fraction
import math

# theta = log4/log3 = 0.79248...  The near-coincidences 3^p ~ 4^q sit at q/p ~ theta,
# i.e. p/q ~ log3/log4. We want convergents of theta = log4/log3.
theta = math.log(4)/math.log(3)
print(f"theta = log4/log3 = {theta:.12f}")
print(f"1/theta = log3/log4 = {1/theta:.12f}")

# Continued fraction of theta
def cf(x, n):
    a=[]
    for _ in range(n):
        ai=math.floor(x); a.append(ai); x-=ai
        if x<1e-12: break
        x=1/x
    return a
A = cf(theta, 15)
print("CF(log4/log3) =", A)

# convergents p_k/q_k
def convergents(a):
    h=[0,1]; k=[1,0]; out=[]
    for ai in a:
        h.append(ai*h[-1]+h[-2]); k.append(ai*k[-1]+k[-2])
        out.append((h[-1],k[-1]))
    return out
C = convergents(A)
print("\nConvergents num/den of theta (num=q-index of 4-power, den=p-index of 3-power):")
for (num,den) in C:
    print(f"   {num}/{den}  -> 3^{den} vs 4^{num}")

# For each convergent p (=denominator, the 3-exponent), find best q minimizing |3^p - 4^q|
print("\n=== Actual near-coincidences |3^p - 4^q| for p up to 60 ===")
print(f"{'p':>3} {'q':>3} {'|3^p-4^q|':>22} {'rel=|.|/3^p':>14} {'log_3(rel)':>12}")
near=[]
for p in range(1,61):
    P=3**p
    # best q ~ p*theta
    q0=round(p*theta)
    best=None
    for q in (q0-1,q0,q0+1):
        if q<1: continue
        d=abs(P-4**q)
        if best is None or d<best[1]:
            best=(q,d)
    q,d=best
    rel=d/P
    near.append((p,q,d,rel))
    # only print the locally-closest (the convergent hits)
for (p,q,d,rel) in near:
    # flag convergent denominators
    is_conv = any(den==p for (num,den) in C)
    flag = " <== CONVERGENT" if is_conv else ""
    if rel < 0.06 or is_conv:
        print(f"{p:>3} {q:>3} {d:>22} {rel:>14.6e} {math.log(rel)/math.log(3):>12.4f}{flag}")
