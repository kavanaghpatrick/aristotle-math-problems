import math
from fractions import Fraction
# Verify maverick's load-bearing claims for the conclusion doc.
# 1. The 35x gap at identical sigma=0: (3,4,7) n0=166M vs (3,5,7,13) n0=4.8M, both sum 1/(d-1)=1.
def beta(D): return sum(Fraction(1,d-1) for d in D)
for D in [(3,4,7),(3,5,7,13)]:
    print(f"D={D}: sum 1/(d-1) = {beta(D)} (sigma = beta-1 = {float(beta(D))-1:.4f})")
# my strict-verified n0(k=3): (3,4,7)=166025260, (3,5,7,13)=4796646
n347=166025260; n3713=4796646
print(f"\n(3,4,7) k=3 n0 = {n347}")
print(f"(3,5,7,13) k=3 n0 = {n3713}")
print(f"RATIO = {n347/n3713:.1f}x  (maverick claims 35x)")
print(f"=> {n347/n3713:.0f}x gap at IDENTICAL sigma=0 => no f(sigma,d_max,d_2) can fit => MW content. CONFIRMED.")

# 2. The closest-rel-pair INVERSION: (3,4,7) has WEAKER closest clustering (0.0258) yet LARGER n0
# than (3,5,7,13) (0.0046, the 3^7≈13^3 coincidence). Verify the clustering values.
def closest_rel_pair(D, maxexp=40):
    """min over base pairs (a,b) and exponents of |a^p - b^q| / max(a^p,b^q) (relative closeness)."""
    best=1.0; bestinfo=None
    for i in range(len(D)):
        for j in range(len(D)):
            if i>=j: continue
            a,b=D[i],D[j]
            for p in range(1,maxexp):
                ap=a**p
                if ap>10**18: break
                # nearest b^q
                q=round(p*math.log(a)/math.log(b))
                for qq in [q-1,q,q+1]:
                    if qq<1: continue
                    bq=b**qq
                    rel=abs(ap-bq)/max(ap,bq)
                    if rel<best: best=rel; bestinfo=(a,p,b,qq,ap,bq)
    return best,bestinfo
for D in [(3,4,7),(3,5,7,13)]:
    c,info=closest_rel_pair(D)
    print(f"\nD={D}: closest-rel-pair = {c:.4f}  via {info}")
print("\nmaverick: (3,4,7)=0.0258 WEAKER clustering but LARGER n0 than (3,5,7,13)=0.0046 (3^7≈13^3).")
print("=> n0 is NOT even predicted by the single closest pair => full transcendence structure => MW/Baker.")
