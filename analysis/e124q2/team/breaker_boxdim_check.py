import math
from fractions import Fraction
def boxdim(D): return sum(math.log(2)/math.log(d) for d in D)
def beta(D): return float(sum(Fraction(1,d-1) for d in D))
# maverick: {3,4} and {3,4,9} satisfy boxdim>1 but NOT cofinite. Check, and find boxdim's failures.
test=[(3,4),(3,4,9),(3,4,11),(3,5,7),(3,4,13),(3,4,10),(3,4,12)]
print("Does box-dim Σlog2/logd > 1 misfire (>1 but β<1, i.e. NOT cofinite)?")
for D in test:
    bd=boxdim(D); b=beta(D)
    print(f"  {str(D):<12} boxdim={bd:.4f} (>1? {bd>1}) | β={b:.4f} (cofinite? {b>=1}) | MISFIRE={bd>1 and b<1}")
# The cleanest disproof of box-dim: a family with boxdim>1 but β<1 (not cofinite) AND boxdim < a
# cofinite family — i.e. no single box-dim threshold works. Search for it.
import itertools
print("\nSearching for box-dim threshold failure (not-cofinite boxdim >= some cofinite boxdim)...")
cof=[]; noncof=[]
for r in range(2,5):
    for D in itertools.combinations(range(3,20),r):
        b=beta(D)
        bd=boxdim(D)
        if b>=1: cof.append((D,bd))
        else: noncof.append((D,bd))
min_cof_bd=min(bd for _,bd in cof)
fp=[(D,round(bd,3)) for D,bd in noncof if bd>=min_cof_bd]
print(f"  min boxdim over cofinite (β>=1) families (d<20,r<=4) = {min_cof_bd:.4f}")
print(f"  NOT-cofinite families with boxdim >= that (box-dim FALSE POSITIVES): {len(fp)}")
print(f"  examples: {sorted(fp,key=lambda x:-x[1])[:8]}")
