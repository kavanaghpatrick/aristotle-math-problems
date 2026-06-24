from mpmath import mp, mpf, log, floor, frac
mp.dps = 80

ln3, ln4, ln7 = log(3), log(4), log(7)

# ratio-1 model at each atom family (asymptotic, corrections O(1/v)):
# v=3^a: (1/3)(4^(1-{a*ln3/ln4})-1) + (1/6)(7^(1-{a*ln3/ln7})-1)
# v=4^b: (1/2)(3^(1-{b*ln4/ln3})-1) + (1/6)(7^(1-{b*ln4/ln7})-1)
# v=7^c: (1/2)(3^(1-{c*ln7/ln3})-1) + (1/3)(4^(1-{c*ln7/ln4})-1)

def d3(a):
    u4 = 1 - frac(a*ln3/ln4); u7 = 1 - frac(a*ln3/ln7)
    return (mpf(4)**u4 - 1)/3 + (mpf(7)**u7 - 1)/6
def d4(b):
    u3 = 1 - frac(b*ln4/ln3); u7 = 1 - frac(b*ln4/ln7)
    return (mpf(3)**u3 - 1)/2 + (mpf(7)**u7 - 1)/6
def d7(c):
    u3 = 1 - frac(c*ln7/ln3); u4 = 1 - frac(c*ln7/ln4)
    return (mpf(3)**u3 - 1)/2 + (mpf(4)**u4 - 1)/3

# sanity: exact check vs true atomSum at moderate size
atoms = sorted([3**e for e in range(2,200)]+[4**e for e in range(2,160)]+[7**e for e in range(2,120)])
import math
def exact_delta(v):
    s = sum(a for a in atoms if a < v)
    return s/v - 1
print("sanity (exact vs model):")
for (v, f, n) in [(3**40, d3, 40), (4**30, d4, 30), (7**25, d7, 25)]:
    print("  v=%s : exact=%.6f model=%.6f" % (("3^40","4^30","7^25")[[3**40,4**30,7**25].index(v)], exact_delta(v), float((d3 if v==3**40 else d4 if v==4**30 else d7)(n))))

# running infimum over all atoms up to 10^3100 (a<=6500 for base3, etc.)
import heapq
events = []
for a in range(16, 6510): events.append((float(a*ln3/log(10)), '3', a))
for b in range(10, 5170): events.append((float(b*ln4/log(10)), '4', b))
for c in range(6, 3670): events.append((float(c*ln7/log(10)), '7', c))
events.sort()
fn = {'3': d3, '4': d4, '7': d7}
best = mpf(10)
records = []
for (h, base, e) in events:
    d = fn[base](e)
    if d < best:
        best = d
        records.append((h, base, e, float(d)))
print("\nrunning-infimum records over all atoms, v in (3^15, 10^3100]:")
for (h, base, e, d) in records:
    print("  v = %s^%d  (10^%.1f)  delta = %.6f" % (base, e, h, d))
