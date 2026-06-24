# Deep search: does inf(atomSum(<v)/v - 1) keep dropping?
# Fixed-point 128-bit arithmetic: frac(e*theta) = ((e*T) mod 2^128)/2^128, error <= e*2^-128.
from mpmath import mp, mpf, log
mp.dps = 60
ln3, ln4, ln7 = log(3), log(4), log(7)
SH = 128; MOD = 1 << SH; MASK = MOD - 1
def fix(x): return int(x * MOD)

fams = {
  '3': (fix(ln3/ln4), fix(ln3/ln7), (mpf(4), mpf(3)), (mpf(7), mpf(6))),
  '4': (fix(ln4/ln3), fix(ln4/ln7), (mpf(3), mpf(2)), (mpf(7), mpf(6))),
  '7': (fix(ln7/ln3), fix(ln7/ln4), (mpf(3), mpf(2)), (mpf(4), mpf(3))),
}
lnb = {'3': float(ln3), '4': float(ln4), '7': float(ln7)}
import math
LIM = {'3': 20_000_000, '4': 15_771_000, '7': 11_220_000}  # equal height ~3^2e7

best = mpf('0.0055551')  # current record from <=10^3100 scan
recs = []
THRESH = int(0.02 * MOD)  # only evaluate when both one-sided distances < 0.02
for base, (T1, T2, (b1, d1), (b2, d2)) in fams.items():
    s1 = 0; s2 = 0
    for e in range(1, LIM[base] + 1):
        s1 = (s1 + T1) & MASK
        s2 = (s2 + T2) & MASK
        u1 = MOD - s1; u2 = MOD - s2
        if u1 < THRESH and u2 < THRESH:
            uu1 = mpf(u1) / MOD; uu2 = mpf(u2) / MOD
            dlt = (b1**uu1 - 1) / d1 + (b2**uu2 - 1) / d2
            if dlt < best:
                best = dlt
                h = e * lnb[base] / math.log(10)
                recs.append((h, base, e, float(dlt)))
print("new records (height as 10^h):")
for h, base, e, d in sorted(recs):
    print("  v = %s^%d  (10^%.0f)  delta = %.8f" % (base, e, h, d))
print("final infimum upper bound:", float(best))
