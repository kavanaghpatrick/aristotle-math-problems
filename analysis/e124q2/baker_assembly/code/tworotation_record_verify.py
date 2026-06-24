from mpmath import mp, mpf, log, frac, ceil
mp.dps = 100
ln3, ln4, ln7 = log(3), log(4), log(7)
a = 1743375
x4 = a*ln3/ln4; x7 = a*ln3/ln7
u4 = 1 - frac(x4); u7 = 1 - frac(x7)
print("a =", a)
print("u4 = ceil(a*log3/log4) - a*log3/log4 =", mp.nstr(u4, 8), " next 4-power exponent p =", int(ceil(x4)))
print("u7 = ceil(a*log3/log7) - a*log3/log7 =", mp.nstr(u7, 8), " next 7-power exponent q =", int(ceil(x7)))
delta = (mpf(4)**u4 - 1)/3 + (mpf(7)**u7 - 1)/6
print("delta = atomSum(<3^a)/3^a - 1 =", mp.nstr(delta, 8))
# interpretation: 4^p / 3^a and 7^q / 3^a
print("4^p/3^a = 4^u4 =", mp.nstr(mpf(4)**u4, 12), "   7^q/3^a = 7^u7 =", mp.nstr(mpf(7)**u7, 12))
# Kronecker prediction: corner (1,1) visited => delta -> 0. Also check: any rational relation
# r*(ln3/ln4) + s*(ln3/ln7) = t would be detectable via PSLQ on (ln3*ln7, ln3*ln4, ln4*ln7)
from mpmath import pslq
rel = pslq([ln3*ln7, ln3*ln4, ln4*ln7], maxcoeff=10**12, maxsteps=10**6)
print("PSLQ integer relation among (ln3*ln7, ln3*ln4, ln4*ln7), coeffs<=1e12:", rel)
