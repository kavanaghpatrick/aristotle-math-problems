"""KILL-TEST rhin's irrationality-measure claims."""
from math import log
import mpmath as mp
mp.mp.dps=60

print("="*70)
print("CLAIM 2: mu(log4/log3) = mu(log2/log3) exactly (rational scaling preserves exponent)")
print("="*70)
r1 = mp.log(4)/mp.log(3)
r2 = 2*mp.log(2)/mp.log(3)
print(f"  log4/log3      = {mp.nstr(r1,30)}")
print(f"  2*(log2/log3)  = {mp.nstr(r2,30)}")
print(f"  |diff| = {mp.nstr(abs(r1-r2),5)}  (rhin: <1e-40)")
# CAVEAT CHECK: is the IRRATIONALITY MEASURE preserved under x -> 2x? 
# mu(alpha) for |alpha - p/q| > c/q^mu. For beta=2*alpha: |beta - p/q| = 2|alpha - (p/2)/q|.
# This relates beta's approximations to alpha's by HALF-integer numerators -> measure IS preserved
# (standard: mu invariant under nonzero rational Mobius / scaling). rhin's claim is STANDARD and TRUE.
print("  rational scaling preserves mu: STANDARD (Mobius-invariance of the irrationality exponent). OK")

print()
print("="*70)
print("CLAIM 3: MW (log p)^2 bound DOMINATES Matveev (log p)^1 at every relevant p")
print("="*70)
ln3,ln4 = log(3),log(4)
CA = 1.4*30**5*2**4.5*ln3*ln4   # ~1.17e9
def relMW_logexp(p):  return -762*(8+log(p))**2     # rhin's quoted shape (approx of 500 ln4 ... )
def relMW_exact(p):   return -500*ln4*(8+log(p))**2 # exact loss exponent in base-3 orders? no: this is in nats? 
# careful: BEGL |3^p-4^q|>exp{ln3(p-500ln4(8+lnp)^2)}. rel=|.|/3^p, log(rel)>ln3(p-500ln4(8+lnp)^2)-p ln3
#        = -ln3*500 ln4 (8+ln p)^2. So log(rel)_MW > -ln3*500*ln4*(8+ln p)^2 = -762.0*(8+ln p)^2. rhin's 762 OK.
def logrelMW(p): return -ln3*500*ln4*(8+log(p))**2
def logrelMat(p): return -CA*(1+log(p))   # log(rel) > -CA*(1+log p)
print(f"  MW coefficient ln3*500*ln4 = {ln3*500*ln4:.1f}  (rhin says 762)")
print(f"  Matveev coefficient C*A1*A2 = {CA:.3e}  (rhin says 1.17e9)")
print(f"  {'p':>12} {'logrel_MW':>15} {'logrel_Matveev':>16} {'MW > Mat (less negative)?':>26}")
for p in [5,53,665,10**4,10**6,10**9,10**10,10**12]:
    mw, mat = logrelMW(p), logrelMat(p)
    print(f"  {p:>12} {mw:>15.1f} {mat:>16.3e} {str(mw>mat):>26}")
# Where would (log p)^2 ever overtake (log p)^1? When 762*(8+lnp)^2 > 1.17e9*(1+lnp), i.e. lnp ~ 1.5e6
import mpmath
# solve 762*(lnp)^2 ~ 1.17e9 lnp -> lnp ~ 1.17e9/762 ~ 1.54e6 -> p ~ e^1.5e6 (hyper-astronomical)
print(f"\n  MW only loses to Matveev when ln p > ~{CA/( ln3*500*ln4):.3e}, i.e. p > e^(1.5e6) -- never relevant.")
print("  => rhin's domination claim HOLDS at every computable/relevant p. OK")
