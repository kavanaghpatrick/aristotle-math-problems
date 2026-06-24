import numpy as np
# Does psi_m match the predicted torus orbit? lift says orbit {m log3/log4 mod 1}, {m log3/log7 mod 1}.
# Measured psi_m (argmin C / 3^m, in [1,3)):
measured = {8:2.402,9:2.780,10:1.000,11:1.091,12:1.443,13:2.486,14:1.001,15:1.031,16:2.274,17:1.278,18:1.002}
import math
log3=math.log(3); log4=math.log(4); log7=math.log(7)
print("Does psi_m track a torus orbit? Compare measured argmin-phase to predicted {m*log3/log7} etc.")
print(f"{'m':>3}{'psi_meas':>10}{'frac(m*l3/l7)':>15}{'frac(m*l3/l4)':>15}{'psi-1 (in[0,2))':>16}")
for m in sorted(measured):
    p=measured[m]
    o7=(m*log3/log7)%1
    o4=(m*log3/log4)%1
    print(f"{m:>3}{p:>10.3f}{o7:>15.3f}{o4:>15.3f}{p-1:>16.3f}")
# Test correlation: is (psi_m - 1) (in [0,2)) a function of the torus position? 
# The phases cluster at psi≈1.0 for m=10,14,18 (period 4). Check: is m mod something the driver?
print("\npsi≈1.00 at m=10,14,18 (period 4 in m). Is this the torus orbit or a base-driven periodicity?")
# torus orbit {m log3/log4} has period = denominator of best rational approx of log3/log4=0.792
# log3/log4 ~ 0.7925; convergents: 4/5=0.8, 19/24... so quasi-period ~5 or ~24, NOT 4.
print(f"log3/log4={log3/log4:.4f} (convergents 4/5, 19/24,...); log3/log7={log3/log7:.4f}")
print("=> period-4 clustering of psi≈1 does NOT match either torus rotation number (would be period ~5 or ~24).")
print("=> the phase is NOT cleanly the predicted 2-torus orbit; it's dominated by a low-order resonance.")
# correlation test: fit psi_m-1 to a linear combo of the two torus coords
import numpy as np
X=np.array([[ (m*log3/log7)%1, (m*log3/log4)%1, 1] for m in sorted(measured)])
y=np.array([measured[m]-1 for m in sorted(measured)])
coef,res,_,_=np.linalg.lstsq(X,y,rcond=None)
pred=X@coef
ss_res=np.sum((y-pred)**2); ss_tot=np.sum((y-y.mean())**2)
print(f"\nlinear fit of (psi_m-1) to torus coords: R^2 = {1-ss_res/ss_tot:.3f} (high => torus-predictable; low => not)")
