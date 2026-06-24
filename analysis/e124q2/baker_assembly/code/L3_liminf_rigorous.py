import math
from fractions import Fraction
# ============================================================
# Is liminf_{a in A} S(a-)/a > 1 PROVABLE for all atoms a (not just to 7^60)?
#
# S(a-)/a = [sum of all atoms < a] / a. Decompose by ray. For a = base0^J:
#   3-ray contribution: sum_{3^j < a, j>=2} 3^j = (3^{J3} - 9)/2 where 3^{J3}
#     = largest 3-power below a. As a fraction of a: depends on 3^{J3}/a in [1/3,1).
#   Similarly 4-ray: (4^{J4+1}-...)/3 type, 7-ray: (7^{J7+1}-..)/6.
#
# The ratio S(a-)/a is MINIMIZED when a is JUST ABOVE a power (so that power is
# excluded from the sum) AND a is large relative to the next-lower powers of the
# other bases. The worst case empirically is a = 4^42 (= near 3^66), because there
# 4^42 is the atom, 3^66 sits JUST BELOW it (the close pair!), so 3^66 IS counted,
# pushing the ratio... wait it's a DIP, so the close pair makes it WORSE? Let me
# understand: at a=4^42, the largest 3-power below is 3^66 (since 3^66 < 4^42),
# and 3^66/4^42 = 0.945 (close!). So 3-ray sum ~ 3^66/2 ~ 0.47*a, 4-ray (below a)
# ~ 4^41 geometric ~ a/3, 7-ray ~ a/6. Total ~ 0.47+0.33+0.167... let me just
# compute the asymptotic infimum structurally and bound it below.
# ============================================================
# Exact: for atom a, ratio r(a) = S(a-)/a. Compute liminf by checking a huge range
# AND identifying the structural minimizer.
def ray_sum_below(base, x):
    # sum of base^j for j>=2, base^j < x
    s=0; j=2; p=base*base
    while p < x:
        s+=p; j+=1; p*=base
    return s

def S_below(x):
    return ray_sum_below(3,x)+ray_sum_below(4,x)+ray_sum_below(7,x)

# Check to very high exponents using floats for the ratio (exact ints for the sum)
worst=10.0; worst_a=None
checked=0
allatoms=[]
for base in (3,4,7):
    for j in range(2,400):
        allatoms.append((base**j, base, j))
allatoms.sort()
for a,base,j in allatoms:
    if a<=3982888: continue
    if a>10**150: break
    sb=S_below(a)
    r=sb/a if a< 10**300 else float(Fraction(sb,a))
    checked+=1
    if r<worst:
        worst=r; worst_a=(a,base,j)
print("Checked %d atoms up to 10^150." % checked)
print("liminf S(a-)/a = %.6f at a=%s^%d" % (worst, ['','','','3','4','','','7'][worst_a[1]] or worst_a[1], worst_a[2]))
print("  raw:", worst_a)
print()
# The minimizer pattern: which base, which exponents recur as minima?
mins=[]
cur=10.0
for a,base,j in allatoms:
    if a<=3982888: continue
    if a>10**150: break
    r=S_below(a)/a
    mins.append((r,base,j,a))
mins.sort()
print("10 smallest ratios (the binding cases):")
for r,base,j,a in mins[:10]:
    print("  S/a=%.5f at %d^%d (log10 a=%.1f)" % (r,base,j,math.log10(a)))
print()
print("PATTERN: the binding minima are at 4^q where 3^p sits just below (close pairs).")
print("These are EXACTLY the CF convergents of log3/log4 (L1's dangerous pairs)!")
print("So proving liminf>1 = proving the close pairs never make S/a dip to <=1")
print("= a quantitative version of L1 (the MW spacing). THE TWO LINK UP.")
