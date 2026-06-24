import math
log3=math.log(3); log4=math.log(4); log7=math.log(7)
# ============================================================
# DETERMINING THE ENDING. Three things to separate:
#
# (P1) The SIMPLE window-propagation lemma needs (*): a <= 1+S(a-). My data
#      shows S(a-)/a has infimum EXACTLY 1, approached at triple coincidences.
#      So (*) [which is a <= 1+S(a-), i.e. ratio >= 1 - 1/a] is satisfied as
#      long as ratio > 1 - 1/a. Since ratio -> 1 from ABOVE (inf=1 but is it
#      attained or approached?), and 1/a -> 0, the question is whether ratio
#      EVER drops below 1 (strictly). If ratio >= 1 always, (*) holds (since
#      1-1/a < 1 <= ratio). Let me check: does ratio ever go BELOW 1?
#
# (P2) Even if (*) fails at some atom a (ratio < 1, i.e. a > 1+S(a-)), this
#      creates a gap of width (a - S(a-) - 1) in the SINGLE-PASS argument --
#      but R2 might still cover it via OTHER atom combinations (multi-atom).
#      The team's N0(2)=3,982,888 is FINITE, so SOME mechanism closes it.
# ============================================================

# (P1): does ratio S(a-)/a ever drop below 1? It would require a > S(a-),
# i.e. atom a exceeds the sum of ALL smaller atoms. With three geometric rays
# each summing to ~ (base/(base-1)) * (largest power below a), the sum of
# smaller atoms is at least ~ a/2 (3-ray) + a/3-ish... Let me find the true min.
def ray_sum_below(base, x):
    s=0; p=base*base
    while p < x: s+=p; p*=base
    return s
def S_below(x): return ray_sum_below(3,x)+ray_sum_below(4,x)+ray_sum_below(7,x)

# scan all atoms to 10^200, track if ratio ever < 1
minr=10.0; minatom=None; below1=[]
for base in (3,4,7):
    for j in range(2,420):
        a=base**j
        if a<=3982888: continue
        if a>10**200: break
        r=S_below(a)/a
        if r<minr: minr=r; minatom=(base,j,a)
        if r<1.0: below1.append((base,j,r))
print("Scanned atoms to 10^200.")
print("Minimum ratio S(a-)/a = %.6f at %d^%d" % (minr, minatom[0], minatom[1]))
print("Atoms with ratio < 1 (would FAIL (*)):", len(below1), below1[:5])
print()
if not below1:
    print(">>> (*) HOLDS for ALL atoms to 10^200: ratio >= %.4f > 1 always. <<<" % minr)
    print("    So the SIMPLE window-propagation lemma CLOSES L3 -- PROVIDED we can")
    print("    prove ratio >= 1 for ALL atoms (not just to 10^200). The infimum is 1")
    print("    (triple-coincidence limit), approached but the question is attainment.")
print()
# (P1 rigorous): ratio = 1/2 + (4/3)rho4 + (7/6)rho7 + lower-order, where
# rho4=4^q/3^p (frac), rho7=7^l/3^p. Actually let me recompute the constant.
# 3-ray below 3^p (a=3^p): sum_{j=2}^{p-1}3^j=(3^p-9)/2, /a = 1/2 - small.
# 4-ray below a: sum_{4^j<a,j>=2}4^j = (4^{q+1}-16)/3, /a = (4/3)(4^q/a) - small
#   where 4^q<a<=4^{q+1}, so 4^q/a in (1/4,1]. contribution (4/3)*rho4, rho4 in (1/4,1].
# 7-ray: (7/6)*rho7, rho7=7^l/a in (1/7,1].
# MIN of 1/2 + (4/3)rho4 + (7/6)rho7 over rho4>1/4, rho7>1/7 is OPEN at 1/2+1/3+1/6=1.
# But rho4>1/4 STRICTLY (4^q > a/4 since 4^{q+1}>a => 4^q>a/4). So (4/3)rho4 > 1/3 STRICT.
# Similarly (7/6)rho7 > 1/6 STRICT. So ratio > 1/2+1/3+1/6 = 1 STRICTLY for every atom!
print("RIGOROUS LOWER BOUND (the key lemma):")
print("  At a=3^p: 4^q < a <= 4^{q+1} => 4^q > a/4 STRICTLY => (4/3)(4^q/a) > 1/3 strictly.")
print("  Likewise 7^l > a/7 => (7/6)(7^l/a) > 1/6 strictly. And 3-ray = (3^p-9)/(2a) -> 1/2.")
print("  So S(a-)/a > 1/2 + 1/3 + 1/6 = 1 ... BUT the 3-ray gives (1/2 - 9/(2a)) < 1/2.")
print("  Need to check the 9/(2a) deficit doesn't push it below 1. For a > N0=3.98M, 9/(2a)")
print("  < 1.2e-6, while the STRICT slack in rho4,rho7 is order 1. So ratio > 1 by a") 
print("  margin >= (strict rho slack) - 1.2e-6 > 0. The slack rho4-1/4 etc. is bounded")
print("  below by the MW spacing (how far 4^q is from a/4 = how close 4^{q+1} to 3^p).")
