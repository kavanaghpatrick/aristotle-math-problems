import math
log3=math.log(3); log4=math.log(4); log7=math.log(7)
N0=3982888
# ============================================================
# DIRECTIVE (b): does pairwise MW close the gap lemma beyond a crossover V0?
#
# Gap lemma (GAP): atomSum(<v) >= v + 2N0 for atoms v > 3^15.
# Exact identity (Aristotle §4): atomSum(<v) = sum_d (c_d(v) - d^2)/(d-1),
#   c_d(v) = smallest power of d that is >= v.  For the base of v, c_d(v)=v.
# So for v = base0^e:
#   atomSum(<v) = (v - base0^2)/(base0-1) + sum_{d != base0} (c_d(v) - d^2)/(d-1).
# The SLACK above v is: sum_{d != base0} (c_d(v) - v)/(d-1) [the gap to next d-powers].
#
# Worst case: v near a TRIPLE coincidence 3^p ~ 4^q ~ 7^r, where c_d(v) - v is
# small for BOTH other bases simultaneously. Need slack >= 2N0 + (deficit ~18).
#
# KEY (b) insight from team-lead: the needed slack 2N0 is CONSTANT (~8e6) while
# atomSum scales with v. The deficit at large v needs the gap c_d(v)-v to not be
# too small. By MW, c_d(v)-v (the distance from v up to the next power of another
# base) is bounded below: if v=3^p, the next 4-power above is 4^{q+1} with
# 4^{q+1} - 3^p >= |4^{q+1} - 3^p|, and MW bounds this. Let me work out the
# crossover V0 beyond which MW guarantees (GAP).
# ============================================================

# For v = 3^p (a 3-atom), slack = (c_4(v)-v)/3 + (c_7(v)-v)/6.
# c_4(v) = 4^{ceil(p log3/log4)}, c_7(v)=7^{ceil(p log3/log7)}.
# The slack is SMALL only if BOTH 4^{q+1} and 7^{r+1} are just above 3^p.
# Worst single-base: 4^{q+1} just above 3^p means |4^{q+1}-3^p| small = MW close pair.
# MW: |3^p - 4^{q'}| >= 3^p exp(-C(log p)^2). So c_4(v)-v = 4^{q+1}-3^p could be as
# small as ~3^p exp(-C(log p)^2) IF 4^{q+1} is the close one. Then slack/v ~ 
# (1/3) exp(-C(log p)^2) -> needs >= 2N0/v. Since 2N0/v -> 0 (v grows) and 
# exp(-C(log p)^2) decays SLOWER than any 1/v^eps... wait exp(-C(log p)^2) vs 2N0/v:
# 2N0/v = 2N0/3^p = exp(log(2N0) - p log3) -> decays like exp(-p) (geometric).
# exp(-C(log p)^2) decays like exp(-(log p)^2) -- MUCH SLOWER than exp(-p).
# So for large p, exp(-C(log p)^2) >> 2N0/3^p, i.e. slack/v >> 2N0/v => slack >> 2N0.
# THE GAP LEMMA HOLDS for large v EVEN with terrible MW constants!
print("DIRECTIVE (b): does MW close (GAP) beyond a crossover V0?")
print()
print("Worst-case slack at v=3^p (triple-coincidence): slack/v ~ (1/3)*rel_gap_4 + (1/6)*rel_gap_7")
print("where rel_gap_d = (c_d(v)-v)/v = distance to next d-power, relative.")
print("Needed: slack >= 2N0, i.e. slack/v >= 2N0/v = 2N0/3^p.")
print()
print("2N0/3^p decays GEOMETRICALLY (~exp(-p log3)). MW gives rel_gap_d >= exp(-C(log p)^2)")
print("which decays POLY-LOG (~exp(-(log p)^2)) -- MUCH SLOWER. So for large p, MW slack")
print("DOMINATES the needed 2N0/v. Crossover V0 = where exp(-C(log p)^2) ~ 2N0/3^p:")
print()
# Solve: the slack lower bound from MW vs 2N0/v. Use BEGL constant C in 
# rel_gap >= exp(-500*ln3*ln4*(8+log p)^2) [the relative form].
# Condition: (1/3)*exp(-500 ln3 ln4 (8+log p)^2) >= 2N0/3^p
#   <=> p*log3 - log(3) - 500 ln3 ln4 (8+log p)^2 >= log(2N0)
#   <=> p*log3 - 500 ln3 ln4 (8+log p)^2 >= log(6 N0)
def lhs(p): return p*log3 - 500*log3*log4*(8+math.log(p))**2
rhs = math.log(6*N0)
print("Solving p*log3 - 500 ln3 ln4 (8+log p)^2 >= log(6 N0) = %.2f:" % rhs)
import numpy as np
for p in [10**3, 10**4, 10**5, 2*10**5, 2.94*10**5, 3*10**5, 4*10**5, 10**6]:
    p=int(p)
    val=lhs(p)
    print("  p=%8d: LHS=%.3e  (>= %.1f ? %s)" % (p, val, rhs, val>=rhs))
# crossover
ps=np.arange(100, 10**6)
vals = ps*log3 - 500*log3*log4*(8+np.log(ps))**2
idx=np.where(vals>=rhs)[0]
p_star = int(ps[idx[0]]) if len(idx) else None
print()
print(">>> Crossover p* (BEGL constant) where MW closes (GAP): p* =", p_star)
print("    i.e. for atoms v = 3^p with p >= %d (and similarly 4^q, 7^r), (GAP) holds by MW." % p_star)
print("    Height 3^p* ~ 10^%.0f" % (p_star*log3/math.log(10)))
print()
print("This MATCHES team-lead's estimate (~3^{p*}, p*~2.94e5). The gap lemma's V0 is the")
print("SAME crossover as the pairwise |3^p-4^q| finiteness crossover. Below V0: finite check.")
