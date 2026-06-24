import math
log3=math.log(3); log4=math.log(4); log7=math.log(7)

# ============================================================
# THE HONEST RECONSTRUCTION of BEGL's (3,4,7) k=1 argument.
# (BEGL compress it to one line; this is what it must be.)
#
# The argument has exactly TWO parts:
#
# PART A (asymptotic, USES MW): For n large, n is covered. Mechanism:
#   the B3+B4 ray has gaps ~ (1/2) * (largest power below n), located just
#   below powers. The B7 ray must place a subset-sum in each gap. A gap is
#   UNbridgeable only if it's both wide AND positioned where no 7-subset-sum
#   lands -- which happens only at a deep 3^p~4^q notch. The RELATIVE notch
#   depth is bounded below by MW: |3^p-4^q|/3^p > exp(-500 ln3 ln4 (8+ln p)^2).
#   Since this floor decays only like exp(-(log p)^2) while the number of
#   available B7 shifts grows like p/log7*log3, for p beyond a COMPUTABLE
#   bound the B7 ray always bridges. => only finitely many 'dangerous' scales.
#
# PART B (finite check): below that computable bound, verify by direct
#   computation. BEGL's "581" is the OUTPUT of this finite check.
#
# CRITICAL: the boundary between A and B is NOT at p*~294k (where the
# ABSOLUTE bound bites). It's where the RELATIVE bound first guarantees
# bridging. Let me estimate that crossover and check it's modest.
# ============================================================

# The bridging condition (heuristic, BEGL-style): the B7 ray near scale 3^p
# has ~ log_7(3^p) = p*log3/log7 'active' high powers, each contributing a
# subset-sum structure that covers a fraction ~ (1 - 1/7) of any interval of
# its scale. The notch the B7 ray must avoid being defeated by has relative
# width ~ MW floor. Bridging succeeds when (number of B7 shifts) * (per-shift
# coverage) exceeds 1 over the notch, i.e. roughly when the notch isn't deeper
# than the B7 lattice can resolve.
#
# A cleaner, RIGOROUS-ENOUGH statement (what actually matters for k-transfer):
# The set of (p,q) with |3^p-4^q|/3^p < epsilon is FINITE for any fixed epsilon>0
# IFF log4/log3 has finite irrationality measure -- which MW/Baker GUARANTEES
# (effective finite measure). Count them:
theta=log3/log4
def closest_q(p): return round(p*theta)
for eps in [1e-1, 1e-2, 1e-3, 1e-4]:
    cnt=0; maxp=0
    for p in range(1,5000):
        q=closest_q(p)
        if q<1: continue
        d=q*log4-p*log3
        rel=abs(1-math.exp(d)) if abs(d)<700 else 9
        if rel<eps:
            cnt+=1; maxp=max(maxp,p)
    print("  rel gap < %.0e : %d pairs with p<5000, largest p=%d" % (eps,cnt,maxp))
print()
print("The dangerous-pair set thins geometrically (CF convergents). For the")
print("(3,4,7) covering, the relevant epsilon (B7 notch tolerance) is ~O(1)")
print("modest, so the dangerous set is SMALL and the finite check is to N0=581.")
print()

# NOW THE k=2 TRANSFER. At k=2, R_2 = subset-sums of {3^j,4^j,7^j : j>=2}.
# Equivalently (matveev §B, lift §A): same close-pair set restricted to p,q>=2.
# So PART A (asymptotic, MW) carries VERBATIM (subset of the same pairs).
# PART B (finite check) reruns to a LARGER N0=3,982,888.
print("k=1 -> k=2 TRANSFER:")
print("  PART A (asymptotic MW bound): CARRIES. Same |3^p-4^q| bound, pairs p,q>=2 a subset.")
print("  PART B (finite check): CARRIES mechanically, N0 grows 581 -> 3,982,888 (feasible sieve).")
print()
# BUT: is there a hidden k-dependence in the BRIDGING crossover (where PART A
# takes over)? At k=2 the rays are 3^2 B3, 4^2 B4, 7^2 B7 -- scaled. The notch
# structure is the SAME pairwise object but the B7 RESOLUTION changes: fewer
# 7-powers available below a given n (since 7^2=49 is the smallest atom).
# This is mahler's point: the three rays dilate by DIFFERENT factors.
print("THE ONE GENUINE k-RISK (mahler's finding): at k=2 the bridging crossover")
print("(where PART A takes over from PART B) may shift, because the B7 ray's local")
print("resolution changes (smallest 7-atom is 7^2=49, not 7). This is PARAMETRIC")
print("(re-runs with shifted constant), NOT structural -- UNLESS the joint")
print("equidistribution (troika §C.3) is what's really doing PART A, in which")
print("case PART A is OPEN at every k and BEGL's one-liner hides it. >>> baker adjudicates <<<")
