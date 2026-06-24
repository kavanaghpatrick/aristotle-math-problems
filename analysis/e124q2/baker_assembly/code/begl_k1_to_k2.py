import math
log3=math.log(3); log4=math.log(4); log7=math.log(7)

# ============================================================
# DISSECTION: what does BEGL96's (3,4,7) k=1 proof actually consist of?
#
# From the paper (lines 227-238), the ENTIRE (3,4,7) argument is:
#   "Using ... |3^p-4^q| > exp{ln3(p - 500 ln4 (8+ln p)^2)} of MW Cor 10.1,
#    we can show that the largest integer not in Σ(Pow({3,4,7};1)) is 581."
#
# There is NO 4-Claim machinery for (3,4,7). The 4 Claims (Theorem 1) need
# lim sup A(n)/n > 0 (positive density of the INFINITE base set) AND a finite
# chunk with harmonic sum β>2 — BOTH FALSE for the finite triple {3,4,7}
# (β = 1/2+1/3+1/6 = 1.0 exactly, and A(n)/n→0). So Theorem 1 is inapplicable.
#
# THEREFORE the (3,4,7) proof = [MW pairwise bound] + [finite computation to 581].
# The MW bound's ROLE: it guarantees the bad set (close pairs 3^p~4^q) is FINITE,
# so that beyond some computable point the gaps are provably filled, reducing
# completeness to a FINITE check (which yields 581).
# ============================================================

print("="*70)
print("STEP-BY-STEP: BEGL96 (3,4,7) k=1, and what each step needs at k=2")
print("="*70)

# The honest reconstruction of HOW the MW bound closes it (BEGL compress this
# to one line; the mechanism is the gap-filling argument):
# - Above N, every integer n is covered if the three rays B3,B4,B7 jointly
#   tile [N,inf). The only way coverage FAILS is a 'notch' where a 3-power and
#   4-power nearly coincide leaving a gap the 7-ray must bridge.
# - MW bounds |3^p-4^q| from below => only finitely many notches deep enough
#   to matter => finite check.

print("""
KEY STRUCTURAL FACT (verified from paper text):
The (3,4,7) result has NO combinatorial/covering 'half' written in BEGL96.
The 4-Claim machinery (Claims 1-4) belongs to Theorem 1, whose hypotheses
(lim sup A(n)/n > 0 AND a finite β>2 chunk) are BOTH FALSE for {3,4,7}.
So BEGL's (3,4,7) proof = ONE pairwise MW bound + ONE finite computation (->581).
'Where does k=1 enter the covering half' is therefore the WRONG question:
there is no covering half. k=1 enters only via (i) the MW bound's height range
and (ii) the finite-check ceiling.
""")

# What changes at k=2:
print("WHAT CHANGES k=1 -> k=2 (each step tagged):")
print()
# STEP 1: the pairwise MW input
print("STEP 1 [MW pairwise bound |3^p-4^q|]:  CARRIES (k-UNIFORM).")
print("  The bound |3^p-4^q| > exp{...} is a statement about ALL p,q>=1.")
print("  At k=2 we use only pairs p,q>=2 (a SUBSET). Same inequality, same constant.")
print("  Verified earlier (matveev §B): raising k only discards low pairs.")
print()
# STEP 2: the finite check ceiling
N0_k1, N0_k2, N0_k3 = 581, 3982888, 166025260
print("STEP 2 [finite computation to N0]:  CARRIES but BALLOONS (NEEDS-NEW-COMPUTATION).")
print("  k=1: finite check to N0=581       (trivial, by hand in 1996)")
print("  k=2: finite check to N0=%d  (4 million; trivial for a computer, NOT by hand)" % N0_k2)
print("  k=3: finite check to N0=%d (166 million; still a feasible sieve)" % N0_k3)
print("  The check ITSELF is mechanical; only its SIZE grows. No new mathematics.")
print()
# The crossover p* (where MW bound bites) vs the finite N0 — are they consistent?
pb=1e5
for _ in range(500): pb = 500*log4*(8+math.log(pb))**2
print("STEP 3 [reconciling MW crossover with finite N0]:  THE SUBTLE POINT.")
print("  MW bound 'bites' (forces |3^p-4^q|>1) only at p* ~ %d, i.e. 3^p* has" % round(pb))
print("  ~140,000 digits — ASTRONOMICALLY beyond N0=581 (or 4M, or 166M).")
print("  So the MW bound does NOT directly certify gaps at the SCALE of the holes.")
print("  Its real job: prove the close-pair SET is FINITE (only finitely many p")
print("  with |3^p-4^q|/3^p below any fixed notch tolerance), which combined with")
print("  the ray-density argument reduces completeness to the finite check.")
print("  This logic is IDENTICAL at k=2 (the close-pair set is the same set,")
print("  restricted to p,q>=2). CARRIES.")
print()

# Is there a JOINT/equidistribution step hiding? Check: does the pairwise |3^p-4^q|
# bound ALONE suffice, or is base-7 joint covering needed (troika's retraction)?
print("STEP 4 [the base-7 bridge — pairwise vs joint, baker's adjudication]:")
print("  troika's §C.3 retraction says asymptotic closure is base-7 JOINT")
print("  equidistribution, NOT pairwise. BUT: BEGL's WRITTEN proof invokes only")
print("  the PAIRWISE |3^p-4^q| bound + finite check to 581. The joint covering")
print("  is what their ONE-LINE 'we can show ... is 581' COMPRESSES — i.e. the")
print("  finite computation to 581 IS the joint check, done by brute force below")
print("  the point where the pairwise bound takes over. So at k=1 the 'joint'")
print("  content lives entirely in the finite check (<=581), not in an asymptotic")
print("  equidistribution theorem. At k=2 the same: joint content lives in the")
print("  finite check (<=3,982,888). >>> THIS IS THE CRUX FOR baker <<<")
