import numpy as np
# ============================================================
# VERIFY ARISTOTLE'S REDUCTION (directive a), line by line.
#
# §1 Symmetry: Reach(S) symmetric about Sigma/2. CHECK by direct sieve.
# §2 Doubling: I(V) = "(N0, Sigma_V - N0) subset Reach(S_V)". Step adds atom v,
#    claims M ∪ (M+v) covers (N0, Sigma_v - N0) iff v <= Sigma_V - 2N0.
# §3 Base I(3^15): (3982888, 29858461) gap-free in Reach(S_{3^15}).
# §4 Gap lemma: atomSum(<v) >= v + 2N0 for atoms v > 3^15.
# ============================================================
N0 = 3982888

# --- CHECK §1 symmetry on a finite atom set ---
def reach(atoms):
    Sigma = sum(atoms)
    r = np.zeros(Sigma+1, bool); r[0]=True
    for a in atoms:
        r[a:] |= r[:Sigma+1-a].copy()
    return r, Sigma

base_atoms = sorted([3**e for e in range(2,16)]+[4**e for e in range(2,12)]+[7**e for e in range(2,9)])
print("Base atoms (<=3^15):", len(base_atoms), "atoms; sum =", sum(base_atoms))
r, Sigma = reach(base_atoms)
# symmetry: r[n] == r[Sigma-n]
sym_ok = bool((r == r[::-1]).all())
print("§1 SYMMETRY r[n]==r[Sigma-n]:", sym_ok, "(Sigma=%d)"%Sigma)
print()

# --- CHECK §3 base case I(3^15): (N0, Sigma-N0) gap-free ---
lo, hi = N0+1, Sigma-N0-1
mid_solid = bool(r[lo:hi+1].all())
print("§3 BASE I(3^15): middle (%d, %d) gap-free:" % (N0, Sigma-N0), mid_solid)
print("   (Aristotle's interval: [3982889, 29858460], Sigma-N0-1 = %d)" % (Sigma-N0-1))
print("   match Sigma-N0=%d vs claimed 29858461:" % (Sigma-N0), Sigma-N0==29858461)
print()

# --- CHECK §2 doubling step interval algebra ---
# I(V): (N0, Sigma_V - N0) subset Reach(S_V). Add atom v. 
# M = (N0, Sigma_V - N0) open. M+v = (N0+v, Sigma_V - N0 + v) = (N0+v, Sigma_v - N0).
# Union covers (N0, Sigma_v - N0) iff M and M+v overlap/abut: N0+v <= (Sigma_V - N0) [+1 for integers]
# i.e. v <= Sigma_V - 2N0. Let me verify this is the EXACT condition AND that it
# actually yields I(v) by direct sieve, step by step through the tail atoms.
print("§2 DOUBLING: verifying I(V) propagates via (star) v <= Sigma_V - 2N0, step-by-step:")
atoms_all = sorted([3**e for e in range(2,40)]+[4**e for e in range(2,40)]+[7**e for e in range(2,40)])
V0 = 3**15
S = [a for a in atoms_all if a <= V0]
SigmaV = sum(S)
tail = [a for a in atoms_all if a > V0]
print("  Start: Sigma_V0 = %d, middle (%d, %d)" % (SigmaV, N0, SigmaV-N0))
all_ok = True
for v in tail[:15]:
    star = (v <= SigmaV - 2*N0)
    margin = (SigmaV - 2*N0) - v
    if not star:
        all_ok=False
        print("  v=%-12d : (star) FAILS, margin=%d  <<< INDUCTION BREAKS" % (v, margin))
    SigmaV += v  # I(v) now holds, Sigma grows
print("  (star) holds for first 15 tail atoms:", all_ok)
print()
# --- CHECK §4 gap lemma equals (star) ---
# (star): v <= Sigma_V - 2N0 where Sigma_V = atomSum(<v) (sum of all atoms < v).
# So (star) <=> atomSum(<v) >= v + 2N0 = (GAP). EXACT equivalence. Verify:
print("§4 GAP LEMMA: (star) v <= atomSum(<v) - 2N0  <=>  atomSum(<v) >= v + 2N0:")
def atomSum_below(v):
    return sum(a for a in atoms_all if a < v)
minmargin = 10**18; argmin=None
for v in tail:
    if v > 10**30: break
    asb = atomSum_below(v)
    margin = asb - (v + 2*N0)
    if margin < minmargin: minmargin=margin; argmin=v
print("  min margin (atomSum(<v) - v - 2N0) over tail atoms <=10^30:", minmargin)
import math
print("  attained at v =", argmin, "= 7^%d?" % round(math.log(argmin,7)), 7**round(math.log(argmin,7))==argmin)
print("  Aristotle claims min +2,299,182 at 7^9. Match:", minmargin==2299182, "argmin=7^9:", argmin==7**9)
