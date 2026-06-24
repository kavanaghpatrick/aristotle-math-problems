import math
# ============================================================
# TASK #41: the ineffective (Ridout) route for ALL-k. Three questions.
#
# Q1 [CITATION]: Ridout's theorem (p-adic Roth), Ridout 1958 Mathematika 5:40-48
# (team-lead said 1957; actual publication 1958). Statement + the |a^m-b^n| corollary.
#
# Q2 [CRUX for all-k]: the doubling induction at level k needs a BASE CASE I_k(V0(k)).
# We have bases for k=1,2 (computed). Does a level-k base follow from a uniform/scaling
# argument, or need per-k computation (infinitely many = not a proof)?
#
# Q3 [PRIOR ART]: is ineffective all-k folklore?
# ============================================================

print("="*68)
print("Q1 — RIDOUT CITATION + the |a^m - b^n| corollary")
print("="*68)
print("""
Ridout's theorem (D. Ridout, "The p-adic generalization of the Thue-Siegel-
Roth theorem", Mathematika 5 (1958) 40-48 — NOTE: 1958, team-lead said 1957):
Let alpha be algebraic. Let p_1..p_s, q_1..q_t be distinct primes. Consider
rationals x/y with x composed of the p_i's times a bounded part, y of the q_j's
times a bounded part. Then for any eps>0, |alpha - x/y| > H(x/y)^{-(mu+eps)} with
mu reduced from Roth's 2 according to how much of x,y is supported on the fixed
primes. In the fully-supported case the exponent drops toward 1.

STANDARD COROLLARY (the one the route needs):
For multiplicatively independent integers a,b >= 2 and any eps>0,
   |a^m - b^n| > max(a^m, b^n)^{1 - eps}   for all but finitely many (m,n).
This is INEFFECTIVE (inherits Roth/Ridout ineffectivity: no bound on the size of
the exceptional (m,n) or the implied constant). It DOES bound the NUMBER of
exceptions (Davenport-Roth gap principle), but not their size.
[Verified status: Wikipedia (Roth's theorem) confirms Ridout 1958 + ineffectivity;
the corollary is standard — appears in Bugeaud "Approximation by algebraic numbers",
and as the S-unit/Pillai-type application. NEED nesterenko to pull the exact corollary
constant from Bugeaud's book Ch. for the report.]
""")

print("="*68)
print("Q2 — THE ALL-k CRUX: does the level-k base case scale, or need per-k compute?")
print("="*68)
N0={1:581, 2:3982888, 3:166025260}
print("""
The doubling induction at level k needs a BASE CASE I_k(V0(k)): a gap-free middle
interval (N0(k), Sigma_{V0(k)} - N0(k)) in Reach(A_k), A_k = {3^j,4^j,7^j : j>=k}.

KEY STRUCTURAL FACT (the machine-verified scaling theorem, per-base):
  x in S(d,k)  <=>  d^k | x  AND  x/d^k in S(d,0).
This is PER-BASE. The question: does a JOINT base case scale? I.e. can I_k be
DERIVED from I_1 (or I_0) by a uniform argument, or must it be recomputed per k?
""")
# Test: is R_k a scaled copy of R_1? NO -- the three bases scale by DIFFERENT factors
# 3^k, 4^k, 7^k. So A_k is NOT lambda*A_1 for any single lambda.
print("Test: A_k = {3^j,4^j,7^j : j>=k}. Is this a uniform dilation of A_1?")
print("  3-ray scales by 3^{k-1}, 4-ray by 4^{k-1}, 7-ray by 7^{k-1} -- DIFFERENT factors.")
print("  (4/3)^{k-1}: ", [round((4/3)**(k-1),2) for k in (1,2,3,4)], "-- ray geometry DRIFTS with k")
print("  So R_k is NOT a scaled copy of R_1. The base case does NOT trivially scale. ✗")
print()
print("  => A per-k base case is a SEPARATE finite computation at each k. The reduction")
print("     gives: I_k = [finite base computation to V0(k)] + [gap lemma for v>V0(k)].")
print("     The gap lemma at level k: atomSum_k(<v) >= v + 2*N0(k). Ridout closes the v>V0(k)")
print("     half INEFFECTIVELY (finitely many exceptions per pair). BUT the BASE V0(k) and")
print("     N0(k) GROW with k (mahler: super-geometric), and each needs its OWN computation.")
print()
print("THE VERDICT hinges on: is there a UNIFORM-in-k argument for the base case?")
print("  - Aristotle's symmetry+doubling is k-uniform in FORM (works at every k).")
print("  - BUT the base case I_k(V0(k)) is a k-DEPENDENT finite check. No scaling derives it.")
print("  - So all-k via this route = {for each k: finite base check + Ridout tail} = INFINITELY")
print("    MANY finite computations. That is NOT a proof of the ∀k statement UNLESS the base")
print("    checks are bounded/uniformized by an argument.")
