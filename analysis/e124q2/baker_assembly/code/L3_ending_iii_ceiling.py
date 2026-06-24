import math
log3=math.log(3); log4=math.log(4); log7=math.log(7)
# ============================================================
# ENDING (iii): quantify the finite-but-large verification ceiling for L3.
#
# The rigorous closure that DOES work (team Theorem 8 + the bounded-gap upgrade):
# (1) Theorem 8 (Lemma BG): beta>=1 => R2 has BOUNDED gaps, <= G = O(d_min^k)=O(3^k).
#     Actually the bound is ~ 2*(largest atom)^... the team's G(k) ~ d_min^k. For
#     a FIXED triple the max gap above the transient is bounded by a CONSTANT G2.
# (2) The bounded gap G2, combined with residue coverage mod M (Theorem 3) and
#     the +M-closure (Theorem 6, M=9), gives: once R2 has a run of M=9 consecutive
#     AND no +M-failure above V, the tail is solid. 
# (3) The +M-closure FAILURES are what MW bounds: a +9-failure at n means n in R2,
#     n+9 not. These occur at cross-base notches. MW => finitely many, last at
#     v=N0-9=3,982,879 (VERIFIED). 
#
# So the RIGOROUS ceiling: we must verify NO +9-closure failure occurs above
# v=3,982,879. The +9-failures correspond to n where n+9 falls in a deep notch.
# By MW, the deepest notch above scale X has relative depth >= exp(-C(log p)^2).
# A +9-failure needs the notch to be deeper than the local B7 covering can fill.
# The LAST possible +9-failure is bounded by where MW guarantees the notch is
# shallower than 9/n (so +9 can't escape coverage). Let me bound this.
# ============================================================
# A +9-closure failure at n: n in R2 but n+9 not in R2. For n+9 to be a MISS,
# n+9 must avoid ALL representations = sit at a deep multi-ray notch. The notch
# depth (how isolated) is governed by the cross-base spacing. The team verified
# the LAST +9-failure is at 3,982,879 (= N0(2)-9). To PROVE no failure above it,
# the bounded-gap argument needs: above N0, max gap G2 < 9 forces +9-closure... 
# no. Let me think about what finite check certifies the infinite tail.
#
# The cleanest RIGOROUS finite certificate (this is the real ending-iii answer):
# The team's Theorem 6: N0 = v + M where v = last +M-closure failure. To prove
# v <= V (some bound) we need: for all n > V, n in R2 => n+M in R2. 
# Equivalent: for all n > V+M, if n in R2 then n-M in R2 (downward +M-closure) OR
# n itself reachable. The forward statement is certified once R2 has M consecutive
# reachables and the atom structure gives +M-closure. The +M-closure HOLDS once
# the running atom sum dominates locally -- which by Theorem 8 happens above the
# bounded-gap transient. For (3,4,7), what is that transient bound rigorously?
#
# HONEST ANSWER: the bounded-gap transient for a FIXED triple is itself only
# known to be bounded by the MW crossover p* (where the spacing self-certifies),
# i.e. height 3^p* ~ 10^140000. Below that, it's a finite-but-astronomical check.
# UNLESS the bounded-gap G2 can be shown constant by an elementary argument.
print("ENDING (iii) ceiling analysis:")
print()
print("The rigorous tail closure = 'no +9-closure failure above v=3,982,879'.")
print("This is certified IF: (Thm 8) R2 has bounded gaps above a transient X_BG, AND")
print("(MW/L1) no deep notch above X_BG can create a +9-failure.")
print()
print("Two sub-questions:")
print("  Q1: is the bounded-gap bound G2 a CONSTANT for the fixed triple (elementary)?")
print("  Q2: what scale X_BG must the sieve reach to certify it?")
print()
# Theorem 8 bound: G ~ 2*d_min^k? team says runs bounded by O(d_min^k). For k=2,
# d_min^k = 9. But the ACTUAL max run of MISSES (not gap) -- let me get max gap above N0.
# Above N0 max gap is 1 (solid). The relevant 'gap' is in the +M-closure sense.
print("Theorem 8 gives max-RUN-of-misses <= O(3^k); for k=2 the verified max run is 8")
print("(team: (3,4,7) k=2 has max run 8 ≈ 3^2). A run of misses <= 8 < M=9 means once")
print("we pass a run, +9 lands in reachable territory. THIS is the elementary closure:")
print("  IF max-miss-run <= 8 for ALL n > X_BG (bounded by Thm 8, beta>=1, ELEMENTARY),")
print("  AND R2 has a reachable in every window of 9 above X_BG,")
print("  THEN +9-closure holds => tail solid.")
print()
print(">>> THE CRUX REDUCES TO: is 'max-miss-run <= 8 for all n > X_BG' ELEMENTARY")
print("    (Thm 8, no MW) or does it need MW? If Thm 8 (bounded gap from beta>=1) is")
print("    genuinely elementary and gives run <= G2=O(3^k) as a CONSTANT, then L3 is")
print("    ELEMENTARY above X_BG and we just need the finite check to X_BG. <<<")
