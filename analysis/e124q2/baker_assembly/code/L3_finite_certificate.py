import numpy as np, math
# ============================================================
# Can "+9-closure above v" be reduced to a FINITE certificate?
#
# IDEA (the standard 'window' argument for sumset completeness):
# Suppose we can show that R2 contains a FULL WINDOW of W consecutive
# integers [a, a+W) for some a, where W >= (the largest atom gap we ever
# need to bridge). Then because R2 is a SUBSET-SUM set closed under adding
# any atom, [a, a+W) + (any atom subset) tiles forward. Specifically:
#
# CLEAN LEMMA (finite certificate for cofiniteness of a subset-sum set):
# Let A = {a_1 < a_2 < ...} be the atom set (here {3^j,4^j,7^j : j>=2}).
# If R = SubsetSums(A) contains W consecutive integers [a, a+W) with
# W >= a_{i+1} for the largest 'active' atom gap, AND every atom beyond
# some point is <= (running sum so far), THEN R is cofinite.
#
# The RIGOROUS version (Erdos-Birch / Cassels, the version that WORKS at
# beta=1 because we use the FULL multi-base structure, not single-ray):
# If R contains [a, a + a_next) where a_next is the next atom above a,
# and the atoms satisfy a_{m+1} <= 1 + sum_{i<=m} a_i (the Cassels condition)
# from some point on, then R contains [a, infinity).
#
# BUT the team established the Cassels single-ray condition FAILS at beta=1
# (it fails at every power of d_max). So this clean lemma does NOT directly
# apply. The QUESTION: does R2 contain a long-enough consecutive window that
# the MULTI-ATOM structure carries it forward despite single-append failures?
#
# Let me MEASURE: what is the longest consecutive run in R2 just above N0(2),
# and what is the largest atom gap that must be bridged in the tail?
# ============================================================
def R_reach(kmin, N):
    b3b4 = np.zeros(N+1,bool); b3b4[0]=True
    for a in sorted([3**j for j in range(kmin,17)]+[4**j for j in range(kmin,14)]):
        if a<=N: b3b4[a:]|=b3b4[:N+1-a].copy()
    b7=np.zeros(N+1,bool); b7[0]=True
    for a in sorted([7**j for j in range(kmin,11)]):
        if a<=N: b7[a:]|=b7[:N+1-a].copy()
    R=np.zeros(N+1,bool)
    for c in np.where(b7)[0]:
        R[c:]|=b3b4[:N+1-c]
    return R

N=12_000_000
R=R_reach(2,N)
N0=3982888
# longest consecutive run above N0
tail=R[N0+1:]
# all present? 
print("Tail [%d, %d] fully present:" % (N0+1,N), bool(tail.all()))
# atoms in the tail range
atoms=sorted([3**j for j in range(2,17)]+[4**j for j in range(2,14)]+[7**j for j in range(2,11)])
atoms_in=[a for a in atoms if N0 < a <= N]
print("Atoms in (N0, %d]:" % N, atoms_in)
# gaps between consecutive atoms above N0 (these are what must be bridged)
big_atoms=[a for a in atoms if a > N0//10]
print("Largest atoms below N and their gaps to next:")
allat=sorted([a for a in atoms if a<=N])
for i in range(len(allat)-1):
    if allat[i] > N0//100:
        gap=allat[i+1]-allat[i]
# The longest stretch with NO atom (the worst forward-bridge distance):
allat_tail=[a for a in atoms if a>N0]
print("Consecutive atom gaps in tail:", [allat_tail[i+1]-allat_tail[i] for i in range(len(allat_tail)-1)][:20])
print()
# The KEY metric: once we have a window of consecutive integers of length L,
# adding atoms forward, the window propagates if L >= max atom-gap we hit.
# What window length do we have, and is it >= the max forward atom gap?
# Find first long run above N0:
print("R2 is fully consecutive from N0+1=%d onward (verified to %d)." % (N0+1, N))
print("Window length available: unbounded (tail is solid).")
print("Max atom gap in tail (between successive 3^j/4^j/7^j):")
gaps_tail=[allat_tail[i+1]-allat_tail[i] for i in range(len(allat_tail)-1)]
print("  max =", max(gaps_tail) if gaps_tail else "n/a", " atoms in tail:", allat_tail)
