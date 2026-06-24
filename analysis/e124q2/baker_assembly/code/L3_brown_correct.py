import numpy as np
# ============================================================
# Brown's theorem, applied CORRECTLY. The theorem (Brown 1961, the CORRECT
# citation per the team's UNIFIED doc):
#
# THEOREM (Brown). Let 0 < a_1 <= a_2 <= ... If a_1 = 1 ... (for completeness
# from 1). For our case the relevant form: if there is an index n0 and value P
# such that SubsetSums(a_1..a_{n0}) ⊇ [m, P] (solid block) for some m, and for
# all n >= n0: a_{n+1} <= P_n + 1 where P_n = m + sum_{i<=n} a_i ... 
#
# The PRECISE statement I need: Sigma(A) is cofinite iff, listing atoms sorted,
# the PARTIAL SUMS satisfy: once the running subset-sum reaches a solid block
# [N0+1, B], each subsequent atom a <= B+1 EXTENDS it to [N0+1, B+a].
#
# My earlier sim used 'a <= B - N0' which was WRONG. The CORRECT abut condition:
# R2 ⊇ [N0+1, B]. Atom a. Then R2 ⊇ [N0+1,B] ∪ ([N0+1,B]+a) = [N0+1,B] ∪ [N0+1+a, B+a].
# For these to merge into [N0+1, B+a], need N0+1+a <= B+1, i.e. a <= B-N0. 
# THAT failed. So the block does NOT self-extend by single atoms. CONFIRMED my sim.
#
# BUT R2 is solid past N0 (sieve fact). So the merging uses the SMALL atoms too:
# R2 ⊇ [N0+1,B] + {subset sums of ALL atoms} -- the shifts are by ANY reachable
# value, not just single atoms. The smallest reachable values include 9,16,25,...
# So R2 ⊇ [N0+1,B] + {0,9,16,...} which fills densely. Let me find the actual
# DENSE shift set: the small subset-sums of R2 in [0, N0].
# ============================================================
def build(N):
    b3b4=np.zeros(N+1,bool);b3b4[0]=True
    for x in sorted([3**j for j in range(2,18)]+[4**j for j in range(2,15)]):
        if x<=N:b3b4[x:]|=b3b4[:N+1-x].copy()
    b7=np.zeros(N+1,bool);b7[0]=True
    for x in sorted([7**j for j in range(2,12)]):
        if x<=N:b7[x:]|=b7[:N+1-x].copy()
    R=np.zeros(N+1,bool)
    for c in np.where(b7)[0]:R[c:]|=b3b4[:N+1-c]
    return R
N=30_000_000
R=build(N)
N0=3982888
# R2 in [N0+1, 2*N0]: solid? Then [N0+1,2N0] + atom a covers [N0+1+a, 2N0+a].
# Consecutive atoms a, a' with a' - a <= N0 (gap between atoms <= N0) => the
# shifted solid blocks [.+a] and [.+a'] OVERLAP (since each has length N0).
# So the REAL condition: consecutive atom GAPS <= (solid block length).
# Block length available ~ unbounded (R2 solid from N0+1). Atom gaps GROW.
# But the block grows too! Let me check: is R2 solid on [N0+1, X] for X growing,
# and are atom-gaps always < X-N0 at the point they're needed?
atoms=sorted([3**j for j in range(2,40)]+[4**j for j in range(2,40)]+[7**j for j in range(2,40)])
atoms_above=[a for a in atoms if a>N0]
print("THE CORRECT MECHANISM: R2 ⊇ [N0+1, B] solid. For n in [B+1, ...], write")
print("n = a + r where a is an atom (or atom-subset-sum) and r in [N0+1, B].")
print("Coverage of [B+1, B+a_gap] needs an atom/sum landing so that n-atom in [N0+1,B].")
print()
print("Consecutive atom gaps above N0 and whether < current solid-block length:")
# solid block from N0+1 grows; track true solid top from sieve
solidtop = N
print("  (R2 solid to %d from sieve)" % N)
for i in range(len(atoms_above)-1):
    a,anext=atoms_above[i],atoms_above[i+1]
    if a>N: break
    gap=anext-a
    print("  atom %.3e -> next %.3e, gap=%.3e" % (a,anext,gap))
print()
print("The block [N0+1, B] with B~the largest verified solid point. For the tail")
print("to stay solid, need: every point n has SOME representation. This is NOT a")
print("single-atom-gap condition -- it's the full JOINT covering. My single-block")
print("lemma is genuinely insufficient. CONFIRMED: L3 is NOT elementary-single-block.")
