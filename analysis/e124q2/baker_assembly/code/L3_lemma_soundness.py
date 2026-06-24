import numpy as np
# ============================================================
# SOUNDNESS TEST of the window-propagation lemma, stated precisely:
#
# LEMMA. Atoms sorted a_1<a_2<.... R=SubsetSums. Suppose R contains solid
# [L,T]. Process atoms a>T in increasing order. Maintain solid [L,B] (B=T init).
# When adding atom a: the set R-so-far (atoms <a) contains [L,B]. Adding a gives
# also [L+a, B+a]. These two intervals UNION to [L, B+a] IFF L+a <= B+1
# (abut/overlap), i.e. a <= B-L+1. If so, B <- B+a. If NOT (a > B-L+1), a GAP
# opens at [B+1, L+a-1] and the block does NOT extend -- FAILURE.
#
# So the REAL condition per atom is: a <= B - L + 1, where B is the CURRENT
# block top (which has accumulated ALL smaller atoms). Since B-L+1 = (block
# length) and the block has absorbed sum of all atoms < a (plus initial T-L+1),
# B - L >= S(a^-) + (T - L). Wait, that's only if every smaller atom abutted.
# Let me SIMULATE honestly: start with the TRUE solid block [N0+1, first_atom),
# then apply ONLY the lemma's append rule and see if it stays gap-free.
# ============================================================
N0=3982888
# atoms above N0
atoms=sorted([3**j for j in range(2,60)]+[4**j for j in range(2,60)]+[7**j for j in range(2,60)])
atoms_above=[a for a in atoms if a>N0]

# initial solid block [L, B]; L=N0+1, B = (first atom above N0) - 1
L=N0+1
B=atoms_above[0]-1   # solid up to just before first atom (verified by sieve)
print("Initial solid block [%d, %d], length %d" % (L,B,B-L+1))
print()
# But WAIT: the block [L,B] is solid in R2, and R2 ALSO contains subset sums
# using atoms BELOW N0. So when we add atom a, the reachable set shifted by a
# is not just [L+a,B+a] -- it's (everything in R2 below) + a. The lemma as I
# stated is too weak. The CORRECT statement uses: R2 restricted to [0, a) is
# rich. Let me test the HONEST lemma: does B (block top) satisfy, for each
# successive atom a, a <= B+1 (so the shifted block [a, ...] abuts [0..B])?
# Using B as the running max-solid-from-0... no, R2 isn't solid from 0.
#
# CORRECT framing: R2 ⊇ [N0+1, B]. For atom a, R2 ⊇ [N0+1,B] + {0,a} = 
#   [N0+1,B] ∪ [N0+1+a, B+a]. Union solid iff N0+1+a <= B+1 iff a <= B-N0.
# So condition: a <= B - N0. Then B <- B+a.
ok=True; failed_at=None
for a in atoms_above:
    if a <= B - N0:
        B = B + a   # block extends to B+a
    else:
        ok=False; failed_at=(a, B, a-(B-N0)); break
print("Applying append rule 'a <= B - N0 => B += a':")
if ok:
    print("  ALL atoms appended successfully; block -> infinity. LEMMA SOUND for the run.")
else:
    print("  FAILED at atom a=%d: a=%d > B-N0=%d (gap of %d)" % (failed_at[0],failed_at[0],B-N0,failed_at[2]))
print("  Final block top reached: %.3e (after %d atoms)" % (B, len(atoms_above)))
print()
# Cross-check against TRUE sieve to moderate N
def R_reach(N):
    b3b4=np.zeros(N+1,bool);b3b4[0]=True
    for x in sorted([3**j for j in range(2,17)]+[4**j for j in range(2,14)]):
        if x<=N:b3b4[x:]|=b3b4[:N+1-x].copy()
    b7=np.zeros(N+1,bool);b7[0]=True
    for x in sorted([7**j for j in range(2,11)]):
        if x<=N:b7[x:]|=b7[:N+1-x].copy()
    R=np.zeros(N+1,bool)
    for c in np.where(b7)[0]:R[c:]|=b3b4[:N+1-c]
    return R
N=20_000_000
R=R_reach(N)
print("TRUE sieve: R2 gap-free on [N0+1, %d]?" % N, bool(R[N0+1:N+1].all()))
print()
print("The append condition 'a <= B - N0' is what must hold for every atom a>N0.")
print("Check it directly: for each atom a, is a <= (sum of all atoms in (N0,a)) + (init block)?")
# init block top before any append = atoms_above[0]-1; B-N0 initially = atoms_above[0]-1-N0
Binit=atoms_above[0]-1
runB=Binit
print("  atom a | B-N0 (capacity) | a <= B-N0 ? | new B")
for a in atoms_above[:12]:
    cap=runB-N0
    okk = a<=cap
    if okk: runB+=a
    print("  %-12d | %-15d | %s | %.3e" % (a, cap, okk, runB))
