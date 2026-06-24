import numpy as np
# ============================================================
# HONEST Brown induction, done right. Maintain R as a growing boolean set.
# Process atoms in SORTED order. After incorporating atoms a_1..a_i, R_i =
# SubsetSums(a_1..a_i). Track the solid block: the largest B_i such that
# [m_i, B_i] ⊆ R_i for the relevant m. The abut when adding a_{i+1}:
# R_{i+1} = R_i ∪ (R_i + a_{i+1}). If R_i ⊇ [m, B_i] solid and a_{i+1} <= B_i - m + 1,
# then R_{i+1} ⊇ [m, B_i + a_{i+1}] (the shifted block abuts). 
# So the condition is a_{i+1} <= (B_i - m + 1) = (current solid block LENGTH).
# B_i grows by a_{i+1} each successful step. Let me run this HONESTLY with the
# TRUE solid block from the sieve as the base, then continue symbolically.
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

# Base: pick a threshold T where R2 is solid on [N0+1, T]. Use sieve to get a
# solid block. The block LENGTH = T - N0. For the induction to continue past T
# using the NEXT atom a, need a <= block length = T - N0.
N=30_000_000
R=build(N)
N0=3982888
# largest T with [N0+1,T] solid:
gaps=np.where(~R[N0+1:N+1])[0]
T = N if len(gaps)==0 else N0+gaps[0]
print("Solid block [N0+1, %d], length L0 = %d" % (T, T-N0))
print()
# Now the atoms above T:
atoms=sorted([3**j for j in range(2,50)]+[4**j for j in range(2,50)]+[7**j for j in range(2,50)])
# Brown induction: block [N0+1, B], B=T. Add atom a > B: need a <= B - N0 (block len).
# Actually we can use ALL atoms in (T, ...] AND re-add to grow. But also atoms in
# (N0, T] are already incorporated. Process atoms > T:
B = T
m = N0+1
ok=True; fail=None; nsteps=0
for a in atoms:
    if a <= B: continue   # already within solid block
    # adding atom a: shifted block [m+a, B+a]. abut to [m,B] iff m+a <= B+1
    if a <= B - m + 1:
        B = B + a; nsteps+=1
    else:
        ok=False; fail=(a, B-m+1, a-(B-m+1)); break
print("Brown induction from solid base, condition 'a <= block_length = B-N0':")
if ok:
    print("  ALL atoms incorporated, B -> infinity after %d steps. L3 CLOSES." % nsteps)
else:
    print("  FAILS at a=%.4e: block_length=%.4e, shortfall=%.4e" % (fail[0],fail[1],fail[2]))
    print("  => after incorporating all atoms < a, solid block is [N0+1, %.4e]," % (B))
    print("     but next atom a=%.4e exceeds block_length+... leaving gap [%.4e, %.4e]" % (fail[0], B+1, fail[0]+N0))
print()
print("So the block length when the FIRST failing atom appears is the key number.")
print("If block length >= atom at every step, L3 closes elementarily. Let me see the")
print("first failure scale.")
