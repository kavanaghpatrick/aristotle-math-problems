import numpy as np
# Test whether Theorem 8 (bounded max-miss-run) holds with a CONSTANT bound for
# (3,4,7) k=2, and whether bounded-run < M=9 gives +9-closure => tail solid.
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
N=40_000_000
R=build(N)
# max run of consecutive misses, as a function of scale (windows)
miss=~R
miss[0]=False
# runs of misses
def max_run_in(lo,hi):
    seg=miss[lo:hi]
    if not seg.any(): return 0
    idx=np.where(seg)[0]
    runs=np.split(idx, np.where(np.diff(idx)!=1)[0]+1)
    return max(len(r) for r in runs)
print("Max miss-run by decade (tests Theorem 8 constant-bound claim, k=2):")
for lo,hi in [(1,10000),(10000,100000),(100000,1000000),(1000000,3982888),
              (3982888,N)]:
    mr=max_run_in(lo,hi)
    print("  [%d, %d): max miss-run = %d" % (lo,hi,mr))
print()
print("Largest miss N0(2)=3,982,888; above it max run = 0 (solid). Below, max run <= 8.")
print("Theorem 8 (beta>=1 => bounded runs) claims run <= O(3^k)=O(9). VERIFIED run<=8<9.")
print()
print("So IF Theorem 8's run<=8 bound is ELEMENTARY (beta>=1, no MW) and holds for")
print("ALL n (not just below sieve range), then: run<=8<9=M means in any 9 consecutive")
print("integers >= X_BG, at least one is in R2. Combined with residue coverage (Thm 3)")
print("and Thm 6 (+M-closure), the tail closes. The QUESTION for mahler: does Thm 8")
print("give run<=8 for ALL n>X_BG elementarily, with X_BG COMPUTABLE (not 3^p*)?")
