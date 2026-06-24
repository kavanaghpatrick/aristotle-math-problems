import numpy as np, math
# ============================================================
# L3, written out via +M-closure (team Theorem 6, M = d_min^k = 3^2 = 9).
#
# THEOREM 6 (Lemma C): R is cofinite IFF it has finitely many +M-closure
# failures, where a +M-closure failure at n means: n in R but n+M not in R.
# Quantitatively N0 = v + M where v = max{n : n in R, n+M not in R}.
#
# The POINT: if we can show R2 has NO +M-closure failure above some
# COMPUTABLE bound V, then the tail above V+M is gap-free, REDUCING the
# infinite problem to a finite check to V. So L3 = "find V and verify no
# +M-failure above it" + "verify [N0, N0+M) all present".
#
# But the SAME issue recurs: why no +M-failure above V? A +M-failure is
# n in R, n+9 not in R. We need to bound the largest such n. Let me first
# MEASURE where the last +M-closure failure actually is for R2.
# ============================================================
def R_reach(kmin, N):
    b3b4 = np.zeros(N+1,bool); b3b4[0]=True
    for a in sorted([3**j for j in range(kmin,16)]+[4**j for j in range(kmin,13)]):
        if a<=N: b3b4[a:]|=b3b4[:N+1-a].copy()
    b7=np.zeros(N+1,bool); b7[0]=True
    for a in sorted([7**j for j in range(kmin,10)]):
        if a<=N: b7[a:]|=b7[:N+1-a].copy()
    R=np.zeros(N+1,bool)
    for c in np.where(b7)[0]:
        R[c:]|=b3b4[:N+1-c]
    return R

M=9
N=8_000_000
R=R_reach(2,N)
# +M-closure failures: n in R and n+M not in R
present=R[:N+1-M]
nextM=R[M:N+1]
failures=np.where(present & ~nextM)[0]
print("k=2, M=9: +M-closure failures (n in R, n+9 not in R):")
print("  count below %d:" % N, len(failures))
print("  largest +M-failure v =", int(failures.max()) if len(failures) else None)
print("  => Theorem 6 predicts N0 = v + M =", int(failures.max())+M if len(failures) else None)
print("  actual N0(2) = 3,982,888")
# misses
miss=np.where(~R[1:])[0]+1
print("  largest miss (independent):", int(miss.max()))
print()
# Now the KEY question: is the largest +M-failure BELOW our sieve range?
v=int(failures.max())
print("Largest +M-closure failure at v=%d, well within sieve range (%d)." % (v,N))
print("So IF we can prove no +M-failure occurs in (v, infinity), the tail closes.")
print("Equivalently: prove that for all n > v, [n, n+9) cannot have n present but n+9 absent,")
print("i.e. R2 is +9-closed above v. This is a statement about the LOCAL structure of R2.")
