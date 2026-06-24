import numpy as np
# ============================================================
# What ACTUALLY keeps R2 gap-free past N0? My single-block lemma was wrong.
# The truth: n is covered by SUBSET SUMS using atoms both below AND above N0.
# Let me find the real invariant. For a target n in (4194303, 4194304+X), it's
# covered as n = (atom 4^11=4194304) + (something in R2 below n-4194304), where
# n - 4194304 ranges over [1, X]. Since R2 is solid on [N0+1, 4194303] AND
# contains small values, n-4194304 in [1,X] must be in R2.
# But n-4194304 could be < N0+1 (in the pre-N0 range with holes)!
# So coverage just above an atom a uses R2 ∩ [0, small], which is NOT solid.
#
# The REAL mechanism (let me discover it empirically): for n just above atom a,
# n = a + m where m must be in R2. The set {a + R2} covers [a, a+max] where R2
# is solid. R2 is solid from N0+1. So a + (R2 ∩ [N0+1, ...]) covers [a+N0+1, ...].
# That leaves [a+1, a+N0] potentially uncovered by THIS atom -- but covered by
# OTHER atoms or atom-combinations. Let me just identify: above the LARGEST atom
# below n, what covers n?
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
    return R,b3b4,b7
N=30_000_000
R,b3b4,b7=build(N)
N0=3982888
print("R2 gap-free [N0+1,%d]:"%N, bool(R[N0+1:N+1].all()))
print()
# The key structural fact: what is the LONGEST solid run, and does it just keep
# growing? The real lemma must be: R2 contains a solid block [N0+1, B] and B grows
# to infinity because R2 = R2 + {0, atom} keeps the block growing whenever a new
# atom a satisfies a <= B (NOT B - N0). Let me test 'a <= B => B = max(B, B+a)'...
# Actually n=a+m, m in [N0+1,B] solid => covers [a+N0+1, a+B]. For this to EXTEND
# [N0+1,B] we need a+N0+1 <= B+1, i.e. a <= B - N0. Same condition -- and it fails.
# So a SINGLE atom never extends the block. It must be CUMULATIVE: the block top B
# is the largest n with [N0+1,n] solid; adding ALL atoms' shifts together.
# Let me measure B (true solid top) as a function of N -- does it track N (grow)?
solid_top=N0
# find first gap above N0
gaps=np.where(~R[N0+1:N+1])[0]
print("First gap above N0:", "NONE (solid to %d)"%N if len(gaps)==0 else N0+1+gaps[0])
print()
# So R2 IS solid from N0+1 to 30M. The mechanism keeping it solid: every n is
# n = sum of atoms. Coverage is GLOBAL (all atoms jointly), confirmed by sieve.
# My error: treating it as one shifted block. The HONEST closure argument must be
# either (a) the team's bounded-gap + something, or (b) a genuinely finite-but-large
# verification, or (c) needs the open lemma.
print("VERDICT REVISION: my elementary single-block window lemma is REFUTED by")
print("simulation. R2's gap-freeness past N0 is a JOINT multi-atom property, exactly")
print("baker's FACE-2. The sieve verifies it to 30M but the INFINITE tail is NOT")
print("closed by an elementary single-block induction. This is ending (ii)/(iii):")
print("the closure needs either the open uniform covering lemma, or a finite-but-")
print("large verification whose ceiling I must now bound HONESTLY.")
