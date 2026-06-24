import math
# ============================================================
# L3 WRITTEN OUT (the finite certificate for the infinite tail).
#
# CLAIM (window propagation, the rigorous closure): Let A = sorted atoms
# {3^j,4^j,7^j : j>=2}. Suppose R2 = SubsetSums(A) contains the solid block
# [N0+1, T] for some T, and let S(x) = sum of atoms <= x. Then for any atom
# a with N0 < a <= S(a-1)+1 ... actually the clean statement:
#
# LEMMA (Cassels forward, MULTI-ATOM form). If [L, T] subset R with
# T - L + 1 >= 1 (nonempty solid block) and EVERY atom a > T satisfies
#   a <= 1 + (sum of all atoms < a)               (*)
# then R contains [L, infinity).
# Proof: induct. Adding atoms one at a time in increasing order. When we add
# atom a, R already contains [L, T'] where T' = sum of atoms in (prev, a) plus
# old block >= a-1 by (*). So [L,T'] and [L,T']+a = [L+a, T'+a] overlap or abut
# (since a <= T'+1), giving solid [L, T'+a]. QED.
#
# So L3 reduces to verifying (*): every atom a > N0 is <= 1 + sum of smaller atoms.
# This is a FINITE-to-check condition IF it holds for all atoms beyond some point
# by a clean monotone argument. Let me CHECK (*) for the tail atoms.
# ============================================================
N0=3982888
atoms=sorted([3**j for j in range(2,200)]+[4**j for j in range(2,200)]+[7**j for j in range(2,200)])
# cumulative sum
cum=0
prev_sum={}
fails=[]
cumsum=0
running=[]
S=0
atom_list=atoms
# compute for each atom a, sum of all atoms strictly less than a
import bisect
sorted_atoms=atoms
prefix=[0]
for a in sorted_atoms:
    prefix.append(prefix[-1]+a)
def sum_below(a):
    i=bisect.bisect_left(sorted_atoms,a)
    return prefix[i]
print("Checking Cassels forward condition (*): atom a <= 1 + sum(atoms < a), for a > N0")
print("a, sum_below(a), holds?")
first_fail=None
for a in sorted_atoms:
    if a<=N0: continue
    if a>10**40: break
    sb=sum_below(a)
    holds = a <= 1+sb
    if not holds and first_fail is None:
        first_fail=a
    if a < 10**12:
        print("  a=%-14d sum_below=%-16d holds=%s" % (a, sb, holds))
print()
if first_fail:
    print(">>> (*) FAILS first at a =", first_fail, "(log10=%.1f)" % math.log10(first_fail))
    print("    So pure single-atom Cassels forward does NOT close it -- as expected (beta=1).")
else:
    print(">>> (*) HOLDS for all atoms up to 10^40. If it holds forever, L3 is PROVEN finitely.")
