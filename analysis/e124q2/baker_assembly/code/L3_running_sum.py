import numpy as np
# ============================================================
# The CORRECT classical lemma (Brown / "complete sequence" criterion):
# A sorted sequence a_1 <= a_2 <= ... has Sigma (all subset sums) ⊇ [a_1, sum]
# with NO gaps IFF a_{n+1} <= 1 + sum_{i<=n} a_i for all n (the "complete
# sequence" / stamp condition). More precisely, if this holds for all n >= n0
# AND the partial subset-sums up to a_{n0} already form a solid block [0 or a_1, P_{n0}],
# then Sigma ⊇ [start, infinity).
#
# This is the RIGHT condition (running sum of ALL prior atoms, not block-N0).
# I tested a-S(a-) < 18 EARLIER and found it ALWAYS holds (S(a-) > a-18). But
# the complete-sequence condition is a_{n+1} <= 1 + S(a_{n+1}^-) = 1 + (sum of
# ALL atoms strictly less). That's EXACTLY a - S(a-) <= 1. And I found a-S(a-)
# can be up to... let me recheck: earlier "max (a-S(a-)) = -556064" (NEGATIVE!),
# meaning a - S(a-) <= -556064 < 1 ALWAYS. So the complete-sequence condition
# a <= 1 + S(a-) HOLDS (since a < S(a-) by 556064). Let me re-verify carefully --
# my soundness sim used a DIFFERENT (wrong) condition (a <= B-N0). The RIGHT
# condition is a <= 1 + S(a-) where S(a-) = sum of ALL smaller atoms.
# ============================================================
def S_below(a):
    s=0
    for b in (3,4,7):
        p=b*b
        while p<a: s+=p; p*=b
    return s
atoms=sorted(set([3**j for j in range(2,80)]+[4**j for j in range(2,80)]+[7**j for j in range(2,80)]))
print("Testing TRUE complete-sequence condition: a <= 1 + S(a-) [S(a-)=sum ALL smaller atoms]")
maxdef=-10**18; worst=None; viol=0
for a in atoms:
    if a>10**40: break
    s=S_below(a)
    d=a-(1+s)   # >0 means VIOLATION
    if d>maxdef: maxdef=d; worst=a
    if d>0: viol+=1
print("  max(a - 1 - S(a-)) =", maxdef, "(>0 would violate)")
print("  violations:", viol)
print()
# The condition involves ALL atoms below a INCLUDING those below N0. So S(a-)
# accumulates the small atoms 9,16,27,49,... too. Let me verify the FULL subset
# sum from a_1 is solid. Brown's theorem: if a_{i+1} <= 1+sum_{j<=i} a_j for ALL i>=1,
# then Sigma(a_1,...) = [0, total] fully (every value). Check from the SMALLEST atom:
allat=sorted(set([3**j for j in range(2,40)]+[4**j for j in range(2,40)]+[7**j for j in range(2,40)]))
run=0; firstviol=None
for i,a in enumerate(allat):
    if i==0:
        run=a; continue
    if a > 1+run:
        if firstviol is None: firstviol=(i,a,1+run)
    run+=a
print("Brown complete-sequence check from smallest atom (a_1=9):")
print("  smallest atoms:", allat[:8])
print("  first violation a_{i+1} > 1+sum_{<=i}:", firstviol)
# a_1=9, so Sigma starts at 9 not 0/1. The condition a_{i+1}<=1+running.
# 9, then 16 <= 1+9=10? NO (16>10). So GAP between 9 and 16. That's expected --
# small atoms have gaps (that's why N0 exists). The condition holds EVENTUALLY.
print()
print("Find the LAST i where a_{i+1} > 1 + sum_{j<=i} a_j (last complete-seq violation):")
run=0; last_viol=None
for i,a in enumerate(allat):
    if i>0 and a > 1+run: last_viol=(i,a,1+run,a-1-run)
    run+=a
print("  last violation:", last_viol)
