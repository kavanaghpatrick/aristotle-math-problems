import numpy as np, math
log3=math.log(3); log4=math.log(4); log7=math.log(7)
# ============================================================
# Test baker's "margin GROWS above N0" claim for the fixed-(3,4,7) k=2 joint
# covering at the (3,4)-COINCIDENCE gaps. If the min B7-rep count at coincidence
# gaps grows (or stays bounded below by >=1 with growing slack), the joint
# covering lemma is provable for the fixed triple => L3 closes (ending i for
# fixed k=2, non-uniform constant).
#
# A (3,4)-coincidence gap sits just below 3^p ~ 4^q (a CF convergent of log3/log4).
# For k=2: the relevant powers are 3^p, 4^q with the B3+B4 gap ending at the power.
# At each such gap, measure: over interior points, the MIN number of B7 subset-sums
# c with (n-c) in B3+B4 (the "rep count"). If min >= 1 with GROWING margin, covered.
# ============================================================
def build(N):
    b3b4=np.zeros(N+1,bool);b3b4[0]=True
    for x in sorted([3**j for j in range(2,18)]+[4**j for j in range(2,15)]):
        if x<=N:b3b4[x:]|=b3b4[:N+1-x].copy()
    b7=np.zeros(N+1,bool);b7[0]=True
    for x in sorted([7**j for j in range(2,12)]):
        if x<=N:b7[x:]|=b7[:N+1-x].copy()
    return b3b4, b7

N=60_000_000
b3b4,b7=build(N)
b7vals=np.where(b7)[0]
N0=3982888

# rep count r(n) = #{c in B7 : n-c in B3+B4}, for n in a window. Vectorized per gap.
def repcount_window(lo, hi):
    # for n in [lo,hi], count c in b7vals with c<=n and b3b4[n-c]
    res=np.zeros(hi-lo+1, dtype=int)
    rel=b7vals[b7vals<=hi]
    for c in rel:
        idx0=max(lo, c)
        # n from idx0..hi: b3b4[n-c]
        ns=np.arange(idx0,hi+1)
        res[ns-lo]+= b3b4[ns-c]
    return res

# Find (3,4)-coincidence gaps: B3+B4 gaps ending just below a power of 3 or 4.
# Locate the largest B3+B4 gaps in the tail and their min rep count.
nonr=~b3b4; nonr[0]=False
idx=np.where(nonr)[0]
gaps=[]
if len(idx):
    s=idx[0];p=idx[0]
    for x in idx[1:]:
        if x==p+1:p=x
        else:gaps.append((s,p));s=x;p=x
    gaps.append((s,p))
gaps=[(a,b,b-a+1) for a,b in gaps if b-a+1>5000]  # significant gaps only
gaps.sort()
print("Min B7-rep count over interior of significant B3+B4 gaps (k=2), by location:")
print(" gap location (end) | width | min rep-count over interior | ends-at-power")
powers3={3**j for j in range(2,20)}; powers4={4**j for j in range(2,20)}
for a,b,w in gaps:
    if b > N-10**6: continue
    rc=repcount_window(a,b)
    minrc=int(rc.min())
    endpow = "3^%d"%round(math.log(b+1,3)) if (b+1) in powers3 else ("4^%d"%round(math.log(b+1,4)) if (b+1) in powers4 else "-")
    region = "BELOW N0" if b<N0 else "ABOVE N0"
    print("  %10d | %7d | min rep=%3d | %-6s | %s" % (b,w,minrc,endpow,region))
print()
print("baker's claim: min rep-count >= 1 with GROWING margin above N0. If min rep-count")
print("at coincidence gaps (those ending at/near 3^p~4^q) stays >= 1 and grows, the")
print("fixed-triple joint covering is provable => L3 closes for k=2 (non-uniform const).")
