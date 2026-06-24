# k=0 memory-light probe of (3,4,11): n = a3+a4+a11, a_d ANY 0/1-digit base-d number (j>=0).
def S_d0_set(d, N):
    vals=[0]; j=0
    while d**j<=N:
        p=d**j; vals=vals+[v+p for v in vals if v+p<=N]; j+=1
    return set(vals)
def in_S_d0(x,d):
    if x<0: return False
    while x>0:
        if x%d not in (0,1): return False
        x//=d
    return True
def representable_k0(n,S3):
    S11=S_d0_set(11,n)
    for a11 in S11:
        rem=n-a11
        for a3 in S3:
            if a3>rem: continue
            if in_S_d0(rem-a3,4): return True
    return False
# density predicts forced misses just below d_min^m = 3^m. Probe densely just below 3^m.
for m in [16,17,18,19,20]:
    q=3**m
    S3=S_d0_set(3,q)
    # dense sample: every point in [q-3000, q)
    band=range(q-3000,q)
    miss=[n for n in band if not representable_k0(n,S3)]
    print(f"k=0 just below 3^{m}={q}: {len(miss)}/3000 non-representable" + (f"  e.g. {miss[:6]} (max {max(miss)}, dist below 3^m: {q-max(miss)})" if miss else ""))
