# Probe (3,4,11) k=1 representability just below high powers of d_min=3 (density's Weyl prediction).
def S_d1_set(d, N):
    vals=[0]; j=1
    while d**j<=N:
        p=d**j; vals=vals+[v+p for v in vals if v+p<=N]; j+=1
    return set(vals)
def in_S_d1(x,d):
    if x<0: return False
    pos=0
    while x>0:
        dig=x%d
        if dig not in (0,1): return False
        if pos==0 and dig!=0: return False
        x//=d; pos+=1
    return True
def representable(n, S3=None):
    if S3 is None: S3=S_d1_set(3,n)
    S11=S_d1_set(11,n)
    for a11 in S11:
        rem1=n-a11
        for a3 in S3:
            if a3>rem1: continue
            if in_S_d1(rem1-a3,4): return True
    return False
# d_min=3 powers: 3^19=1162261467, 3^20=3486784401, 3^21=10460353203
for m in [18,19,20,21]:
    q=3**m
    S3=S_d1_set(3,q)
    # sample 150 points in [q - 3^(m-1), q)
    step=max(1,(3**(m-1))//150)
    band=[q-1-i*step for i in range(150)]
    miss=[n for n in band if not representable(n,S3)]
    print(f"3^{m}={q}: tested 150 pts just below, {len(miss)} non-representable" + (f"  e.g. {miss[:8]}" if miss else ""))
