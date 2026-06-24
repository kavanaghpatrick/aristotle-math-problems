import numpy as np
def Ck(D,k):
    offs={0}
    for d in D:
        p=d**k
        offs={o for o in offs}|{o+p for o in offs}
    return sorted(offs)
def Lmin_cover_np(D,M,Lmax=60):
    res=np.zeros(M,dtype=bool); res[0]=True
    for L in range(1,Lmax+1):
        new=np.zeros(M,dtype=bool)
        for c in (c%M for c in Ck(D,L)):
            new |= np.roll(res,c)
        res=new
        if res.all(): return L
    return None
# slope c = L_min(p^a)/a as a->inf, for p|some d (the bottleneck prime = smallest base's prime, usually 3)
# This c is the "coverage lag" — the key constant in (★).
print("Coverage-lag slope c_p = lim L_min(p^a)/a for the bottleneck prime (p | d_min):")
for D in [(3,4,7),(3,5,7,13),(3,4,11,16),(3,5,6,21),(3,4,9,25)]:
    dmin=min(D)
    # bottleneck prime: smallest prime dividing dmin
    p=2
    while dmin%p!=0: p+=1
    seq=[Lmin_cover_np(D,p**a) for a in range(1,11)]
    slopes=[seq[a]/(a+1) for a in range(len(seq)) if seq[a]]
    # asymptotic slope from last few
    asym=(seq[-1]-seq[-4])/3 if all(seq[-4:]) else None
    print(f"   D={str(D):<16} p={p}: L_min(p^a) a=1..10: {seq}  asymptotic slope ~{asym:.3f}")
