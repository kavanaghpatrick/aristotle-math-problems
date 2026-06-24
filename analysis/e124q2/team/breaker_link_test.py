import numpy as np
def per_base_bool(d,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    j=k
    while d**j<=N:
        p=d**j; rep[p:]|=rep[:N+1-p]; j+=1
    return rep
def exceptional2(D,k,N):
    arrs=[per_base_bool(d,k,N) for d in D]; rep=arrs[0]
    for a in arrs[1:]:
        ia=np.flatnonzero(rep); ib=np.flatnonzero(a)
        small,dense=(ia,a) if len(ia)<=len(ib) else (ib,rep)
        c=np.zeros(N+1,dtype=bool)
        for p in small:
            if p>N: break
            c[p:]|=dense[:N+1-p]
        rep=c
    return np.flatnonzero(~rep)
def Ck(D,k):
    offs={0}
    for d in D:
        p=d**k; offs={o for o in offs}|{o+p for o in offs}
    return sorted(offs)
def Lmin_cover_np(D,M,Lmax=40):
    res=np.zeros(M,dtype=bool); res[0]=True
    for L in range(1,Lmax+1):
        new=np.zeros(M,dtype=bool)
        for cc in (c%M for c in Ck(D,L)): new|=np.roll(res,cc)
        res=new
        if res.all(): return L
    return None
def n0(D,k):
    hist=[];N=4000000
    while N<=2000000000:
        exc=exceptional2(D,k,N); cnt=len(exc); mx=int(exc[-1]) if cnt else 0
        hist.append((cnt,mx,N))
        if len(hist)>=3 and hist[-1][0]==hist[-2][0]==hist[-3][0] and hist[-2][1]<hist[-2][2]//2 and hist[-1][1]<hist[-1][2]//2:
            return hist[-1][1]
        N*=2
    return None
print("Coverage-lag c (L_min(3^a)/a) vs threshold ratio n0(k3)/n0(k2):")
print(f"{'D':<16}{'c':>8}{'n0(2)':>10}{'n0(3)':>11}{'ratio':>9}")
for D in [(3,4,7),(3,5,7,13),(3,4,11,16),(3,5,6,21),(3,4,9,25)]:
    seq=[Lmin_cover_np(D,3**a) for a in range(1,11)]
    c=(seq[-1]-seq[-4])/3
    n2=n0(D,2); n3=n0(D,3)
    r=n3/n2 if (n2 and n3) else float('nan')
    print(f"{str(D):<16}{c:>8.3f}{n2:>10}{n3:>11}{r:>9.1f}")
