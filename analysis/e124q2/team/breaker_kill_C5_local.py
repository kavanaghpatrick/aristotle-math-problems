import numpy as np
def sumset_bool(Ds,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    atoms=[]
    for d in Ds:
        j=k
        while d**j<=N: atoms.append(d**j); j+=1
    for p in atoms: rep[p:]|=rep[:N+1-p].copy()
    return rep
def Phi_array(D,k,N):
    d_r=D[-1]; rest=D[:-1]
    P=sumset_bool(rest,k,N)
    Q=np.flatnonzero(sumset_bool((d_r,),k,N))
    Phi=np.zeros(N+1,dtype=np.int32)
    for c in Q:
        Phi[c:]+=P[:N+1-c].astype(np.int32)
    return Phi
def local_varmean(Phi, center, halfwidth):
    lo=max(0,center-halfwidth); hi=min(len(Phi),center+halfwidth)
    w=Phi[lo:hi].astype(float)
    return w.mean(), w.var(), int(w.min())
# Apples-to-apples with maverick: LOCAL var/mean in narrow windows at increasing scales.
print("=== LOCAL var/mean in narrow windows (matching maverick's measurement) ===")
for D in [(3,4,7),(3,4,5),(3,5,7,9)]:
    N=8_000_000
    Phi=Phi_array(D,1,N)
    print(f"\nD={D} (β-class):")
    for center in [10000,100000,1000000,5000000]:
        hw=center//4
        m,v,mn=local_varmean(Phi,center,hw)
        print(f"   window ~{center}: E[Φ]={m:.2f} var={v:.2f} var/mean={v/m if m else 0:.3f} minΦ={mn}")
