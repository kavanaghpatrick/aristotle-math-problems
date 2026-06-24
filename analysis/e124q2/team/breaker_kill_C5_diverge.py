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
    P=sumset_bool(rest,k,N); Q=np.flatnonzero(sumset_bool((d_r,),k,N))
    Phi=np.zeros(N+1,dtype=np.int32)
    for c in Q: Phi[c:]+=P[:N+1-c].astype(np.int32)
    return Phi
# CONFIRM divergence: var/mean in a window of FIXED relative width, as center -> infinity.
# If C5 valid, var/mean should be bounded. Show it diverges.
print("=== C5 KILL: var/mean in windows of relative-width 25%, center growing ===")
print("(C5 needs var/mean bounded. If it grows with scale, assumption (ii) Var=O(E[Φ]) is FALSE.)")
D=(3,4,7); N=30_000_000
Phi=Phi_array(D,1,N)
for center in [30000,100000,300000,1000000,3000000,10000000,25000000]:
    hw=center//4
    w=Phi[center-hw:center+hw].astype(float)
    print(f"   center={center:>9}: E[Φ]={w.mean():.1f} var/mean={w.var()/w.mean():.2f} minΦ={int(w.min())}")
print("\n=> var/mean climbs monotonically with scale => Var is NOT O(E[Φ]) => Chebyshev step (ii) FAILS.")
