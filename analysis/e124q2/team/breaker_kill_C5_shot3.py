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
# KILL SHOT 3 (decisive): is there n with Phi(n)=0 (true miss) while LOCAL E[Phi] >> 1?
# That's a large-deviation event a variance method cannot rule out. The DEEP STRAGGLERS are the candidates.
# (3,4,7) k=2: true misses incl 3964625, 3982888 (near 4^11). Compute Phi there + local E[Phi].
print("KILL SHOT 3: Phi=0 at a deep straggler while local E[Phi]>>1?")
for D,k,stragglers in [((3,4,7),2,[3964625,3982888,785743]),((3,4,7),3,[166025260])]:
    N=int(max(stragglers)*1.3)
    Phi=Phi_array(D,k,N)
    for s in stragglers:
        # local mean around s (exclude s itself), window +-s/20
        hw=s//20; lo=max(0,s-hw); hi=min(N,s+hw)
        local=Phi[lo:hi]
        localmean=local.mean()
        print(f"   D={D} k={k}: Phi({s})={int(Phi[s])}  local E[Phi]~{localmean:.1f}  => Phi=0 with E[Phi]={localmean:.0f}>>1: {Phi[s]==0 and localmean>5}")
print("\n=> If Phi(straggler)=0 while local E[Phi] is large, that's a verified large-deviation event")
print("   the variance method CANNOT exclude => C5 cannot prove cofiniteness (it would predict these hit).")
