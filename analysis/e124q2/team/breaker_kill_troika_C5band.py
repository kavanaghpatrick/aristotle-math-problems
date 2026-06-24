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
    """Phi(n)=#{c in B_{d_r}(k),c<=n : n-c in P}, P = sum of rest."""
    d_r=D[-1]; rest=D[:-1]
    P=sumset_bool(rest,k,N); Q=np.flatnonzero(sumset_bool((d_r,),k,N))
    Phi=np.zeros(N+1,dtype=np.int32)
    for c in Q: Phi[c:]+=P[:N+1-c].astype(np.int32)
    return Phi
def band_local_varmean(Phi, centers, hw):
    """troika's band-local Var/E in homogeneous windows; report worst (max) over centers + global minPhi."""
    worst=0; minphi=10**9
    for c in centers:
        lo=max(0,c-hw); hi=min(len(Phi),c+hw)
        w=Phi[lo:hi].astype(float)
        if w.mean()>0: worst=max(worst, w.var()/w.mean())
        minphi=min(minphi,int(w.min()))
    return worst, minphi
# THE DISCRIMINATION TEST: C5-band must show Var/E BLOW UP (or minPhi->0) for β<1 (NOT cofinite),
# stay bounded with minPhi>0 for β>=1 (cofinite). Test (3,4,7) β=1 cofinite vs (3,4,11) β=0.933 NOT.
print("troika C5-band DISCRIMINATION TEST: does Var/E distinguish β=1 (cof) from β=0.933 (not cof)?")
print("d_r = last base. For each, band-local Var/E (max over windows) + global minPhi up to N.\n")
for D,k,label in [((3,4,7),1,"β=1.000 COFINITE"),((3,4,11),1,"β=0.933 NOT-cofinite"),
                  ((3,4,10),1,"β=0.944 NOT-cofinite"),((3,5,7),1,"β=0.917 NOT-cofinite")]:
    N=200_000_000
    Phi=Phi_array(D,k,N)
    centers=[int(N*f) for f in [0.1,0.25,0.5,0.75,0.95]]
    hw=N//40
    worst,minphi=band_local_varmean(Phi,centers,hw)
    # also: does Phi ever hit 0 in [N/10,N]? (true miss)
    zeros=int(np.sum(Phi[N//10:]==0))
    print(f"  {str(D):<10} {label}: max band Var/E={worst:.2f}  global minPhi(windows)={minphi}  #Phi=0 in[N/10,N]={zeros}")
print("\nKILL if: (3,4,11)/(3,4,10)/(3,5,7) [β<1, NOT cofinite] show BOUNDED Var/E and minPhi>0,")
print("i.e. C5-band looks IDENTICAL to the cofinite (3,4,7) => CANNOT discriminate => too weak.")
