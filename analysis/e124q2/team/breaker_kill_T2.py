import numpy as np
def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    for p in at: rep[p:]|=rep[:N+1-p].copy()
    return rep
def theta_concentration(D,k,N,nbins=20):
    """bin the MISSES of full D by theta3=log3(n) mod 1; return max/min bin ratio (concentration)."""
    exc=np.flatnonzero(~atoms_repset(D,k,N))
    exc=exc[exc>10]
    if len(exc)<nbins: return None
    th=(np.log(exc)/np.log(3))%1.0
    h,_=np.histogram(th,bins=nbins,range=(0,1))
    nz=h[h>0]
    return h.max()/nz.min() if len(nz) else None, h.argmax()/nbins
# T2 BRIDGE claim: gaps cluster at a bounded θ-class, 3rd ray covers it uniformly => finite casework.
# KILL angle: does T2's θ-concentration DISCRIMINATE cofinite (3rd ray covers, finite misses) from
# sub-threshold (3rd ray FAILS to cover, infinite misses)? If both show the same concentration, T2's
# θ-structure is NECESSARY-not-sufficient (= can't tell when the 3rd ray actually closes it).
print("=== INV-T2 KILL: θ3-concentration of gaps, cofinite vs sub-threshold ===")
for D,k,label in [((3,4,7),1,"β=1 COF"),((3,4,7),2,"β=1 COF k2"),
                  ((3,4,11),1,"β=0.933 NOT-cof (deep trap)"),((3,5,7),1,"β=0.917 NOT-cof"),
                  ((3,4),1,"β=0.833 NOT-cof"),((3,5),1,"β=0.75 NOT-cof")]:
    N=8_000_000
    res=theta_concentration(D,k,N)
    if res: print(f"  {str(D):<10} {label}: θ3-concentration ratio={res[0]:.1f}, peak θ≈{res[1]:.2f}")
print("\nKILL if cofinite & sub-threshold show SAME θ-concentration => T2's clustering is necessary-not-")
print("sufficient (can't distinguish when the 3rd ray closes the bad class). The clustering exists for")
print("ALL families (gaps always cluster at powers); the question is whether the cluster is FINITE.")
