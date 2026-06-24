import numpy as np
def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    for p in at: rep[p:]|=rep[:N+1-p].copy()
    return rep
# troika's SHARPER test: is the bad θ-class (where the LAST/persistent gaps live) FINITE for β>=1 but
# GROWS for β<1? Measure the θ3-SPREAD of gaps in successive scale windows. For β>=1 (cofinite) the gaps
# stop => the occupied θ-classes shrink to EMPTY. For β<1 the gaps persist => θ-classes stay populated.
def occupied_theta_classes(D,k,N,window_lo,window_hi,nbins=50):
    exc=np.flatnonzero(~atoms_repset(D,k,N))
    exc=exc[(exc>=window_lo)&(exc<window_hi)]
    if len(exc)==0: return 0
    th=(np.log(exc)/np.log(3))%1.0
    h,_=np.histogram(th,bins=nbins,range=(0,1))
    return int(np.sum(h>0))  # # of occupied θ-bins (the "bad class" size)
print("=== INV-T2 SHARP test: # occupied θ3-classes of gaps in successive scale windows ===")
print("(β>=1: gaps stop => occupied classes -> 0. β<1: gaps persist => classes stay populated.)")
for D,k,label in [((3,4,7),1,"β=1 COF"),((3,4),1,"β=0.833 NOT-cof"),((3,5,7),1,"β=0.917 NOT-cof"),((3,4,11),1,"β=0.933 deep-trap")]:
    N=8_000_000
    print(f"  {str(D):<10} {label}:")
    for w in [(1000,10000),(10000,100000),(100000,1000000),(1000000,8000000)]:
        c=occupied_theta_classes(D,k,N,w[0],w[1])
        print(f"     window[{w[0]},{w[1]}]: {c}/50 θ-classes occupied by gaps")
print("\nVERDICT: if occupied-classes -> 0 for β>=1 but stays >0 for β<1 (within reach), T2 discriminates.")
print("If (3,4,11) [β<1] ALSO shows -> 0 within reach (deep trap), T2 can't see its asymptotic gaps => same blindness.")
