import numpy as np
def Bd_k(d,k,N):
    """d^k*B_d up to N as boolean array: sums of distinct d^j, j>=k."""
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    j=k
    while d**j<=N: p=d**j; rep[p:]|=rep[:N+1-p].copy(); j+=1
    return rep
def Bd_vals(d,k,N):
    return np.flatnonzero(Bd_k(d,k,N))
def sumset(Ds,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    atoms=[]
    for d in Ds:
        j=k
        while d**j<=N: atoms.append(d**j); j+=1
    for p in atoms: rep[p:]|=rep[:N+1-p].copy()
    return rep
def Phi_array(D,k,N):
    """Phi(n) = #{c in B_{d_r}(k), c<=n : n-c in P} for all n<=N. D sorted, d_r=last."""
    d_r=D[-1]; rest=D[:-1]
    P=sumset(rest,k,N)            # boolean P over [0,N]
    Q=Bd_vals(d_r,k,N)            # the d_r^k*B_{d_r} values (the c's)
    Phi=np.zeros(N+1,dtype=np.int32)
    for c in Q:
        # for n in [c,N]: add P[n-c]
        Phi[c:]+= P[:N+1-c].astype(np.int32)
    return Phi, P
def kill_report(D,k,N,name):
    Phi,P=Phi_array(D,k,N)
    exc=np.flatnonzero(~sumset(D,k,N))  # true misses of full D
    # Phi(n)=0 exactly when n is a true miss (n not in P+Q). Check.
    zero_phi=np.flatnonzero(Phi==0)
    # restrict to n>=some lower bound to avoid trivial small-n
    big=N//10
    region=Phi[big:]
    mean=region.mean(); var=region.var()
    minPhi=int(region.min()); 
    # n where Phi=0 in region (the kill shot: Phi=0 while E[Phi] large)
    zeros_in_region=np.flatnonzero(Phi[big:]==0)+big
    print(f"{name} D={D} k={k} N={N}:")
    print(f"   E[Phi]={mean:.2f} Var={var:.2f} var/mean={var/mean if mean else 0:.3f} minPhi(region)={minPhi}")
    print(f"   #n with Phi=0 in [N/10,N]: {len(zeros_in_region)}  (these are true misses)")
    if len(zeros_in_region): print(f"      e.g. {zeros_in_region[:8].tolist()} max={int(zeros_in_region[-1])}")
    return mean,var,minPhi,len(zeros_in_region)

# KILL SHOT 1: does var/mean blow up near boundary β=1?
print("=== KILL SHOT 1: var/mean across β (last base = d_r) ===")
kill_report((3,4,7),1,8_000_000,"boundary β=1.0")
kill_report((3,4,5),1,8_000_000,"strict β=1.083")
kill_report((3,5,7,9),1,8_000_000,"near-crit β=1.042")
