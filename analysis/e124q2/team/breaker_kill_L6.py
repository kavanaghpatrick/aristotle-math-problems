import numpy as np
def sumset_bool(Ds,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    atoms=[]
    for d in Ds:
        j=k
        while d**j<=N: atoms.append(d**j); j+=1
    for p in atoms: rep[p:]|=rep[:N+1-p].copy()
    return rep
def Cn_window(lo,hi,N,P,Q):
    """C(n)=#{c in Q=B7 : n-c in P=B3+B4} for n in [lo,hi)."""
    C=np.zeros(hi-lo,dtype=np.int32)
    for c in Q:
        if c>=hi: break
        # n in [lo,hi): n-c in [lo-c, hi-c); add P[n-c]
        a=max(lo,c); 
        # indices n in [a,hi): C[n-lo]+= P[n-c]
        lo_i=a-lo; 
        src_lo=a-c; src_hi=hi-c
        C[lo_i:] += P[src_lo:src_hi].astype(np.int32)
    return C
# INV-L6: (3,4,7), windows [3^m,3^{m+1}), m up to ~18 (3^18=387M). Track phase psi_m=argmin(C)/3^m and min/mean.
k=1; N=400_000_000
P=sumset_bool((3,4),k,N)   # B3+B4
Q=np.flatnonzero(sumset_bool((7,),k,N))  # B7
print("INV-L6 (3,4,7): per-window [3^m,3^{m+1}) min C, mean C, min/mean, phase psi_m=argmin/3^m")
print(f"{'m':>3}{'3^m':>12}{'minC':>7}{'meanC':>9}{'min/mean':>10}{'psi_m':>8}")
prev_psi=None
for m in range(8,19):
    lo=3**m; hi=min(3**(m+1),N)
    if lo>=N: break
    C=Cn_window(lo,hi,N,P,Q)
    minC=int(C.min()); meanC=float(C.mean())
    ratio=minC/meanC if meanC>0 else 0
    psi=(lo+int(C.argmin()))/3**m  # in [1,3)
    print(f"{m:>3}{lo:>12}{minC:>7}{meanC:>9.1f}{ratio:>10.3f}{psi:>8.3f}")
print("\nFALSIFICATION watch: if min/mean -> 0 at some m, the bad region isn't shrinking (=> possible NON-cofinite high k).")
print("SURVIVES: min/mean bounded away from 0 AND psi drifts predictably (torus orbit {m log3/log7 mod 1}).")
