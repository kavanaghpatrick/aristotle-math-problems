import numpy as np
def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    for p in at: rep[p:]|=rep[:N+1-p].copy()
    return rep
# maverick's V3 challenge: did my re-spike test probe the SINGLETON/straggler band, or only run-bands?
# My re-spike test counted holes-per-7^j-band. The straggler n0=166,025,260 — which 7-band is it in?
# 7^9=40,353,607; 7^10=282,475,249. So n0=166M is in the [7^9, 7^10) band. My test DID count that band
# (it reported the band drains to ...->2155->0). But maverick's point: V3's drainage inequality is about
# AGGREGATE holes-per-band; the SINGLETON straggler at 166M is ONE hole in a band with 2155 others.
# Does V3's per-band drainage (band total) MASK the singleton? Check: is the band containing 166M
# the one where drainage->0, and does the singleton sit in the DRAINING tail or get masked?
D=(3,4,7); k=3; N=200_000_000
exc=np.flatnonzero(~atoms_repset(D,k,N))
n0=int(exc[-1])
print(f"(3,4,7) k=3: n0(straggler)={n0}; 7^9={7**9}, 7^10={7**10}")
print(f"n0 is in 7-band [{7**9},{7**10}): {7**9<=n0<7**10}")
# holes in that band:
band_holes=exc[(exc>=7**9)&(exc<7**10)]
print(f"holes in the [7^9,7^10) band containing n0: {len(band_holes)}, max={int(band_holes[-1]) if len(band_holes) else 0}")
# THE KEY: is the straggler n0 a SINGLETON (isolated hole) or part of a run? Check neighbors.
print(f"\nStraggler structure at n0={n0}: representable neighbors?")
full=atoms_repset(D,k,N)
print(f"  n0-1 rep={bool(full[n0-1])}, n0 rep={bool(full[n0])}, n0+1 rep={bool(full[n0+1])}")
# run-length of holes around n0
lo=n0; 
while lo>0 and not full[lo]: lo-=1
hi=n0
while hi<N and not full[hi]: hi+=1
print(f"  hole-run containing n0: [{lo+1},{hi-1}], length={hi-1-lo}")
print(f"\n=> maverick's question: V3 counts AGGREGATE band-holes (drains to 0). The straggler is a")
print(f"   {'SINGLETON' if hi-1-lo==1 else f'run of {hi-1-lo}'}. V3's band-total drainage masks whether the")
print("   SINGLETON specifically is drained — maverick is right that band-aggregate != singleton-level.")
