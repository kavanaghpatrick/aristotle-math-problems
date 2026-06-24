import numpy as np
def atoms_list(D,k,N):
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    return sorted(at)
def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    for p in atoms_list(D,k,N): rep[p:]|=rep[:N+1-p].copy()
    return rep
# Is INV-C1's induction's per-level residual representability ITSELF easy, or does it re-hit hard cases?
# Measure: following the FULL peel recursion n -> n-a -> ..., does any residual land in the "hard"
# region (just above a power, the MW-cluster) at EVERY level, or do the residuals become "generic"?
# Proxy: at each recursion level, is the residual within distance d_min^j of a pure power d^j (MW-hard)
# or generic? Count fraction of recursion steps that are "near-power" (hard).
D=(3,4,7); k=1; N=3_000_000
full=atoms_repset(D,k,N); allatoms=atoms_list(D,k,N)
exc=np.flatnonzero(~full); n0=int(exc[-1])
powers=set()
for d in D:
    j=k
    while d**j<=N: powers.add(d**j); j+=1
def near_power(x):
    # within 5% of some single atom-power d^j from below
    for p in sorted(powers):
        if p*0.9 <= x < p: return True
    return False
lo=n0+1; hi=lo+5000
near_count=0; total_steps=0
for n in range(lo,hi):
    if not full[n]: continue
    rem=n; guard=0
    while rem>0 and guard<100:
        guard+=1
        for a in reversed([x for x in allatoms if x<=rem]):
            if full[rem-a]:
                total_steps+=1
                if near_power(rem): near_count+=1
                rem-=a; break
        else: break
print(f"(3,4,7) k=1 INV-C1 recursion: {total_steps} total peel steps, {near_count} ({near_count/total_steps:.1%}) at near-power(MW-hard) residuals")
print("If LOW %: induction's residuals are mostly generic (hard cases rare, don't nest) => C1 reduction has easy base.")
print("If HIGH %: every level re-hits MW-cluster => C1 relocates the wall, doesn't escape it.")
