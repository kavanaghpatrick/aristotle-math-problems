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
# MY near-power definition (from breaker_C1_induction_depth.py): a residual x is "near-power" if
# x is within 10% BELOW some single atom-power d^j: p*0.9 <= x < p. (single-base, below only, eps=10%.)
def near_power_BREAKER(x, powers):
    for p in sorted(powers):
        if p*0.9 <= x < p: return True
    return False
# CARRY's definition (as described): within eps of FLOOR or CEIL power across ALL 3 bases, eps=0.5-5%.
def near_power_CARRY(x, powers, eps):
    for p in sorted(powers):
        if abs(x-p)/p <= eps: return True  # both sides (floor+ceil)
    return False
D=(3,4,7); k=1; N=3_000_000
full=atoms_repset(D,k,N); allatoms=atoms_list(D,k,N)
powers=set(allatoms)
exc=np.flatnonzero(~full); n0=int(exc[-1])
lo=n0+1; hi=lo+5000
# run the recursion, count fraction of peel steps at near-power under EACH definition
defs={'BREAKER (below 10%, single-side)':lambda x:near_power_BREAKER(x,powers),
      'CARRY eps=5% (both sides)':lambda x:near_power_CARRY(x,powers,0.05),
      'CARRY eps=2% (both sides)':lambda x:near_power_CARRY(x,powers,0.02),
      'CARRY eps=0.5% (both sides)':lambda x:near_power_CARRY(x,powers,0.005)}
counts={name:[0,0] for name in defs}  # [near, total]
for n in range(lo,hi):
    if not full[n]: continue
    rem=n; guard=0
    while rem>0 and guard<100:
        guard+=1
        for a in reversed([x for x in allatoms if x<=rem]):
            if full[rem-a]:
                for name,f in defs.items():
                    counts[name][1]+=1
                    if f(rem): counts[name][0]+=1
                rem-=a; break
        else: break
print("(3,4,7) k=1: fraction of recursion peel-steps at NEAR-POWER residuals, by definition:")
for name,(near,tot) in counts.items():
    print(f"  {name:<35}: {near}/{tot} = {near/tot:.1%}")
