"""Independent sieve to kill-test matveev's TARGET-2 L2/L3 claims for (3,4,7) k=1 and k=2."""
import numpy as np

def Bd_upto(d, N, k):
    """0/1-digit base-d numbers times d^k, all <= N. Returns sorted np array of d^k * B_d values <= N."""
    # atoms d^(k+j), j>=0, <= N
    atoms=[]
    e=k
    while d**e <= N:
        atoms.append(d**e); e+=1
    # subset sums via boolean convolution
    reach=np.zeros(N+1, dtype=bool); reach[0]=True
    for a in atoms:
        reach[a:] |= reach[:-a] if a<=N else False
        # the line above shifts; do it correctly:
    return reach

def reachable_set(D, k, N):
    """boolean array: which n<=N are in sum_{d in D} d^k*B_d."""
    # start with {0}
    reach=np.zeros(N+1,dtype=bool); reach[0]=True
    for d in D:
        # atoms for this base
        atoms=[]; e=k
        while d**e<=N:
            atoms.append(d**e); e+=1
        # per-base reachable 0/1-digit combos
        base=np.zeros(N+1,dtype=bool); base[0]=True
        for a in atoms:
            base[a:] |= base[:N+1-a]
        # Minkowski sum reach += base (convolve supports)
        newreach=np.zeros(N+1,dtype=bool)
        idx=np.nonzero(base)[0]
        for a in idx:
            if a==0:
                newreach |= reach
            else:
                newreach[a:] |= reach[:N+1-a]
        reach=newreach
    return reach

# k=1: confirm N0=581
N=2000
r1=reachable_set([3,4,7],1,N)
miss1=np.nonzero(~r1[1:N+1])[0]+1  # 1..N not reachable
print("k=1: #misses <=2000 =", len(miss1), " max miss =", miss1.max())
print("  581 in misses:", 581 in set(miss1.tolist()), "| 580,582..587 all reachable:",
      all(r1[n] for n in [580,582,583,584,585,586,587]))
print("  matveev/ground-truth N0(1)=581 ->", "CONFIRMED" if miss1.max()==581 else "MISMATCH")

# k=2: confirm N0=3,982,888 and the [3789577,4194303] gap claim
print("\nk=2 sieve to N=8M (a minute)...")
N2=8_000_000
r2=reachable_set([3,4,7],2,N2)
miss2=np.nonzero(~r2[1:N2+1])[0]+1
print("k=2: #misses <=8M =", len(miss2), " max miss =", miss2.max())
print("  matveev/ground-truth N0(2)=3,982,888 ->",
      "CONFIRMED" if miss2.max()==3982888 else f"MISMATCH (got {miss2.max()})")
# the specific super-gap claim: in [3789577,4194303], how many uncovered, and are they <= N0(2)?
lo,hi=3789577,4194303
gapmiss=miss2[(miss2>=lo)&(miss2<=hi)]
print(f"  uncovered in [{lo},{hi}] (ends at 4^11={4**11}): count={len(gapmiss)}, values={gapmiss.tolist()}")
print(f"  all <= N0(2)=3982888:", bool((gapmiss<=3982888).all()) if len(gapmiss) else "N/A (0 uncovered)")
# tail gap-free above N0(2)?
above=miss2[miss2>3982888]
print(f"  misses strictly above N0(2): {len(above)} (should be 0 for tail-gap-free)")
