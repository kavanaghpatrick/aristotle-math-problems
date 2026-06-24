import numpy as np
from fractions import Fraction
def repset_atoms(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    atoms=[]
    for d in D:
        j=k
        while d**j<=N: atoms.append(d**j); j+=1
    for p in atoms: rep[p:]|=rep[:N+1-p].copy()
    return rep
def gaps_and_bridges(reparr, N):
    """Return (gap_positions, gap_lengths, bridge_lengths) for a representable bitarray.
       A 'gap' = maximal run of NON-representable ints. A 'bridge' = maximal run of representable ints.
       Newhouse thickness tau = inf over gaps of (adjacent bridge length / gap length)."""
    idx=np.flatnonzero(reparr)
    # gaps between consecutive representable points
    d=np.diff(idx)
    gap_lens=d[d>1]-1                      # lengths of missing runs
    gap_starts=idx[:-1][d>1]+1
    # bridges = runs of representable ints
    rep=reparr.copy()
    # find runs of True
    padded=np.concatenate(([0],rep.view(np.int8),[0]))
    diff=np.diff(padded)
    bstarts=np.flatnonzero(diff==1); bends=np.flatnonzero(diff==-1)
    bridge_lens=bends-bstarts
    return gap_starts, gap_lens, bridge_lens

print("=== RAW MATERIAL for thickness attack ===\n")
print("## Single-base B_d structure (d^k=d^0, k irrelevant by scaling S(d,k)=d^k B_d) ##")
print("Self-similar: just below d^m, largest 0/1 value = (d^m-1)/(d-1) (all-ones); gap to d^m has")
print("gap/allones -> d-2 EXACTLY. So B_d thinness governed by (d-2); admissibility uses 1/(d-1).\n")
for d in [3,4,5,7,11]:
    N=2*d**7
    rep=repset_atoms((d,),0,N)
    gs,gl,bl=gaps_and_bridges(rep,N)
    # Newhouse-style worst ratio over the structured region (away from boundary)
    # pair each gap with the bridge to its LEFT
    idx=np.flatnonzero(rep)
    print(f" d={d}: #gaps={len(gl)} max_gap={int(gl.max()) if len(gl) else 0} "
          f"#bridges={len(bl)} max_bridge={int(bl.max())} "
          f"1/(d-1)={1/(d-1):.4f} (d-2)={d-2}")
