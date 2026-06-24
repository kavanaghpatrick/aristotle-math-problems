import numpy as np
# Gap/bridge structure of B_d (0/1-digit base-d numbers) and the Newhouse-thickness raw material.
# B_d up to N: sorted representable values. Gaps = differences between consecutive elements.
# Astels/Newhouse thickness of a Cantor-like set: tau = inf over gaps G of (length of bridge adjacent to G)/(length of G).
def B_d(d, N):
    vals=np.zeros(N+1,dtype=bool); vals[0]=True
    j=0
    while d**j<=N:
        p=d**j; vals[p:]|=vals[:N+1-p].copy(); j+=1
    return np.flatnonzero(vals)
# For B_d, the structure is exactly: at scale d^m, B_d looks like {0,1} digits => self-similar Cantor set.
# Gap just after the "all 1s up to d^(m-1)" block: largest value < d^m is (d^m-1)/(d-1) (all 1s),
# next value is d^m. So GAP = d^m - (d^m-1)/(d-1) = (d^m(d-2)+1)/(d-1). Bridge before it = the block [0,(d^m-1)/(d-1)].
print("B_d gap/bridge structure (self-similar Cantor-like). Largest pre-d^m value, gap to d^m, bridge length:")
for d in [3,4,5,7,11]:
    print(f"\n base d={d}: (d-1)^{{-1}}={1/(d-1):.4f}")
    for m in range(2,7):
        q=d**m
        allones=(q-1)//(d-1)  # 1+d+...+d^(m-1)
        gap = q - allones      # gap from allones to next element d^m
        bridge = allones+1     # contiguous block [0, allones] has length allones+1 (it IS contiguous? NO)
        # Actually B_d is NOT contiguous below allones. The RIGHTMOST contiguous run below d^m:
        Bvals=set(int(x) for x in B_d(d,q))
        # find longest contiguous run ending at allones
        run=0; x=allones
        while x in Bvals: run+=1; x-=1
        print(f"   m={m}: d^m={q} largest_0/1_val(allones)={allones} gap_to_d^m={gap} ratio gap/allones={gap/allones:.4f} | rightmost_contig_run_len={run}")
