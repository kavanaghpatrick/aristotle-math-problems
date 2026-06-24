import numpy as np
# Fix: exact integer r(n) via DP (0/1 knapsack count), then test scholar's actual claim:
# does the MAJOR-ARC main term (theta near 0 contribution) PREDICT r(n)>0 for all n>581?
# The major-arc main term for a subset-sum count ~ (1/density-ish) * product structure near theta=0.
D=(3,4,7); k=1; M=6000
atoms=[]
for d in D:
    j=k
    while d**j<=M: atoms.append(d**j); j+=1
# exact representation count r(n)
r=np.zeros(M+1,dtype=np.float64); r[0]=1
for a in atoms:
    r[a:]+=r[:M+1-a]
misses=[n for n in range(M+1) if r[n]==0]
print(f"(3,4,7) k=1 exact r(n): #misses={len(misses)}, max miss={max(misses)} (expect 581)")
print(f"  r(n) above 581 grows; min r(n) for n in [582,{M}] = {r[582:].min():.0f}")
# scholar's circle-method kill: the major-arc MAIN TERM. For atoms with leading singularity at theta=0,
# the main term ~ vol = integral predicting the SMOOTH count. Compare exact r(n) to its local average
# (the major-arc/smooth prediction) and check if the FLUCTUATION (minor arcs) ever drives r to 0 where
# the main term is large. THIS is the real test: at the misses {178..581}, is the major-arc prediction >>0?
# local-average (smooth/major-arc proxy) = moving average of r over window ~ smallest atom scale
win=50
smooth=np.convolve(r,np.ones(win)/win,mode='same')
# at the LARGEST miss 581: major-arc predicts smooth[581], actual r[581]=0
print(f"\n  At misses, is the smooth (major-arc) prediction >> 0 while actual r=0? (=> minor arcs carry signal)")
for n in [178,212,581]:
    print(f"    n={n}: actual r(n)={r[n]:.0f}, smooth/major-arc prediction~{smooth[n]:.1f}")
print(f"\n  => if smooth>>0 at the misses, the major-arc main term CANNOT see the misses (minor arcs do)")
print(f"     => circle method's main term fails to vanish at misses => CAN'T prove r(n)>0 by major arcs alone.")
# decisive: ratio of minor-arc fluctuation to major-arc term in the miss region
print(f"\n  fluctuation test: in [100,600], max smooth={smooth[100:600].max():.1f}, but {len([n for n in range(100,600) if r[n]==0])} misses exist there")
print(f"  => minor-arc (fluctuation) amplitude >= major-arc term (misses occur where main term is O(major)) => S1 method can't separate.")
