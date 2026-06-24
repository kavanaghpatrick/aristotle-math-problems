import numpy as np
# Test scholar's claim: (3,4,7) k=2 stragglers near 4^J are the computational shadow of the
# Mignotte-Waldschmidt bound on |3^p - 4^q|. The largest non-representable n cluster just below 4^11.
# MW says 3^p and 4^q can't be too close => the "thin band" just below 4^J where representation
# is hard has a size controlled by min_p |4^J - 3^p| (how far the nearest power of 3 is).
def per_base_bool(d,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    j=k
    while d**j<=N:
        p=d**j; rep[p:]|=rep[:N+1-p]; j+=1
    return rep
def exceptional2(D,k,N):
    arrs=[per_base_bool(d,k,N) for d in D]; rep=arrs[0]
    for a in arrs[1:]:
        ia=np.flatnonzero(rep); ib=np.flatnonzero(a)
        small,dense=(ia,a) if len(ia)<=len(ib) else (ib,rep)
        c=np.zeros(N+1,dtype=bool)
        for p in small:
            if p>N: break
            c[p:]|=dense[:N+1-p]
        rep=c
    return np.flatnonzero(~rep)

exc=sorted(int(x) for x in exceptional2((3,4,7),2,5000000))
print(f"(3,4,7) k=2: {len(exc)} exceptionals, max={exc[-1]}")
# Powers of 4 (the k=2 atoms are 4^j, j>=2): 4^2=16,...
pw4=[4**j for j in range(2,13)]
pw3=[3**j for j in range(2,15)]
pw7=[7**j for j in range(2,9)]
# For each large straggler, find nearest power of 4 above and the MW quantity min|4^J - 3^p|
print("\nLarge stragglers vs nearest power-of-4 band and MW gap min|4^J - 3^p|:")
for e in [x for x in exc if x>100000]:
    # nearest 4^J strictly above e
    above=[q for q in pw4 if q>e]
    J4=min(above) if above else None
    dist=J4-e if J4 else None
    # MW: how close is J4 to a power of 3?
    mw=min(abs(J4-p3) for p3 in pw3) if J4 else None
    print(f"  e={e:>9}  nearest 4^J above={J4} (gap {dist})  min|4^J-3^p|={mw}")

# Structural prediction: stragglers exist in a band [4^J - W_J, 4^J) whose WIDTH W_J is bounded
# (MW => W_J grows only polynomially in J, not geometrically). Measure band widths.
print("\nBand structure: for each 4^J, count exceptionals in [4^J - 4^(J-1), 4^J):")
for J in range(5,12):
    q=4**J
    lo=q-4**(J-1)
    band=[e for e in exc if lo<=e<q and e<=exc[-1]]
    if band:
        print(f"  4^{J}={q}: {len(band)} exc in band, range [{min(band)},{max(band)}], width-from-4^J: {q-min(band)}..{q-max(band)}")
