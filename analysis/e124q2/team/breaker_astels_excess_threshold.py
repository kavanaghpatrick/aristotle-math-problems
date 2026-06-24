from fractions import Fraction
def Cd_N(d,N):
    vals=[Fraction(0)]
    for j in range(1,N+1):
        p=Fraction(1,d**j); vals=vals+[v+p for v in vals]
    return sorted(set(vals))
def sumset_frac(D,N):
    res=[Fraction(0)]
    for d in D:
        C=Cd_N(d,N); new=set()
        for a in res:
            for c in C: new.add(a+c)
        res=sorted(new)
    return res
def scaled_central_gap(D,N,lo=Fraction(1,5),hi=Fraction(4,5)):
    vals=sumset_frac(D,N); hull=vals[-1]
    central=[v for v in vals if hull*lo<=v<=hull*hi]
    g=max(central[i+1]-central[i] for i in range(len(central)-1))
    return float(g)*max(D)**N
# Find: at what excess does scaled-gap DECAY (->0, mechanism works) vs GROW (mechanism fails)?
# Test families across excess range, look at trend N=3->5.
fams=[(3,4,5,7),(3,4,5,6),(3,4,6),(3,4,5),(3,5,6,9),(3,5,7,8),(3,5,7,9),(3,4,7)]
print("Scaled central gap trend (N=3,4,5) vs excess — does the v4 mechanism (gap->0) hold?")
print(f"{'D':<14}{'excess':>9}{'N=3':>8}{'N=4':>8}{'N=5':>8}{'trend':>10}")
for D in fams:
    ex=float(sum(Fraction(1,d-1) for d in D))-1
    gs=[scaled_central_gap(D,N) for N in [3,4,5]]
    trend = "DECAY✓" if gs[2]<gs[0] and gs[2]<1 else "GROW✗"
    print(f"{str(D):<14}{ex:>+9.3f}{gs[0]:>8.3f}{gs[1]:>8.3f}{gs[2]:>8.3f}{trend:>10}")
