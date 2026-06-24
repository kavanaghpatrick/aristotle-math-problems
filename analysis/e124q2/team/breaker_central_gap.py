from fractions import Fraction
import math
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
def central_scaled_gap(D,N,lo=Fraction(1,3),hi=Fraction(2,3)):
    """max gap of sumset_d C_d^(N) restricted to the CENTRAL third [hull/3, 2hull/3], scaled by d_max^N."""
    vals=sumset_frac(D,N); hull=vals[-1]
    central=[v for v in vals if hull*lo<=v<=hull*hi]
    g=max(central[i+1]-central[i] for i in range(len(central)-1))
    return float(g)*max(D)**N
def global_upper_scaled_gap(D,N,lo=Fraction(1,5),hi=Fraction(4,5)):
    vals=sumset_frac(D,N); hull=vals[-1]
    reg=[v for v in vals if hull*lo<=v<=hull*hi]
    g=max(reg[i+1]-reg[i] for i in range(len(reg)-1))
    return float(g)*max(D)**N
def excess(D): return float(sum(Fraction(1,d-1) for d in D))-1
# Re-run my full set with the CENTRAL gap (maverick's reconciliation). N=4->5.
fams=[(3,4,5,6),(3,4,5,7),(3,5,7,8),(3,5,6,9),(3,4,5),(3,5,7,9),(3,4,6),(3,4,7),(3,5,7,13)]
print("CENTRAL gap (maverick) vs GLOBAL-upper gap (breaker), scaled by d_max^N, N=3,4,5:")
print(f"{'D':<14}{'ex':>7} | {'central N3/N4/N5':>26} {'trend':>7} | {'global N4/N5':>16} {'trend':>7}")
for D in fams:
    ex=excess(D)
    cg=[central_scaled_gap(D,N) for N in [3,4,5]]
    gg=[global_upper_scaled_gap(D,N) for N in [4,5]]
    ctrend="DECAY" if cg[2]<cg[0] else "GROW"
    gtrend="DECAY" if gg[1]<gg[0] else "GROW"
    print(f"{str(D):<14}{ex:>+7.3f} | {cg[0]:>8.3f}{cg[1]:>9.3f}{cg[2]:>9.3f} {ctrend:>7} | {gg[0]:>8.3f}{gg[1]:>8.3f} {gtrend:>7}")
print("\nmaverick claim: with CENTRAL gap, strict excess >=~0.04 DECAYS; only GROW = {3,4,6}(MW-pair 6=2*3) & {3,4,7}(boundary).")
