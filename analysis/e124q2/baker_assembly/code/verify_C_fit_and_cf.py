"""Pin down: (a) correct CF labeling for the close pairs, (b) C-fit instability."""
from math import log
import mpmath as mp
mp.mp.dps = 60

# (a) Close pair (3^p, 4^q): 3^p ~ 4^q  <=> p log3 ~ q log4 <=> p/q ~ log4/log3 = 1.26186
# so q/p ~ log3/log4 = 0.79248. The convergents h/k of log3/log4 give q/p? or p/q?
# log3/log4 = 0.79248 ; its convergents are 3/4, 4/5, 19/24, 23/29, 42/53...
# For 3/4: is it p/q or q/p? Test 3^3 vs 4^4=256 vs 3^4=81... 3^p~4^q.
# convergent 3/4 of 0.79248: 3/4=0.75. If this is q/p then q=3,p=4: 3^4=81, 4^3=64 rel 0.27 (not close)
# if p/q then p=3,q=4: 3^3=27,4^4=256 (not close). Hmm. Try 19/24: 19/24=0.7917.
# q/p=19/24 => q=19,p=24: 3^24 vs 4^19. p/q=19/24=>p=19,q=24:3^19 vs 4^24.
for (a,b) in [(3,4),(4,5),(19,24),(23,29),(42,53)]:
    # interpret as q/p = a/b  => p=b, q=a
    p,q = b,a
    P,Q = 3**p, 4**q
    rel1 = abs(P-Q)/min(P,Q)
    # interpret as p/q = a/b => p=a,q=b
    p2,q2 = a,b
    P2,Q2 = 3**p2, 4**q2
    rel2 = abs(P2-Q2)/min(P2,Q2)
    print(f"conv {a}/{b}: as q/p -> p={b},q={a} rel={rel1:.4e} | as p/q -> p={a},q={b} rel={rel2:.4e}")

print()
print("Docs claim close pairs at p in {5,19,24,29,34}, q~{4,15,19,23,27}.")
for p,q in [(5,4),(19,15),(24,19),(29,23),(34,27)]:
    P,Q=3**p,4**q
    print(f"  (3^{p},4^{q}): rel={abs(P-Q)/min(P,Q):.4e}, p/q={p/q:.5f}")

# (b) C-fit over GROWING ranges: show worst-case C is range-dependent => not a proven constant
print("\n=== worst-case C over growing p-ranges (instability check) ===")
def worst_C(pmax):
    wc=0; arg=None
    for p in range(2,pmax+1):
        P=3**p
        q=round(p*log(3)/log(4))
        best=min((abs(P-4**qq)/min(P,4**qq), qq) for qq in (q-1,q,q+1) if qq>=1)
        rel=best[0]
        if rel<=0: continue
        C=-log(rel)/(log(p)**2)
        if C>wc: wc=C; arg=(p,best[1],rel)
    return wc,arg
for pmax in [20,40,80,150,300,600]:
    wc,arg=worst_C(pmax)
    print(f"  pmax={pmax:4d}: worst C={wc:.4f} at p={arg[0]}, rel={arg[2]:.3e}")
