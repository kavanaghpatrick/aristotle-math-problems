"""
ADVERSARIAL VERIFIER ground-truth for E124 baker_assembly.
Independent computation of:
  (1) the closest |3^p - 4^q| spacings (the MW quantity the campaign must bound)
  (2) continued-fraction convergents of log4/log3 (NOT log(4/3) -- the classic retrieval error)
  (3) the empirical "C in exp(-C (log p)^2)" fit the team claims (C ~= 1.22, p<=79)
Uses exact Python ints for the powers; high-precision mpmath for the logs.
"""
from math import log
try:
    import mpmath as mp
    mp.mp.dps = 60
    HAVE_MP = True
except ImportError:
    HAVE_MP = False

# ---- (2) CF of log4/log3 vs log(4/3): the classic error to guard ----
if HAVE_MP:
    theta = mp.log(4)/mp.log(3)        # = log_3(4) = 1.2618595... wait check
    theta2 = mp.log(mp.mpf(4)/3)       # log(4/3) = 0.287682...
    print("log(4)/log(3)  =", mp.nstr(theta, 20))
    print("log(4/3)       =", mp.nstr(theta2, 20))
    # The campaign says log4/log3 = 0.79248. That is log(3)/log(4)! Check both.
    print("log(3)/log(4)  =", mp.nstr(mp.log(3)/mp.log(4), 20))
    # CF of log(3)/log(4) (the 0.79248 value the docs cite)
    val = mp.log(3)/mp.log(4)
    cf = []
    x = val
    for _ in range(15):
        a = int(mp.floor(x)); cf.append(a)
        frac = x - a
        if frac == 0: break
        x = 1/frac
    print("CF of log3/log4 (=0.7925):", cf[:12])
    # convergents
    h0,h1 = 1, cf[0]; k0,k1 = 0,1
    print("convergents p/q of log3/log4:")
    h_prev, h_cur = 1, cf[0]; k_prev, k_cur = 0, 1
    print(f"  {cf[0]}/1")
    for a in cf[1:10]:
        h_next = a*h_cur + h_prev
        k_next = a*k_cur + k_prev
        print(f"  {h_next}/{k_next}  (a={a})")
        h_prev,h_cur = h_cur,h_next
        k_prev,k_cur = k_cur,k_next

# ---- (1) closest |3^p - 4^q| spacings, exact ints ----
print("\n=== closest |3^p - 4^q| relative spacings (exact ints), p<=80 ===")
records = []
for p in range(1, 81):
    P = 3**p
    # nearest q
    q = round(p*log(3)/log(4))
    best = None
    for qq in (q-1,q,q+1,q+2):
        if qq < 1: continue
        Q = 4**qq
        d = abs(P-Q)
        rel = d / min(P,Q)
        if best is None or rel < best[0]:
            best = (rel, qq, d)
    records.append((p, best[1], best[2], best[0]))
records.sort(key=lambda r: r[3])
print("p, q, |3^p-4^q|, rel = |diff|/min")
for p,q,d,rel in records[:12]:
    print(f"  p={p:3d} q={q:3d}  rel={rel:.6e}")

# ---- (3) the C fit: rel >= exp(-C (log p)^2) => C >= -ln(rel)/(log p)^2 ----
print("\n=== implied C in rel >= exp(-C (ln p)^2) ===")
worst_C = 0; worst = None
for p,q,d,rel in records:
    if p < 2 or rel <= 0: continue
    C = -log(rel)/(log(p)**2)
    if C > worst_C:
        worst_C = C; worst = (p,q,rel,C)
print(f"worst-case (largest) C over p in [2,80]: C={worst_C:.4f} at p={worst[0]}, q={worst[1]}, rel={worst[2]:.4e}")
print("(team claims C ~= 1.22, closest p=53 q=42 rel=2.09e-3)")
