import math, time, heapq
N0=3982888; twoN0=2*N0
# ============================================================
# INCREMENTAL bridge: maintain running powers per base (one multiply per step),
# a running atomSum 'acc' (one add per step), and the next power per base.
# atomSum(<v) for the next atom v = acc BEFORE adding v (sorted order). This is
# exactly Aristotle's gapOK accumulator but we keep the powers incrementally so
# we never recompute d**e from scratch. The cost is O(1) bigint mul + add per atom.
# Total ~ N_atoms * O(maxdigits) for the running ops. The KILLER was d**e recompute;
# incremental mul fixes it.
# ============================================================
def run(H_log10):
    lnH = H_log10*math.log(10)
    V0_3exp = int(lnH/math.log(3)) + 2  # cap
    # heap of (value, base); maintain current power per base
    cur = {3:9, 4:16, 7:49}  # d^2
    h = [(cur[d], d) for d in (3,4,7)]
    heapq.heapify(h)
    cap = 3**V0_3exp
    acc = 0
    minmargin=None; argmin=None; ok=True; checked=0; total=0; first_fail=None
    while h:
        v, d = heapq.heappop(h)
        if v > cap: break
        if v > 14348907:
            margin = acc - (v + twoN0)
            checked += 1
            if minmargin is None or margin < minmargin: minmargin=margin; argmin=(d, v)
            if margin < 0 and first_fail is None: ok=False; first_fail=(d, v, margin)
        acc += v
        total += 1
        nxt = v * d   # next power of d (one multiply)
        heapq.heappush(h, (nxt, d))
    return ok, minmargin, argmin, checked, total, first_fail, V0_3exp

# Time a moderate height first, then extrapolate / decide
for H in [50000, 120000]:
    t0=time.time()
    ok,mm,am,ck,tot,ff,v0e = run(H)
    dt=time.time()-t0
    md=am[1] if am else 0
    ndig = len(str(am[1])) if am else 0
    print("to 10^%-7d: ok=%s minmargin=%d (%d atoms, %.1fs)" % (H, ok, mm, tot, dt))
