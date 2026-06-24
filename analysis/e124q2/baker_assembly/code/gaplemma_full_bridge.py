import math, time
N0=3982888
log3=math.log(3); log4=math.log(4); log7=math.log(7)
# Run the gap-lemma bridge check incrementally as far as feasible, timing it,
# to give team-lead a precise feasibility number. The running sum 'acc' grows to
# ~10^140227 (a 140k-digit int); each step is one add of a ~D-digit atom + compare.
# Generate atoms in sorted order by merging three exponent streams (compare by value).
def run_bridge(max_p3):
    # max_p3 = max exponent of 3 to include (sets the ceiling ~3^max_p3)
    V0 = 3**max_p3
    # build merged sorted atom stream via heap of (value, base, exp)
    import heapq
    h=[]
    for base in (3,4,7):
        heapq.heappush(h,(base**2, base, 2))
    acc=0; ok=True; minm=None; count=0; nbad=0
    while h:
        v,base,e = heapq.heappop(h)
        if v > V0: break
        if v > 14348907:
            m = acc - (v + 2*N0)
            if minm is None or m<minm: minm=m
            if m<0: ok=False; nbad+=1
        acc += v
        count+=1
        ne=e+1; heapq.heappush(h,(base**ne, base, ne))
    return ok, minm, count, V0

# Time a moderate run and extrapolate
for max_p3 in [1000, 5000, 20000]:
    t0=time.time()
    ok,minm,count,V0 = run_bridge(max_p3)
    dt=time.time()-t0
    print("to 3^%d (~10^%.0f): %s, min margin=%d, %d atoms, %.2fs" % 
          (max_p3, max_p3*log3/math.log(10), "PASS" if ok else "FAIL", minm, count, dt))
print()
# extrapolate to full p*=293903
print("Extrapolation: atom count scales linearly with p*; bigint ops scale ~p*^2")
print("(running sum is D-digit, D~p*, so total ~ sum of D over atoms ~ p*^2/const).")
print("Full p*=293903 is ~%.0fx the 20000 run in p, ~%.0fx in p^2." % (293903/20000, (293903/20000)**2))
