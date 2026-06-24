import sys
sys.path.insert(0, "/Users/patrickkavanagh/math/analysis/e944/team")
from floor_worker import parse_graph6, k_colorable, deg_order
from collections import Counter
hist = Counter()  # min-degree of each 4-vertex-critical graph
total = 0; vc4 = 0
for line in sys.stdin:
    line = line.strip()
    if not line: continue
    total += 1
    n, adj = parse_graph6(line)
    order = deg_order(adj, n)
    if k_colorable(adj, n, 3, order): continue
    if not k_colorable(adj, n, 4, order): continue
    # vertex-critical?
    ok = True
    for v in range(n):
        keep=[u for u in range(n) if u!=v]; remap={u:i for i,u in enumerate(keep)}
        sub=[0]*(n-1)
        for u in keep:
            nb=adj[u]&~(1<<v); ru=remap[u]
            while nb:
                low=nb&(-nb); w=low.bit_length()-1; sub[ru]|=(1<<remap[w]); nb^=low
        if not k_colorable(sub,n-1,3,deg_order(sub,n-1)): ok=False; break
    if not ok: continue
    vc4 += 1
    mindeg = min(bin(adj[v]).count("1") for v in range(n))
    hist[mindeg]+=1
import json
print(json.dumps({"total":total,"vc4":vc4,"mindeg_hist":dict(sorted(hist.items()))}))
