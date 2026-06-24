import sys; sys.path.insert(0,'.')
from floor_worker import parse_graph6, k_colorable, deg_order
# Reuse the exact predicate (is_witness equiv) and compare against a THM2 early-out screen.
# THM2 early-out (NECESSARY for witness): for vertex u, take ONE 3-coloring of G-u; if the colors
# appearing on N(u) are fewer than 3 (some color absent), then placing u is free => u removable =>
# but that's about vertex-criticality... Actually for NO CRITICAL EDGE at u: every edge uv non-crit
# requires N(u) rainbow in every 3-coloring of G-u. A single 3-coloring of G-u with N(u) non-rainbow
# is a WITNESS that some edge at u IS critical. So: reject if exists u with a 3-coloring of G-u where
# N(u) misses a color. This is a sound NECESSARY-condition screen (rejects only non-witnesses).
def three_coloring_of(adj, n):
    color=[-1]*n; order=deg_order(adj,n)
    def bt(i):
        if i==n: return True
        v=order[i]; forb=0; nb=adj[v]
        while nb:
            low=nb&(-nb); u=low.bit_length()-1
            if color[u]>=0: forb|=(1<<color[u])
            nb^=low
        for c in range(3):
            if not (forb>>c)&1:
                color[v]=c
                if bt(i+1): return True
                color[v]=-1
        return False
    return color[:] if bt(0) else None

def thm2_screen_says_reject(adj, n):
    # for each u: G-u, 3-color it, check N(u) spans 3 colors. If any single coloring non-rainbow -> reject.
    for u in range(n):
        keep=[w for w in range(n) if w!=u]; remap={w:i for i,w in enumerate(keep)}
        sub=[0]*(n-1)
        for w in keep:
            nb=adj[w]&~(1<<u); rw=remap[w]
            while nb:
                low=nb&(-nb); x=low.bit_length()-1; sub[rw]|=(1<<remap[x]); nb^=low
        col=three_coloring_of(sub,n-1)
        if col is None: continue  # G-u not 3-colorable -> u not critical, different rejection
        Nu=[w for w in range(n) if (adj[u]>>w)&1]
        seen=set(col[remap[w]] for w in Nu)
        if len(seen)<3:
            return True  # some edge at u is critical
    return False
print("thm2 screen module loaded")
