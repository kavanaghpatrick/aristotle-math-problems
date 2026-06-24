#!/usr/bin/env python3
"""
forge_chrompoly_bridge.py — bridge vertex-criticality to gallai's B₁ = Σ_e P(G−e,3) > 0
via chromatic-polynomial identities. Target: χ=4 vertex-critical ⟹ B₁ > 0.

KNOWN (gallai): P(G,3)=0 (χ=4) ⟹ B₁(G) = #{3-colorings mono on exactly 1 edge}
= Σ_{e∈E} P(G−e,3) (deletion-contraction: P(G−e)=P(G)+P(G/e), and at x=3 with
P(G,3)=0, each term P(G−e,3) counts colorings proper on G−e; mono-on-exactly-one
follows). B₁>0 ⟺ ∃ critical edge ⟺ NOT a witness.

forge's structural inputs to test as bridges:
1. Vertex-criticality ⟹ P(G−v,3) > 0 for EVERY v (G−v is 3-colorable).
2. deg-3 theorem: a deg-3 vertex ⟹ 3 critical edges ⟹ those P(G−e,3)>0.
3. Per-vertex lemma ⟹ v has a critical edge ⟺ some 3-coloring of G−v unbalanced on N(v).

CANDIDATE BRIDGE IDENTITIES to test on 4vc graphs n≤9:
 (A) Σ_v P(G−v,3) vs B₁ = Σ_e P(G−e,3): is there a sign/positivity relation?
 (B) P'(G,3) (derivative): Σ_v P(G−v,x) = P'(G,x)? (vertex-deletion derivative
     identity). And Σ_e relates to a different derivative.
 (C) The combinatorial reciprocity / Whitney-rank generating function at x=3.
We compute all and look for "vertex-criticality forces B₁>0" structurally.
"""
import itertools
import networkx as nx
import sympy as sp
from forge_verify import is_k_colorable, critical_edges


def chrom_poly(G):
    x = sp.symbols('x')
    return sp.Poly(nx.chromatic_polynomial(G), x), x


def P_at(G, k):
    """P(G,k) integer via chromatic polynomial evaluated at k."""
    x = sp.symbols('x')
    cp = nx.chromatic_polynomial(G)
    return int(sp.Poly(cp, x).eval(k))


def is_4vc(G):
    if is_k_colorable(G, 3) or not is_k_colorable(G, 4):
        return False
    for v in G.nodes():
        H = G.copy(); H.remove_node(v)
        if not is_k_colorable(H, 3):
            return False
    return True


def analyze(G, name):
    n = G.number_of_nodes()
    P3 = P_at(G, 3)  # = 0 for chi>=4
    # B1 = sum over edges of P(G-e, 3)
    B1 = 0
    for e in G.edges():
        H = G.copy(); H.remove_edge(*e)
        B1 += P_at(H, 3)
    # sum over vertices of P(G-v,3)
    SV = 0
    for v in G.nodes():
        H = G.copy(); H.remove_node(v)
        SV += P_at(H, 3)
    # derivative of P at 3
    x = sp.symbols('x')
    cp = sp.Poly(nx.chromatic_polynomial(G), x)
    Pp3 = int(cp.diff(x).eval(3))
    ce = len(critical_edges(G, 4))
    print(f"[{name}] n={n} P(G,3)={P3} B1=Σ_e P(G-e,3)={B1} "
          f"Σ_v P(G-v,3)={SV} P'(G,3)={Pp3} #crit_edges={ce}", flush=True)
    return P3, B1, SV, Pp3, ce


if __name__ == "__main__":
    import subprocess
    GENG = "/opt/homebrew/bin/geng"
    print("=== chromatic-polynomial bridge on 4vc graphs n=7,8 ===", flush=True)
    print("Testing: does vertex-criticality (Σ_v P(G-v,3)>0, all terms>0) force B1>0?", flush=True)
    rows = []
    for n in (7, 8):
        out = subprocess.run([GENG, "-c", "-d3", str(n)], capture_output=True, text=True)
        cnt = 0
        for g6 in out.stdout.split():
            G = nx.from_graph6_bytes(g6.encode())
            if not is_4vc(G):
                continue
            cnt += 1
            if cnt > 12:  # sample
                break
            r = analyze(G, f"n{n}#{cnt}")
            rows.append(r)
    print("\n=== Relations check ===", flush=True)
    # Is B1 always > 0? Is Σ_v P(G-v,3) always > 0 (yes, vertex-critical)? sign of P'(3)?
    allB1pos = all(r[1] > 0 for r in rows)
    allSVpos = all(r[2] > 0 for r in rows)
    print(f"all B1>0: {allB1pos}; all Σ_v P(G-v,3)>0: {allSVpos}", flush=True)
    # ratio / relation between B1, SV, P'(3)
    for r in rows[:6]:
        print(f"  P3={r[0]} B1={r[1]} SV={r[2]} Pp3={r[3]} crit={r[4]} | "
              f"B1 vs SV ratio={r[1]/r[2]:.3f}", flush=True)
