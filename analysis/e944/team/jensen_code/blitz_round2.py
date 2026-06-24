"""
INVENTION BLITZ — jensen/parity lane, ROUND 2. Fixes informed by round 1.
Target: 4-vertex-critical, 0 critical edges; δ≥6, entangled.

J4' Dihedral/dicyclic Cayley SWEEP — non-abelian, n=14..18, search inverse-closed
    6+-regular conn sets for χ=4 ∧ vertex-critical, then min #critical edges. (LIVE LEAD)
J2' Toroidal antiprism — wrap layers into a torus (no boundary) + 2nd-neighbor diagonals → δ≥6.
J3' Complement of DENSER triangle-free base (C_n^2 = circulant(n,{1,2}), still triangle-free for n≥... ;
    or complement of a triangle-free Cayley graph) — aim χ=4 ∧ δ≥6.
J5  ℤ₃-tension-FIRST: design a nonvanishing ℤ₃ tension on a dense template directly.
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import itertools
import networkx as nx
from harness import chromatic_number, is_vertex_critical, critical_edges


def score(G, name, quiet_fail=False):
    if not nx.is_connected(G):
        if not quiet_fail: print(f"{name}: DISCONNECTED")
        return None
    n=G.number_of_nodes(); m=G.number_of_edges()
    chi=chromatic_number(G); dmin=min(d for _,d in G.degree())
    if chi!=4:
        if not quiet_fail: print(f"{name}: n={n} m={m} δ={dmin} χ={chi}")
        return chi
    vc=is_vertex_critical(G,4)
    if not vc:
        if not quiet_fail: print(f"{name}: n={n} m={m} δ={dmin} χ=4 vtx-crit=False")
        return chi
    ce=critical_edges(G); br=len(list(nx.bridges(G)))
    tag="  *** WITNESS ***" if len(ce)==0 else ""
    print(f"{name}: n={n} m={m} δ={dmin} χ=4 vtx-crit=True #critical={len(ce)} bridges={br}{tag}")
    return chi


# ---- J4' dihedral Cayley ----
def dihedral_cayley(k, conn):
    G=nx.Graph(); elems=[(j,e) for j in range(k) for e in (0,1)]; G.add_nodes_from(elems)
    def mul(a,b):
        (j1,e1),(j2,e2)=a,b
        return ((j1+j2)%k,e2) if e1==0 else ((j1-j2)%k,1-e2)
    for a in elems:
        for g in conn: G.add_edge(a,mul(a,g))
    return G

def inverse_closed_sets(k, size):
    """Generate inverse-closed connection sets of D_k (excluding identity).
    rotations (dj,0): inverse (-dj,0); reflections (dj,1): self-inverse.
    We pick some rotation pairs + some reflections to reach `size` generators."""
    rots=[(j,0) for j in range(1,k)]
    refls=[(j,1) for j in range(k)]
    # build inverse-closed: rotation chosen => add its inverse; reflections free
    out=[]
    # try a few structured sets
    import random
    random.seed(0)
    for _ in range(40):
        S=set()
        # add 1-2 rotation pairs
        for _ in range(random.randint(1,2)):
            j=random.randint(1,k-1); S.add((j,0)); S.add(((-j)%k,0))
        # add reflections to fill
        nref=size-len(S)
        if nref<=0: continue
        chosen=random.sample(refls, min(nref,len(refls)))
        for r in chosen: S.add(r)
        if (0,0) in S: S.discard((0,0))
        out.append(sorted(S))
    return out


# ---- J2' toroidal antiprism ----
def toroidal_antiprism(layers, w, diag2=True):
    G=nx.Graph()
    for L in range(layers):
        for i in range(w):
            G.add_edge((L,i),(L,(i+1)%w))
    for L in range(layers):  # wrap: layer L to L+1 mod layers
        Ln=(L+1)%layers
        for i in range(w):
            G.add_edge((L,i),(Ln,i))
            G.add_edge((L,i),(Ln,(i+1)%w))
            if diag2:
                G.add_edge((L,i),(Ln,(i-1)%w))  # extra diagonal → δ up
    return G


# ---- J3' complement of denser triangle-free base ----
def complement_of(baseG):
    return nx.complement(baseG)


# ---- J5 ℤ₃-tension-first dense template ----
def z3_tension_graph(n, shifts):
    """Build on Z_n: connect i to i+s for each s in shifts (circulant-like) BUT then
    add a 'monodromy defect' edge set that forces the ℤ₃-tension nonzero. Concretely:
    a circulant whose total shift around the n-cycle is ≢0 mod 3 forces χ≥4 if the
    structure is right. We just score dense circulants here as a tension-first probe
    (distinct seeds from count: we pick shifts to make EVERY vertex in 3 short odd
    structures). This overlaps count's circulant space — kept SMALL and flagged."""
    G=nx.circulant_graph(n, shifts)
    return G


if __name__=="__main__":
    print("=== BLITZ ROUND 2 (jensen lane) ===")
    print("-- J4' dihedral Cayley sweep (non-abelian) --")
    found=0
    for k in (7,8,9):
        for S in inverse_closed_sets(k,6):
            G=dihedral_cayley(k,S)
            r=score(G,f"D{k} conn={S}",quiet_fail=True)
            if r==4:
                # only print the χ=4 ones loudly
                score(G,f"D{k} conn={S}")
                found+=1
                if found>=12: break
        if found>=12: break
    if found==0: print("  (no χ=4 dihedral Cayley in swept sets)")

    print("-- J2' toroidal antiprism --")
    for (L,w) in [(3,4),(3,5),(4,5),(5,5),(4,6)]:
        score(toroidal_antiprism(L,w), f"J2'(L={L},w={w})")

    print("-- J3' complement of denser triangle-free base --")
    for n in (10,11,12,13):
        base=nx.circulant_graph(n,[1,2])  # triangle-free? 1,2 has triangles (i,i+1,i+2). use [1,3]
    for n in (11,12,13,14):
        base=nx.circulant_graph(n,[1,4])  # tri-free for suitable n
        if max((len(c) for c in nx.find_cliques(base)),default=2)<=2:
            score(complement_of(base),f"J3' comp(C_{n}(1,4)) [tri-free base]")
        else:
            print(f"J3' base C_{n}(1,4) has triangles, skip")

    print("-- J5 ℤ₃-tension-first dense circulant probe (flagged: overlaps count) --")
    for n in (13,16):
        for shifts in [[1,5],[2,3],[1,5,6]]:
            score(z3_tension_graph(n,shifts),f"J5 C_{n}{shifts}",quiet_fail=True) or None
