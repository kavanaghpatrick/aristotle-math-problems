#!/usr/bin/env python3
"""
forge_blitz_r1.py — kill-tests for forge invention-ledger round 1:
  forge-1: edge-entangled triangle-cover (every edge in >=2 edge-disjoint triangles, delta>=6)
  forge-2: double shift graph / iterated line-digraph (global ordering obstruction)
  forge-3: asymmetric independent-set blow-up of the n=10 champion ICpdbY{]_
All dual-verified with checkers.py.
"""
import itertools
import subprocess
import networkx as nx
from forge_verify import is_k_colorable, is_vertex_critical, critical_edges
import checkers

GENG = "/opt/homebrew/bin/geng"


def chi4(G):
    return (not is_k_colorable(G, 3)) and is_k_colorable(G, 4)


def is_4vc(G):
    if not chi4(G):
        return False
    for v in G.nodes():
        H = G.copy(); H.remove_node(v)
        if not is_k_colorable(H, 3):
            return False
    return True


def reduce_to_4vc(G):
    H = nx.convert_node_labels_to_integers(G)
    if is_k_colorable(H, 3) or not is_k_colorable(H, 4):
        return None
    changed = True
    while changed:
        changed = False
        for v in list(H.nodes()):
            K = H.copy(); K.remove_node(v)
            if K.number_of_nodes() >= 4 and (not is_k_colorable(K, 3)) and is_k_colorable(K, 4):
                H = K; changed = True; break
    return nx.convert_node_labels_to_integers(H)


def report(G, name):
    G = nx.convert_node_labels_to_integers(G)
    degs = sorted(d for _, d in G.degree())
    if not chi4(G):
        c = 2 if is_k_colorable(G, 2) else (3 if is_k_colorable(G, 3) else ">=5")
        print(f"[{name}] n={G.number_of_nodes()} m={G.number_of_edges()} chi={c} "
              f"mindeg={degs[0] if degs else '-'}", flush=True)
        return None
    vc, _, bad = is_vertex_critical(G, 4)
    ce = critical_edges(G, 4)
    m = G.number_of_edges()
    print(f"[{name}] n={G.number_of_nodes()} m={m} chi=4 mindeg={degs[0]} "
          f"vc={vc} noncrit_v={len(bad)} |E*|={len(ce)} redundant={m-len(ce)}", flush=True)
    if vc and len(ce) == 0:
        edges = [tuple(sorted(e)) for e in G.edges()]
        if checkers.is_erdos944_k_r1(edges, G.number_of_nodes(), 4):
            print(f"  *** DUAL-VERIFIED WITNESS: {name} ***", flush=True)
            return ("W", G)
    return (len(ce) if vc else None, G)


# ---------- forge-1: edge-entangled triangle-cover ----------
def every_edge_in_ge2_triangles(G):
    for u, v in G.edges():
        common = set(G[u]) & set(G[v])
        if len(common) < 2:
            return False
    return True


def test_forge1():
    print("=== forge-1: edge-entangled triangle-cover (delta>=6, every edge in >=2 triangles) ===", flush=True)
    best = None
    for n in (11, 12, 13):
        # stream geng delta>=6; filter the triangle property; this is a strong filter
        proc = subprocess.Popen([GENG, "-c", "-d6", str(n)], stdout=subprocess.PIPE, text=True, bufsize=1)
        seen = 0; passed = 0
        for line in proc.stdout:
            line = line.strip()
            if not line:
                continue
            seen += 1
            if seen > 60000:  # cap per n
                proc.terminate(); break
            G = nx.from_graph6_bytes(line.encode())
            if not every_edge_in_ge2_triangles(G):
                continue
            if not chi4(G):
                continue
            passed += 1
            R = reduce_to_4vc(G)
            if R is None:
                continue
            ce = critical_edges(R, 4); vc, _, _ = is_vertex_critical(R, 4)
            if vc and (best is None or len(ce) < best[0]):
                best = (len(ce), R.copy(), n, line)
                print(f"  n={n} g6={line}: 4vc-reduced |E*|={len(ce)} "
                      f"(n={R.number_of_nodes()})", flush=True)
                if len(ce) == 0:
                    edges = [tuple(sorted(e)) for e in nx.convert_node_labels_to_integers(R).edges()]
                    if checkers.is_erdos944_k_r1(edges, R.number_of_nodes(), 4):
                        print(f"  *** WITNESS forge-1 n={n} ***", flush=True)
                        proc.terminate(); return best
        try:
            proc.terminate()
        except Exception:
            pass
        print(f"  n={n}: scanned {seen} delta>=6 graphs, {passed} passed triangle+chi4 filter", flush=True)
    print(f"  forge-1 best |E*|={best[0] if best else 'none'}", flush=True)
    return best


# ---------- forge-2: shift graphs ----------
def shift_graph(n):
    """S(n): vertices ordered pairs (i,j) i<j in [n]; (i,j)~(k,l) iff j=k or l=i. chi=ceil(log2 n)."""
    V = [(i, j) for i in range(n) for j in range(i + 1, n)]
    G = nx.Graph(); G.add_nodes_from(V)
    for a in V:
        for b in V:
            if a < b and (a[1] == b[0] or b[1] == a[0]):
                G.add_edge(a, b)
    return nx.convert_node_labels_to_integers(G)


def double_shift_graph(n):
    """DS(n): vertices ordered triples i<j<k; (i,j,k)~(j,k,l) style adjacency. chi ~ log log."""
    V = [(i, j, k) for i in range(n) for j in range(i + 1, n) for k in range(j + 1, n)]
    G = nx.Graph(); G.add_nodes_from(V)
    for a in V:
        for b in V:
            if a < b:
                # adjacency: share a 2-suffix/prefix (the line-digraph-of-shift adjacency)
                if a[1] == b[0] and a[2] == b[1]:
                    G.add_edge(a, b)
                if b[1] == a[0] and b[2] == a[1]:
                    G.add_edge(a, b)
    return nx.convert_node_labels_to_integers(G)


def test_forge2():
    print("\n=== forge-2: shift / double-shift graphs (global ordering obstruction) ===", flush=True)
    best = None
    for n in range(4, 9):
        G = shift_graph(n)
        r = report(G, f"S({n})")
        if r and r[0] == "W":
            return r
        if r and isinstance(r[0], int) and (best is None or r[0] < best[0]):
            best = (r[0], r[1])
    for n in range(5, 9):
        G = double_shift_graph(n)
        r = report(G, f"DS({n})")
        if r and r[0] == "W":
            return r
        if r and isinstance(r[0], int) and (best is None or r[0] < best[0]):
            best = (r[0], r[1])
    print(f"  forge-2 best |E*|={best[0] if best else 'none'}", flush=True)
    return best


# ---------- forge-3: blow-up of n=10 champion ----------
def blowup(G, sizes):
    H = nx.Graph()
    for v in G.nodes():
        for a in range(sizes[v]):
            H.add_node((v, a))
    for u, v in G.edges():
        for a in range(sizes[u]):
            for b in range(sizes[v]):
                H.add_edge((u, a), (v, b))
    return nx.convert_node_labels_to_integers(H)


def test_forge3():
    print("\n=== forge-3: asymmetric independent-set blow-up of n=10 champion ===", flush=True)
    G = nx.convert_node_labels_to_integers(nx.from_graph6_bytes("ICpdbY{]_".encode()))
    ce = set()
    for u, v in critical_edges(G, 4):
        ce.add(u); ce.add(v)
    best = None
    # try several asymmetric blow-up size patterns: larger on critical-edge endpoints
    patterns = []
    patterns.append({v: (2 if v in ce else 1) for v in G.nodes()})
    patterns.append({v: (3 if v in ce else 1) for v in G.nodes()})
    patterns.append({v: (2 if v in ce else 2) for v in G.nodes()})  # uniform 2 (control)
    # asymmetric: alternate sizes among critical endpoints
    import random
    rng = random.Random(0)
    for t in range(6):
        patterns.append({v: (rng.choice([1, 2, 3]) if v in ce else rng.choice([1, 2]))
                         for v in G.nodes()})
    for i, sizes in enumerate(patterns):
        H = blowup(G, sizes)
        r = report(H, f"blowup#{i} sizes~{sorted(set(sizes.values()))}")
        if r and r[0] == "W":
            return r
        if r and isinstance(r[0], int) and (best is None or r[0] < best[0]):
            best = (r[0], r[1])
    print(f"  forge-3 best |E*|={best[0] if best else 'none'}", flush=True)
    return best


if __name__ == "__main__":
    test_forge3()   # fastest first
    test_forge2()
    test_forge1()   # slowest (geng stream) last
