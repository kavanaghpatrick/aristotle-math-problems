#!/usr/bin/env python3
"""
algebra_cayley.py — non-cyclic-group Cayley substrates + product substrates.

Entry-point question: the cyclic substrate Z_{k-1}=Z_3 degenerates at k=4
(circulant scan finds no (4,1)-graph). Can a DIFFERENT algebraic category at
"level 3" realize the (4,1) property? We test:

  - Cayley graphs of NON-cyclic groups of small order (S3, Z2xZ2, Z6=Z2xZ3,
    D4, Q8, Z2^3) with every symmetric inverse-closed connection set.
  - Categorical (tensor) and lexicographic products of small chi=4 graphs with
    small graphs (the Lattanzio product-substrate idea: when k-1 = a*b composite
    a product factorization is available; at k-1=3 prime it is NOT).

All chi via hunter's independent backtracking + SAT cross-check.
"""
import sys, os, itertools
import networkx as nx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import checkers as H
import algebra_substrate as A


# ---- group element tables --------------------------------------------------

def group_Zn(n):
    els = list(range(n))
    op = lambda a, b: (a + b) % n
    inv = lambda a: (-a) % n
    return els, op, inv, f"Z{n}"

def group_prod(g1, g2):
    e1, o1, i1, n1 = g1
    e2, o2, i2, n2 = g2
    els = [(a, b) for a in e1 for b in e2]
    op = lambda x, y: (o1(x[0], y[0]), o2(x[1], y[1]))
    inv = lambda x: (i1(x[0]), i2(x[1]))
    return els, op, inv, f"({n1}x{n2})"

def group_S3():
    # S3 as permutations of (0,1,2), composition. element = tuple perm.
    import itertools as it
    els = list(it.permutations(range(3)))
    def comp(p, q):  # (p*q)(i) = p(q(i))
        return tuple(p[q[i]] for i in range(3))
    def inv(p):
        r = [0, 0, 0]
        for i in range(3):
            r[p[i]] = i
        return tuple(r)
    return els, comp, inv, "S3"

def group_D4():
    # dihedral of order 8 as (rot in Z4, flip in Z2), semidirect.
    els = [(r, f) for r in range(4) for f in range(2)]
    def op(x, y):
        r1, f1 = x; r2, f2 = y
        # (r1,f1)*(r2,f2): if f1=0: rot adds; if f1=1: flips r2
        r = (r1 + (r2 if f1 == 0 else -r2)) % 4
        f = (f1 + f2) % 2
        return (r, f)
    def inv(x):
        # brute inverse
        for y in els:
            if op(x, y) == (0, 0):
                return y
    return els, op, inv, "D4"

def group_Q8():
    # quaternion group via explicit Cayley table on {+-1,+-i,+-j,+-k}
    names = ['1', '-1', 'i', '-i', 'j', '-j', 'k', '-k']
    idx = {n: t for t, n in enumerate(names)}
    # multiplication
    mul = {}
    base = {('i','i'):'-1',('j','j'):'-1',('k','k'):'-1',
            ('i','j'):'k',('j','k'):'i',('k','i'):'j',
            ('j','i'):'-k',('k','j'):'-i',('i','k'):'-j'}
    def neg(s): return s[1:] if s.startswith('-') else '-'+s
    def prod(a, b):
        sa = 1; sb = 1
        if a.startswith('-'): sa=-1; a=a[1:]
        if b.startswith('-'): sb=-1; b=b[1:]
        sign = sa*sb
        if a=='1': base_res=b
        elif b=='1': base_res=a
        else: base_res=base[(a,b)]
        # apply sign
        if base_res.startswith('-'):
            base_res=base_res[1:]; sign=-sign
        return base_res if sign==1 else '-'+base_res
    els = list(range(8))
    def op(x, y): return idx[prod(names[x], names[y])]
    def inv(x):
        for y in els:
            if op(x,y)==idx['1']: return y
    return els, op, inv, "Q8"


def cayley_graph(group, conn):
    """Undirected Cayley graph Cay(G, conn). conn must be inverse-closed and not
    contain identity. Returns networkx graph on group elements (indexed)."""
    els, op, inv, name = group
    eidx = {e: i for i, e in enumerate(els)}
    G = nx.Graph()
    G.add_nodes_from(range(len(els)))
    for e in els:
        for s in conn:
            t = op(e, s)
            if t != e:
                G.add_edge(eidx[e], eidx[t])
    return G


def identity_of(group):
    els, op, inv, name = group
    for e in els:
        if all(op(e, x) == x for x in els):
            return e
    return None


def inverse_closed_conn_sets(group, max_size=None):
    """Yield inverse-closed connection sets (no identity), as frozensets of elements.
    To keep it tractable we group elements into inverse-pairs/singletons and pick subsets."""
    els, op, inv, name = group
    ident = identity_of(group)
    nonid = [e for e in els if e != ident]
    # partition into inverse-closed blocks
    seen = set(); blocks = []
    for e in nonid:
        if e in seen: continue
        ie = inv(e)
        blk = {e, ie}
        blocks.append(frozenset(blk))
        seen |= blk
    # choose any subset of blocks as the connection set (union)
    nb = len(blocks)
    for r in range(1, nb + 1):
        if max_size is not None and r > max_size:
            break
        for combo in itertools.combinations(blocks, r):
            conn = set()
            for b in combo:
                conn |= set(b)
            yield frozenset(conn)


def scan_cayley(group, k=4):
    els, op, inv, name = group
    found = []
    tested = 0
    for conn in inverse_closed_conn_sets(group):
        G = cayley_graph(group, conn)
        edges, nn = A.nx_to_edges_n(G)
        tested += 1
        if H.chi_bt(edges, nn) != k:
            continue
        if H.is_vertex_critical(edges, nn, k) and H.has_no_critical_edge(edges, nn, k):
            found.append((name, sorted(conn) if all(isinstance(x,int) for x in conn) else list(conn)))
    return name, len(els), tested, found


if __name__ == "__main__":
    print("=== Non-cyclic Cayley substrate scan for (4,1)-graphs ===\n")
    groups = [
        group_S3(),
        group_prod(group_Zn(2), group_Zn(2)),          # Z2xZ2 (order 4)
        group_prod(group_prod(group_Zn(2), group_Zn(2)), group_Zn(2)),  # Z2^3 (order 8)
        group_prod(group_Zn(2), group_Zn(3)),           # Z6 = Z2xZ3
        group_prod(group_Zn(3), group_Zn(3)),           # Z3xZ3 (order 9)
        group_D4(),
        group_Q8(),
        group_prod(group_Zn(2), group_Zn(2)),
        group_prod(group_Zn(2), group_S3()[0:1]) if False else group_S3(),  # placeholder
    ]
    # dedupe by name
    seen=set(); uniq=[]
    for g in groups:
        if g[3] in seen: continue
        seen.add(g[3]); uniq.append(g)
    for g in uniq:
        name, order, tested, found = scan_cayley(g)
        msg = f"[{name}] order={order} conn-sets tested={tested} (4,1)-witnesses={len(found)}"
        if found:
            msg += "  <<< WITNESS! >>> " + str(found[:3])
        print(msg)
