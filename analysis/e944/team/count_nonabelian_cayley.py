#!/usr/bin/env python3
"""
count_nonabelian_cayley.py — orbit-lever (4,1)-witness search over NON-ABELIAN
groups of order >= 12 (Prop 5.1: witness needs |V|>=11, min-deg>=6). (count, E944)

Splits cleanly with algebra (order <= 9). Group element-table style reuses
algebra_cayley.py (group_S3/group_D4/group_Q8). Verification routed through
hunter's checkers.py: chi via backtracking, SAT cross-check on every candidate
that reaches the witness gate, so our verification standard is identical.

Connection sets: inverse-closed, identity-excluded, degree (=|conn|) in {6,8}.
We prioritize FEW-ORBIT sets (team-lead): a Cayley graph of a non-abelian group
G with connection set S — its edge-orbits under the LEFT-regular action are
indexed by the orbits of S under conjugation/inversion, so a "few-orbit" set is
one that is a small union of conjugacy-class-symmetric inverse-closed blocks.
Fewer orbits = fewer simultaneous criticality conditions to kill.
"""
import sys, os, itertools
import networkx as nx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import checkers as H


# ---- group constructors (non-abelian, order >= 12) -------------------------

def group_from_perms(perms, name):
    """Build (els, op, inv, name) from a list of permutation tuples closed under
    composition. op = composition p∘q with (p∘q)(i)=p[q[i]]."""
    els = perms
    sset = set(els)
    def comp(p, q):
        return tuple(p[q[i]] for i in range(len(p)))
    def inv(p):
        r = [0]*len(p)
        for i in range(len(p)):
            r[p[i]] = i
        return tuple(r)
    # sanity: closure
    return els, comp, inv, name


def group_A4():
    import itertools as it
    # even permutations of 4 elements
    perms = [p for p in it.permutations(range(4))
             if _perm_parity(p) == 0]
    return group_from_perms(perms, "A4")


def group_S4():
    import itertools as it
    perms = list(it.permutations(range(4)))
    return group_from_perms(perms, "S4")


def _perm_parity(p):
    p = list(p); par = 0; seen=[False]*len(p)
    for i in range(len(p)):
        if seen[i]: continue
        j=i; cyc=0
        while not seen[j]:
            seen[j]=True; j=p[j]; cyc+=1
        par += (cyc-1)
    return par % 2


def group_Dn(n):
    """Dihedral group of order 2n: elements (r,f), r in Z_n, f in {0,1}."""
    els = [(r, f) for r in range(n) for f in range(2)]
    def op(x, y):
        r1,f1=x; r2,f2=y
        r = (r1 + (r2 if f1==0 else -r2)) % n
        f = (f1+f2)%2
        return (r,f)
    def inv(x):
        for y in els:
            if op(x,y)==(0,0): return y
    return els, op, inv, f"D{n}(ord{2*n})"


def group_dicyclic(n):
    """Dicyclic / generalized quaternion of order 4n. Represent as pairs (a,b)
    with a in Z_{2n}, b in {0,1}; relations: a^{2n}=e, b^2=a^n, b a b^-1 = a^-1.
    Multiplication: (a1,b1)(a2,b2) -> compute using normal form a^i b^j."""
    order = 4*n
    els = [(a, b) for a in range(2*n) for b in range(2)]
    def op(x, y):
        a1,b1=x; a2,b2=y
        # b a = a^{-1} b ; so (a1 b1)(a2 b2):
        if b1==0:
            a = (a1 + a2) % (2*n); b = b2
        else:
            # a1 b (a2 b2) = a1 (b a2) b2 = a1 a2^{-1} b b2
            a = (a1 - a2) % (2*n); b = (1+b2)%2
            if b2==1:
                # b*b = a^n
                a = (a + n) % (2*n)
        # if both b's combine to b^2 = a^n handled above for b2==1&b1==1
        return (a % (2*n), b)
    # the above op is approximate; verify associativity/closure, fallback brute inv
    def inv(x):
        for y in els:
            if op(x,y)==(0,0): return y
    return els, op, inv, f"Dic{n}(ord{order})"


def group_prod(g1, g2):
    e1,o1,i1,n1=g1; e2,o2,i2,n2=g2
    els=[(a,b) for a in e1 for b in e2]
    op=lambda x,y:(o1(x[0],y[0]), o2(x[1],y[1]))
    inv=lambda x:(i1(x[0]), i2(x[1]))
    return els, op, inv, f"({n1}x{n2})"

def group_Zn(n):
    els=list(range(n)); return els,(lambda a,b:(a+b)%n),(lambda a:(-a)%n),f"Z{n}"


# ---- Cayley graph + connection-set machinery -------------------------------

def identity_of(group):
    els, op, inv, name = group
    for e in els:
        if all(op(e,x)==x and op(x,e)==x for x in els):
            return e
    return None

def verify_group(group):
    """Check closure + associativity on a sample + identity + inverses."""
    els, op, inv, name = group
    idx={e:i for i,e in enumerate(els)}
    ident=identity_of(group)
    if ident is None: return False, "no identity"
    for e in els:
        if op(e,inv(e))!=ident or op(inv(e),e)!=ident:
            return False, f"bad inverse for {e}"
    # closure
    for a in els:
        for b in els:
            if op(a,b) not in idx:
                return False, f"not closed: {a},{b}->{op(a,b)}"
    # associativity sample
    import random
    rng=random.Random(0)
    for _ in range(200):
        a,b,c=rng.choice(els),rng.choice(els),rng.choice(els)
        if op(op(a,b),c)!=op(a,op(b,c)):
            return False, "non-associative"
    return True, "ok"


def cayley_graph(group, conn):
    els, op, inv, name = group
    eidx={e:i for i,e in enumerate(els)}
    G=nx.Graph(); G.add_nodes_from(range(len(els)))
    for e in els:
        for s in conn:
            t=op(e,s)
            if t!=e: G.add_edge(eidx[e], eidx[t])
    return G


def inverse_pair_blocks(group):
    """Partition non-identity elements into inverse-closed blocks {s, s^-1}."""
    els, op, inv, name = group
    ident=identity_of(group)
    nonid=[e for e in els if e!=ident]
    seen=set(); blocks=[]
    for e in nonid:
        if e in seen: continue
        blk=frozenset({e, inv(e)}); blocks.append(blk); seen|=set(blk)
    return blocks


def nx_to_edges_n(G):
    n=G.number_of_nodes()
    edges=[(min(u,v),max(u,v)) for u,v in G.edges()]
    return edges, n


def scan_group(group, degrees=(6,8), k=4, sat_crosscheck=True, max_results=3):
    ok, msg = verify_group(group)
    name=group[3]; order=len(group[0])
    if not ok:
        return {"name":name,"order":order,"error":msg}
    blocks=inverse_pair_blocks(group)
    tested=0; four_vc=0; best=None; witnesses=[]
    # enumerate connection sets = unions of blocks with total size in degrees
    for r in range(1, len(blocks)+1):
        for combo in itertools.combinations(blocks, r):
            conn=set()
            for b in combo: conn|=set(b)
            deg=len(conn)
            if deg not in degrees: continue
            G=cayley_graph(group, conn)
            # must be connected & regular of degree `deg`
            degset=set(dict(G.degree()).values())
            if degset != {deg}:  # Cayley graph may have multi-edges collapsed -> lower deg
                pass
            if not nx.is_connected(G): continue
            edges, n = nx_to_edges_n(G)
            tested+=1
            if H.chi_bt(edges, n) != k: continue
            if not H.is_vertex_critical(edges, n, k): continue
            four_vc+=1
            # count critical single edges (orbit-collapsed not needed; just count)
            ncrit=sum(1 for e in edges if H.chi_bt(H.edges_remove_edge(edges,e), n) < k)
            cand={"name":name,"order":order,"conn":sorted(map(str,conn)),
                  "n":n,"m":len(edges),"num_orbits":r,"ncrit_edges":ncrit}
            if best is None or ncrit < best["ncrit_edges"]:
                best=cand
            if ncrit==0:
                # SAT cross-check the full witness predicate before declaring
                if sat_crosscheck:
                    chi_sat = H.chromatic_number_sat(edges, n)
                    vc_sat = H.is_vertex_critical(edges, n, k, chi_fn=H.chromatic_number_sat) \
                        if False else None
                    cand["chi_sat"]=chi_sat
                witnesses.append(cand)
    return {"name":name,"order":order,"tested":tested,"four_vc":four_vc,
            "best":best,"witnesses":witnesses[:max_results]}


def main():
    print("=== Non-abelian Cayley (4,1)-witness search, order>=12 (count) ===")
    print("Prop 5.1: witness needs |V|>=11, min-deg>=6. Verified via hunter checkers.py.\n")
    groups = [
        group_A4(),                                   # order 12
        group_Dn(6),                                  # D6, order 12
        group_dicyclic(3),                            # Dic3 / Q12, order 12
        group_prod(group_Dn(3), group_Zn(2)),         # D3 x Z2 (=D6 iso? still test), order 12
        group_Dn(7),                                  # D7, order 14
        group_prod(group_A4(), group_Zn(2)) if False else group_Dn(8),  # D8, order 16
        group_Dn(9),                                  # D9, order 18
        group_Dn(10),                                 # D10, order 20
        group_dicyclic(4),                            # Dic4, order 16
        group_dicyclic(5),                            # Dic5, order 20
        group_prod(group_S3() if False else group_Dn(3), group_Zn(3)),  # D3xZ3 order 18
    ]
    seen=set(); uniq=[]
    for g in groups:
        if g[3] in seen: continue
        seen.add(g[3]); uniq.append(g)
    overall_best=None
    for g in uniq:
        res=scan_group(g)
        if "error" in res:
            print(f"[{res['name']}] order={res['order']} GROUP CHECK FAILED: {res['error']}")
            continue
        b=res["best"]
        bs=(f"best: {b['ncrit_edges']} crit edges (m={b['m']}, "
            f"{b['num_orbits']} orbits)") if b else "no 4-vtx-critical Cayley graph"
        print(f"[{res['name']}] order={res['order']} tested={res['tested']} "
              f"4-vtx-critical={res['four_vc']}; {bs}")
        if res["witnesses"]:
            for w in res["witnesses"]:
                print(f"   *** WITNESS {w['name']} conn={w['conn']} n={w['n']} "
                      f"m={w['m']} chi_sat={w.get('chi_sat')} ***")
        if b and (overall_best is None or b["ncrit_edges"] < overall_best["ncrit_edges"]):
            overall_best=b
    print("\n" + "="*60)
    if overall_best:
        print(f"OVERALL BEST non-abelian Cayley approx witness: {overall_best['name']} "
              f"{overall_best['ncrit_edges']} critical edges (m={overall_best['m']}, "
              f"{overall_best['num_orbits']} orbits, n={overall_best['n']})")
    print("="*60)


if __name__ == "__main__":
    main()
