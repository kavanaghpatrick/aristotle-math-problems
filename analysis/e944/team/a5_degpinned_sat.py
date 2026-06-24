"""
A5 (hunter round 2) — DEGREE-SEQUENCE-PINNED wiring SAT + CEGAR.

Round-1 SAT died from (a) cardinality blowup over FREE degrees and (b) the chi>=4 CEGAR stall. A5
tests whether PINNING the exact degree sequence d rescues it: degrees become hard constraints
(exactly deg[v] neighbors per v, via one cardinality-equality per vertex — still cardinality, but
the search space is collapsed), vertex-criticality baked as before, chi>=4 + no-critical-edge by
CEGAR. Targets the IRREGULAR witness regime round 1 identified.

This is a DIAGNOSTIC: if even degree-pinned SAT stalls in chi3-refine, the chi>=4 blowup is intrinsic
(not a degree-freedom artifact), confirming the SAT path is fundamentally wrong for this problem. If
it converges (UNSAT) on a slice enumeration can't reach (e.g. n=13 |E|=41 degree seqs), that's a real
extension.
"""
import sys, time, argparse
from pysat.solvers import Cadical195
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
sys.path.insert(0, "/Users/patrickkavanagh/math/analysis/e944/team")
from checkers import edges_to_adj, is_erdos944_k_r1, chi_bt
from existence_cegar import three_coloring


def run(n, degseq, budget_s, max_iters=500000):
    assert len(degseq) == n and sum(degseq) % 2 == 0
    vp = IDPool()
    pairs = [(i, j) for i in range(n) for j in range(i+1, n)]
    def e(i, j):
        a, b = (i, j) if i < j else (j, i); return vp.id(("e", a, b))
    def cV(v, u, c): return vp.id(("cV", v, u, c))
    S = Cadical195(); add = S.add_clause
    # baked vertex-criticality (3-coloring of every G-v)
    for v in range(n):
        for u in range(n):
            if u == v: continue
            add([cV(v,u,c) for c in range(3)])
            for c1 in range(3):
                for c2 in range(c1+1,3): add([-cV(v,u,c1),-cV(v,u,c2)])
        for (i,j) in pairs:
            if i==v or j==v: continue
            for c in range(3): add([-e(i,j),-cV(v,i,c),-cV(v,j,c)])
    # PIN degrees exactly: for each v, sum of incident edge vars == degseq[v]
    for v in range(n):
        lits = [e(v,w) for w in range(n) if w!=v]
        for cl in CardEnc.equals(lits=lits, bound=degseq[v], vpool=vp, encoding=EncType.seqcounter).clauses:
            add(cl)
    t0=time.time(); it=0
    while it < max_iters and time.time()-t0 < budget_s:
        it += 1
        if not S.solve(): S.delete(); return {"status":"UNSAT","iters":it,"elapsed":time.time()-t0}
        model=set(x for x in S.get_model() if x>0)
        edges=[(i,j) for (i,j) in pairs if e(i,j) in model]
        adj=edges_to_adj(edges,n)
        phi=three_coloring(adj,n)
        if phi is not None:
            mono=[(i,j) for (i,j) in pairs if phi[i]==phi[j] and e(i,j) not in model]
            add([e(i,j) for (i,j) in mono] if mono else [-e(*p) for p in pairs]); continue
        crit=None
        for (a,b) in edges:
            adj[a]&=~(1<<b); adj[b]&=~(1<<a)
            pe=three_coloring(adj,n)
            adj[a]|=(1<<b); adj[b]|=(1<<a)
            if pe is not None: crit=(a,b,pe); break
        if crit is None:
            ok=is_erdos944_k_r1(edges,n,4,chi_fn=chi_bt)
            S.delete(); return {"status":"WITNESS" if ok else "FALSE_CAND","edges":edges,"ok":ok,"iters":it}
        a,b,pe=crit
        mono=[(i,j) for (i,j) in pairs if pe[i]==pe[j] and not(i==a and j==b) and e(i,j) not in model]
        add([-e(a,b)]+[e(i,j) for (i,j) in mono])
    S.delete(); return {"status":"TIMEOUT/MAXITERS","iters":it,"elapsed":time.time()-t0}


if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--n",type=int,default=13)
    ap.add_argument("--degs",type=str,default="8,8,6,6,6,6,6,6,6,6,6,6,6",help="comma degree seq")
    ap.add_argument("--time",type=float,default=300)
    a=ap.parse_args()
    ds=[int(x) for x in a.degs.split(",")]
    print(f"# A5 degree-pinned SAT n={a.n} degseq={ds} sum={sum(ds)} |E|={sum(ds)//2} budget={a.time}s", flush=True)
    r=run(a.n, ds, a.time)
    print(f"# A5 RESULT: {r['status']} iters={r.get('iters')} elapsed={r.get('elapsed',0):.1f}s", flush=True)
    if r['status']=="WITNESS" and r['ok']:
        print(f"# WITNESS edges={r['edges']} — route through skeptic_adjudicate.py")
