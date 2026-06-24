"""
e944 SEARCH INSTRUMENT — the squad's single witness-search tool at n >= 14.
Co-authored: proximity (architecture + sound pieces + verifier) & forge (constructions/seeds).

================================================================================================
DESIGN PRINCIPLE (first-class, load-bearing — read before modifying):

  The (4,1) property RESISTS LOCAL ENCODING because NON-CRITICALITY IS GLOBAL.

  An edge e is non-critical because deleting it leaves chi=4 due to coloring structure that can be
  ARBITRARILY FAR from e. There is NO cheap local certificate for "no critical edge" (proven: every
  local entanglement clause tried — >=2 common neighbors, >=2 edge-disjoint triangles, color-balanced
  neighborhoods — is UNSOUND, excludes real witnesses; see INVENTIONS.md soundness ledger. C14(1,2,5)
  has 28 non-critical edges with <2 common neighbors). Therefore:

  ==> ARCHITECTURE = GENERATE + GLOBAL-VERIFY, not constrain-and-solve.
      Monolithic witness-SAT does NOT scale (hunter: coloring-blocking non-convergence;
      proximity: graph-blocking enumeration count). Both dead at n>=13.

  The ONLY sound STATIC prefilters are degree/connectivity bounds:
    - min-degree >= 6, max-degree <= n-5         [Skottova-Steiner Prop 5.1, dual-verified]
    - edge-connectivity >= 6                       [Prop 5.1; 2-subset-boundary>=6 sound partial proxy]

  *** REGIME WARNING (hunter-measured, 2026-06-10) — prefilters are VACUOUS in the dense witness band.
  At n=13 |E|>=40 (the witness regime: dense delta>=6, well-connected), the lambda>=6 and
  2-set-boundary>=6 prefilters pass ~100% (20000-graph sample at |E|=41: 100% pass both) — the dense
  well-connected regime AUTOMATICALLY satisfies them, so they prune ~nothing while costing a networkx
  edge_connectivity call (~0.3ms/graph). Net: the instrument WITH prefilters is SLOWER (3033 graphs/s)
  than hunter's bare bitmask floor_worker (8800/s). ==> In the |E|>=40 dense regime, DROP the per-graph
  lambda prefilter (use prefilter_connectivity=False) and use hunter's floor_worker as the verify
  backend. The prefilters earn their keep only in SPARSER regimes / other n where low-connectivity
  graphs actually appear. And NO prefilter that passes ~100% reduces the real wall = the raw graph
  COUNT at n=13 |E|>=41 (hundreds of millions); no per-graph speedup or prefilter touches that.

  Everything else (vertex-criticality, no-critical-edge) is checked GLOBALLY per candidate (no local
  certificate exists). For SCANNING throughput use hunter's bitmask floor_worker; the incremental
  verifier here is the INDEPENDENT GATE instrument (encoding diversity), NOT the fast scan backend.

================================================================================================
USAGE:
  scan_geng(n, edge_lo, edge_hi, degree_profile=None)  # exhaustive-ish generation via nauty geng
  verify_candidate(edges, n)                           # the global (4,1) check (incremental verifier)
  Any 0-critical-edge hit is dual-verified (checkers backtrack+SAT) AND must pass
  skeptic_adjudicate.py before alerting team-lead (squad protocol).
"""
import sys, os, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
import checkers as C
from proximity_incremental_verifier import IncrementalWitnessVerifier

GENG = "/opt/homebrew/Cellar/nauty/2.9.3/bin/geng"


# ---------------------------------------------------------------------------
# SOUND static prefilters (Prop 5.1) — applied at generation, cheap
# ---------------------------------------------------------------------------

def passes_prop51_degree(G, n):
    """min-degree >= 6 AND max-degree <= n-5. Necessary (Prop 5.1)."""
    degs = [d for _, d in G.degree()]
    return min(degs) >= 6 and max(degs) <= n - 5


def passes_2set_boundary(G, n):
    """Sound PARTIAL edge-connectivity proxy: every 2-vertex subset has boundary >= 6.
    Cheap O(n^2) check; full lambda>=6 verified separately. (proximity, validated sound)."""
    adj = {v: set(G.neighbors(v)) for v in range(n)}
    for a in range(n):
        for b in range(a + 1, n):
            # edges leaving {a,b} = |N(a)\{b}| + |N(b)\{a}| - 2*|common, both counted| ... count directly
            boundary = len(adj[a] - {b}) + len(adj[b] - {a})
            # common neighbors are counted twice (correctly: each contributes 2 boundary edges)
            if boundary < 6:
                return False
    return True


def passes_edge_connectivity_6(G):
    """Full lambda >= 6 (networkx). Necessary (Prop 5.1). Checked GLOBALLY, not encoded."""
    return nx.is_connected(G) and nx.edge_connectivity(G) >= 6


# ---------------------------------------------------------------------------
# GLOBAL verify — the (4,1) check (no local shortcut exists)
# ---------------------------------------------------------------------------

def verify_candidate(edges, n, dual_check=True):
    """GLOBAL (4,1) verification via the incremental verifier (ENC-2+ENC-6, CEGAR-free).
    Returns (is_witness, detail). dual_check re-confirms any positive with checkers (backtrack+SAT)."""
    v = IncrementalWitnessVerifier(edges, n)
    witness = v.is_witness()
    v.close()
    if witness and dual_check:
        # paranoid re-verify with the independent checkers (both chi paths)
        ok = (C.chi_bt(edges, n) == 4 and C.chromatic_number_sat(edges, n) == 4
              and C.is_vertex_critical(edges, n, 4) and C.has_no_critical_edge(edges, n, 4))
        return ok, ("WITNESS-DUAL-CONFIRMED" if ok else "verifier/checker MISMATCH — investigate")
    return witness, ("witness" if witness else "not a witness")


# ---------------------------------------------------------------------------
# GENERATE via geng (sound static prefilters applied), then GLOBAL verify
# ---------------------------------------------------------------------------

def scan_geng(n, edge_lo, edge_hi, degree_profile=None, res_mod=None, report_every=50000,
              prefilter_connectivity=False):
    """Generate connected min-deg-6 graphs (geng -c -d6 -D{n-5}) in the edge window, then GLOBAL-verify
    each. degree_profile (sorted list) optionally pins the exact degree multiset (ENC-8). res_mod = 'r/m'
    for parallel sharding.
    prefilter_connectivity (default FALSE): the 2-set-boundary + lambda>=6 prefilters are VACUOUS in the
    dense witness regime (n=13 |E|>=40, ~100% pass) and add networkx overhead with no pruning — so they
    are OFF by default. Set True ONLY for sparser regimes where low-connectivity graphs appear and the
    prefilter actually rejects some. geng -d6 already guarantees min-degree>=6; we keep the Prop-5.1
    max-degree<=n-5 check (cheap, sometimes prunes). Returns list of witnesses."""
    cmd = [GENG, "-c", "-d6", f"-D{n-5}", str(n), f"{edge_lo}:{edge_hi}"]
    if res_mod:
        cmd.append(res_mod)
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    total = passed_deg = passed_conn = chi4 = 0
    witnesses = []
    for raw in proc.stdout:
        total += 1
        G = nx.from_graph6_bytes(raw.strip())
        if degree_profile is not None and sorted(d for _, d in G.degree()) != degree_profile:
            continue
        if not passes_prop51_degree(G, n):
            continue
        passed_deg += 1
        if prefilter_connectivity:
            # vacuous in the dense |E|>=40 regime (hunter-measured ~100% pass); OFF by default
            if not passes_2set_boundary(G, n):
                continue
            if not passes_edge_connectivity_6(G):
                continue
        passed_conn += 1
        edges = [(min(u, v), max(u, v)) for u, v in G.edges()]
        # cheap chi gate before the full verify
        if C.chi_bt(edges, n) != 4:
            continue
        chi4 += 1
        ok, detail = verify_candidate(edges, n)
        if ok:
            g6 = raw.strip().decode()
            print(f"*** WITNESS at n={n}: g6={g6} edges={edges} ({detail}) ***")
            print(f"    NEXT: run skeptic_adjudicate.py --g6 '{g6}' then alert team-lead.")
            witnesses.append((g6, edges))
        if report_every and total % report_every == 0:
            print(f"  ...n={n}: {total} gen, {passed_deg} deg-ok, {passed_conn} conn-ok, "
                  f"{chi4} chi=4, {len(witnesses)} witnesses")
    proc.wait()
    print(f"n={n} [{edge_lo}:{edge_hi}] profile={degree_profile}: {total} generated, "
          f"{passed_conn} pass Prop-5.1, {chi4} chi=4, {len(witnesses)} witnesses")
    return witnesses


if __name__ == "__main__":
    # Self-test: the instrument must (a) verify known non-witnesses correctly, (b) run a small scan.
    def circ(nn, S):
        e = set()
        for i in range(nn):
            for d in S:
                j = (i + d) % nn
                e.add((min(i, j), max(i, j)))
        return sorted(e)
    print("SELF-TEST verify_candidate (must all be False = non-witness):")
    for nn, S in [(13, (1, 2, 5)), (14, (1, 2, 5)), (16, (1, 2, 5))]:
        g = circ(nn, S)
        ok, d = verify_candidate(g, nn)
        print(f"  C{nn}{S}: is_witness={ok} ({d})")
    print("\nSMOKE scan n=11 (must find 0; the Prop-5.1 class is exactly-6-regular, all non-vc):")
    scan_geng(11, 33, 33, report_every=100)
