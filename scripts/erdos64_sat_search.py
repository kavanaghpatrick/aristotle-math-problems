#!/usr/bin/env python3
"""
Erdős 64 (Erdős-Gyárfás 1995) external SAT / extremal search.

Conjecture: every finite graph with minimum degree ≥ 3 contains a cycle of
length 2^k for some k ≥ 2. (i.e., a 4-cycle, 8-cycle, 16-cycle, 32-cycle, ...)

A COUNTEREXAMPLE is a graph G with:
  (a) minimum degree ≥ 3
  (b) no cycle of length in {4, 8, 16, 32, ..., 2^k ≤ n}.

Known constraints (literature freshness May 30 2026):
  - Counterexample, if exists, must have > 17 vertices (small cases verified).
  - Hu-Shen 2024: no min-deg-3 P_10-free counterexample.
  - Hegde-Sandeep-Shashank Feb 2025: P_13-free strengthening.
  - Cubic counterexample (3-regular) must have > 30 vertices.
  - Bipartite counterexample must have > 32 vertices.

This script searches the regime n ∈ {18, ..., 25} (where 2^k ∈ {4, 8, 16}
are the only relevant powers for cycle absence).

STRATEGY:
We focus on a structural restriction that keeps search tractable:
  - 3-regular and (3,4)-mixed-degree graphs only (relaxing increases search blowup).
  - For n ≤ 25, the relevant forbidden cycle lengths are {4, 8, 16}. (A 32-cycle
    requires n ≥ 32, so is automatically absent for n ≤ 31.)
  - For each n, enumerate non-isomorphic candidate 3-regular graphs (via
    networkx graph6 generation if available; otherwise sample random 3-regular
    via networkx.random_regular_graph). Filter for no 4/8/16-cycle.

OUTPUT: analysis/erdos64_search_results.json with the FIRST counterexample
found (if any), plus metadata about the search bound reached.
"""

import json
import time
import random
from pathlib import Path
from itertools import combinations
import networkx as nx

OUTPUT = Path(__file__).resolve().parent.parent / "analysis" / "erdos64_search_results.json"


def has_cycle_of_length(G: nx.Graph, k: int) -> bool:
    """True iff G has a simple cycle of length exactly k.

    Uses brute-force enumeration of k-paths from each vertex and checks
    closure. For small n and k this is fast enough.

    For length 4 we use a closed-form: count common neighbours of every
    non-adjacent pair (well, the standard C_4 detection is to count for each
    pair u,v the number of common neighbours; if any pair has ≥ 2 common
    neighbours, there's a 4-cycle).
    """
    n = G.number_of_nodes()
    if k > n:
        return False
    if k == 4:
        nodes = list(G.nodes())
        for i in range(len(nodes)):
            for j in range(i + 1, len(nodes)):
                u, v = nodes[i], nodes[j]
                # common neighbours of u,v
                common = set(G.neighbors(u)) & set(G.neighbors(v))
                if len(common) >= 2:
                    # if u,v themselves form an edge, the 4-cycle is u-w-v-x-u with w,x ∈ common
                    # if u,v are not adjacent, same thing: a 4-cycle u-w-v-x-u
                    return True
        return False

    # General case: DFS with depth ≤ k, return True on first cycle of exact length k.
    for start in G.nodes():
        # DFS: stack of (current_vertex, path_set, path_list)
        stack = [(start, {start}, [start])]
        while stack:
            v, seen, path = stack.pop()
            if len(path) == k:
                # closure must be back to start
                if G.has_edge(v, start):
                    return True
                continue
            for w in G.neighbors(v):
                if w == start and len(path) == k:
                    return True
                if w in seen:
                    continue
                # quick lex-order constraint: require second vertex ≥ start to halve search
                # (we'll skip this since we accept any cycle existence)
                stack.append((w, seen | {w}, path + [w]))
    return False


def has_any_forbidden_cycle(G: nx.Graph, forbidden: list[int]) -> bool:
    """True iff G has a cycle of any length in `forbidden`."""
    for k in forbidden:
        if has_cycle_of_length(G, k):
            return True
    return False


def forbidden_lengths_for_n(n: int) -> list[int]:
    """Powers of 2 (≥ 4) that are ≤ n."""
    lens = []
    p = 4
    while p <= n:
        lens.append(p)
        p *= 2
    return lens


def random_cubic_graph(n: int, rng: random.Random) -> nx.Graph | None:
    """networkx.random_regular_graph wrapped with seed.

    Returns None for odd n (no 3-regular graph exists).
    """
    if (n * 3) % 2 != 0:
        return None
    try:
        seed = rng.randrange(2**31)
        return nx.random_regular_graph(3, n, seed=seed)
    except (nx.NetworkXError, Exception):
        return None


def random_mindeg3_graph(n: int, m: int, rng: random.Random) -> nx.Graph:
    """Random graph with n vertices, m edges, then REPAIR to min-degree ≥ 3.

    Repair: while any vertex has degree < 3, add an edge between two
    minimum-degree vertices that are not already adjacent.

    Returns the repaired graph (always min-deg ≥ 3 if feasible).
    """
    seed = rng.randrange(2**31)
    G = nx.gnm_random_graph(n, m, seed=seed)
    # Repair: ensure min-degree ≥ 3
    max_repair = 50
    for _ in range(max_repair):
        degs = dict(G.degree())
        low = [v for v, d in degs.items() if d < 3]
        if not low:
            break
        # Sort low-degree vertices and try to connect them to a different low-degree
        # or smallest-degree vertex.
        rng.shuffle(low)
        added = False
        for u in low:
            # candidates: other vertices not adjacent to u and not u itself
            cands = [v for v in G.nodes() if v != u and not G.has_edge(u, v)]
            if not cands:
                continue
            # Prefer connecting low-degree vertices first
            cands.sort(key=lambda v: degs.get(v, 0))
            v = cands[0]
            G.add_edge(u, v)
            added = True
            break
        if not added:
            break
    return G


def remove_4cycle_swap(G: nx.Graph, rng: random.Random) -> bool:
    """Try a single 2-swap (edge rewiring) that removes some 4-cycle.

    Strategy: find a vertex pair (u,v) with ≥ 2 common neighbours w1, w2
    (i.e. they form 4-cycle u-w1-v-w2-u). Then try to remove edge u-w1 and add
    a new edge u-x for some x not currently a neighbour of u and such that
    u-x doesn't create a new 4-cycle with x and that the resulting min-deg is
    still ≥ 3.

    Returns True if a swap was performed.
    """
    n = G.number_of_nodes()
    nodes = list(G.nodes())
    rng.shuffle(nodes)
    for i in range(len(nodes)):
        u = nodes[i]
        for j in range(len(nodes)):
            if i == j:
                continue
            v = nodes[j]
            common = list(set(G.neighbors(u)) & set(G.neighbors(v)))
            if len(common) < 2:
                continue
            # Pick a w in common to break u-w
            rng.shuffle(common)
            for w in common:
                # Need degrees stay ≥ 3 after removing u-w
                if G.degree(u) <= 3 or G.degree(w) <= 3:
                    continue
                # Try to add a new edge u-x not currently in G, x ≠ u,
                # such that adding u-x doesn't create another 4-cycle.
                # Simple heuristic: any x not adjacent to u.
                cands = [x for x in nodes if x != u and not G.has_edge(u, x)]
                rng.shuffle(cands)
                for x in cands:
                    # Check no new 4-cycle (no common-neighbour pair of u,x with ≥ 2)
                    # Tentative add
                    G.add_edge(u, x)
                    G.remove_edge(u, w)
                    # Check 4-cycle on the new edge u-x
                    new_common = set(G.neighbors(u)) & set(G.neighbors(x))
                    if len(new_common) >= 2:
                        # Revert
                        G.add_edge(u, w)
                        G.remove_edge(u, x)
                        continue
                    return True
            # done attempting w
    return False


def repair_phase(G: nx.Graph, rng: random.Random, max_swaps: int = 200) -> nx.Graph:
    """Iteratively remove 4-cycles via 2-swaps."""
    for _ in range(max_swaps):
        if not has_cycle_of_length(G, 4):
            break
        if not remove_4cycle_swap(G, rng):
            break
    return G


def graph_to_adj_list(G: nx.Graph) -> list[list[int]]:
    """Return adjacency list with vertices canonically labelled 0..n-1."""
    nodes = sorted(G.nodes())
    relabel = {v: i for i, v in enumerate(nodes)}
    out = []
    for v in nodes:
        nbrs = sorted(relabel[w] for w in G.neighbors(v))
        out.append(nbrs)
    return out


def verify_candidate(G: nx.Graph, n: int) -> dict:
    """Re-verify all the counterexample properties from scratch."""
    forbidden = forbidden_lengths_for_n(n)
    degrees = dict(G.degree())
    min_deg = min(degrees.values()) if degrees else 0
    has_forbidden = {}
    for k in forbidden:
        has_forbidden[k] = has_cycle_of_length(G, k)
    return {
        "n": n,
        "edges": G.number_of_edges(),
        "min_degree": min_deg,
        "max_degree": max(degrees.values()) if degrees else 0,
        "forbidden_lengths": forbidden,
        "has_cycle_of": has_forbidden,
        "is_counterexample": (min_deg >= 3) and not any(has_forbidden.values()),
        "adjacency": graph_to_adj_list(G),
    }


def search_cubic(n: int, max_trials: int, time_budget_s: float, rng: random.Random) -> dict | None:
    """Search random 3-regular graphs on n vertices.

    Returns dict with witness if found, else None. Random 3-regular graphs on
    n vertices have ~3n/2 edges; for n=18 that's 27 edges. 4-cycles are common
    here so most trials will be rejected immediately.
    """
    forbidden = forbidden_lengths_for_n(n)
    start = time.time()
    trials = 0
    rejected_by = {k: 0 for k in forbidden}
    while trials < max_trials and (time.time() - start) < time_budget_s:
        trials += 1
        G = random_cubic_graph(n, rng)
        if G is None:
            continue
        # Quick min-degree check (random_regular_graph should guarantee 3-regular)
        if min(d for _, d in G.degree()) < 3:
            continue
        # Test forbidden cycles in increasing order (short cycles cheaper to test)
        rejected = False
        for k in forbidden:
            if has_cycle_of_length(G, k):
                rejected_by[k] += 1
                rejected = True
                break
        if not rejected:
            return {
                "found": True,
                "n": n,
                "trials": trials,
                "elapsed_s": round(time.time() - start, 2),
                "witness": verify_candidate(G, n),
            }
    return {
        "found": False,
        "n": n,
        "trials": trials,
        "elapsed_s": round(time.time() - start, 2),
        "rejected_by_cycle_length": rejected_by,
    }


def search_mindeg3(n: int, max_trials: int, time_budget_s: float, rng: random.Random,
                    m_range: tuple[int, int] | None = None) -> dict | None:
    """Search random graphs G(n, m) with various edge counts m.

    For min-deg-3 graphs, m ≥ 3n/2. We sample m ∈ [⌈3n/2⌉, 2n] to cover both
    cubic and slightly-denser cases. We accept the first candidate where:
      - min_degree ≥ 3
      - no cycle of length in {4, 8, 16, ...} (≤ n).
    """
    forbidden = forbidden_lengths_for_n(n)
    start = time.time()
    if m_range is None:
        m_lo = (3 * n + 1) // 2  # ⌈3n/2⌉
        m_hi = 2 * n
    else:
        m_lo, m_hi = m_range
    trials = 0
    accepted_mindeg = 0
    rejected_by = {k: 0 for k in forbidden}
    while trials < max_trials and (time.time() - start) < time_budget_s:
        trials += 1
        m = rng.randint(m_lo, m_hi)
        G = random_mindeg3_graph(n, m, rng)
        if not G.nodes:
            continue
        if min(d for _, d in G.degree()) < 3:
            continue
        accepted_mindeg += 1
        rejected = False
        for k in forbidden:
            if has_cycle_of_length(G, k):
                rejected_by[k] += 1
                rejected = True
                break
        if not rejected:
            return {
                "found": True,
                "n": n,
                "trials": trials,
                "mindeg3_accepted": accepted_mindeg,
                "elapsed_s": round(time.time() - start, 2),
                "witness": verify_candidate(G, n),
            }
    return {
        "found": False,
        "n": n,
        "trials": trials,
        "mindeg3_accepted": accepted_mindeg,
        "elapsed_s": round(time.time() - start, 2),
        "rejected_by_cycle_length": rejected_by,
    }


def main() -> None:
    print("Erdős 64 (Erdős-Gyárfás 2^k cycles disproof) — external SAT search")
    print("=" * 70)

    rng = random.Random(42)  # reproducibility
    results: dict = {
        "conjecture": "Every finite graph with min-degree >= 3 contains a cycle of length 2^k for some k >= 2.",
        "search_target": "counterexample with min-degree >= 3 and no cycle of length 2^k (k >= 2)",
        "started_at": time.strftime("%Y-%m-%d %H:%M:%S"),
        "search_log": [],
        "found_witness": None,
        "search_bound_reached": None,
    }

    overall_start = time.time()
    overall_budget_s = 9 * 60  # leave buffer under the 10-min cap

    # PHASE 1: Cubic (3-regular) search for n ∈ {18,..,25}.
    # Note: literature says cubic counterexample needs > 30 vertices, so we expect
    # to find nothing here; this is a sanity check confirming the literature
    # bound and demonstrating the search machinery works.
    cubic_trials_per_n = 4000
    print("\nPHASE 1 — random 3-regular graphs on n ∈ {18,...,25} (sanity check vs Hu-Shen 2024)")
    print("-" * 70)
    for n in range(18, 26):
        elapsed = time.time() - overall_start
        remaining = overall_budget_s - elapsed
        if remaining <= 10:
            break
        budget = min(45.0, remaining * 0.4)
        print(f"  n={n} forbidden cycles={forbidden_lengths_for_n(n)} budget={budget:.0f}s")
        r = search_cubic(n, max_trials=cubic_trials_per_n,
                         time_budget_s=budget, rng=rng)
        r["phase"] = "cubic"
        results["search_log"].append(r)
        print(f"    trials={r['trials']} found={r['found']} rejected_by={r.get('rejected_by_cycle_length')}")
        if r.get("found"):
            results["found_witness"] = r["witness"]
            results["search_bound_reached"] = n
            print(f"  >>> COUNTEREXAMPLE FOUND at n={n}!")
            break

    # PHASE 2: General min-degree-3 graphs, denser samples (m up to 2.2n).
    if results["found_witness"] is None:
        print("\nPHASE 2 — random min-deg-3 graphs on n ∈ {18,...,25}, m ∈ [⌈3n/2⌉, 2n]")
        print("-" * 70)
        mindeg_trials_per_n = 6000
        for n in range(18, 26):
            elapsed = time.time() - overall_start
            remaining = overall_budget_s - elapsed
            if remaining <= 10:
                break
            budget = min(60.0, remaining * 0.45)
            print(f"  n={n} forbidden cycles={forbidden_lengths_for_n(n)} budget={budget:.0f}s")
            r = search_mindeg3(n, max_trials=mindeg_trials_per_n,
                               time_budget_s=budget, rng=rng)
            r["phase"] = "mindeg3"
            results["search_log"].append(r)
            print(f"    trials={r['trials']} mindeg3_accepted={r.get('mindeg3_accepted')} found={r['found']} rejected_by={r.get('rejected_by_cycle_length')}")
            if r.get("found"):
                results["found_witness"] = r["witness"]
                results["search_bound_reached"] = n
                print(f"  >>> COUNTEREXAMPLE FOUND at n={n}!")
                break

    # PHASE 3: Sparse-but-min-deg-3 graphs with slightly higher edge counts.
    # The literature says cubic counterexample needs > 30 vertices, but mixed
    # degree (min 3, average 3.3-3.5) might have counterexample at smaller n
    # (this is the regime where Hu-Shen's P_10-free restriction does NOT apply).
    # NOTE: random_regular_graph(3, n) only works for even n; for odd n we test
    # nearby even n + augmented edges.
    if results["found_witness"] is None:
        print("\nPHASE 3 — extra-mixed-degree min-deg-3 graphs, m ∈ [2n, 2.5n]")
        print("-" * 70)
        for n in range(18, 26):
            elapsed = time.time() - overall_start
            remaining = overall_budget_s - elapsed
            if remaining <= 10:
                break
            budget = min(45.0, remaining * 0.5)
            m_lo = 2 * n
            m_hi = int(2.5 * n)
            print(f"  n={n} m∈[{m_lo},{m_hi}] budget={budget:.0f}s")
            r = search_mindeg3(n, max_trials=4000, time_budget_s=budget,
                               rng=rng, m_range=(m_lo, m_hi))
            r["phase"] = "mindeg3_dense"
            results["search_log"].append(r)
            print(f"    trials={r['trials']} found={r['found']} rejected_by={r.get('rejected_by_cycle_length')}")
            if r.get("found"):
                results["found_witness"] = r["witness"]
                results["search_bound_reached"] = n
                print(f"  >>> COUNTEREXAMPLE FOUND at n={n}!")
                break

    # PHASE 4: Hill-climbing 4-cycle removal on cubic graphs.
    # Start from random 3-regular graph, then iteratively swap edges to remove
    # 4-cycles. If we converge to a graph with no 4-cycle, check for 8-cycle and
    # 16-cycle.
    if results["found_witness"] is None:
        # Extend to n ∈ {26, 28, 30, 32} since literature says cubic >30 is required
        # — push hill-climbing into that regime where a counterexample is most likely.
        # Note that the 8-cycle constraint at n=30,32 with 4-cycle absent is the
        # crux: known mathematical bounds say no cubic graph of girth ≥ 5 on n ≤ 30
        # avoids both 4 and 8 cycles (in fact, the Petersen graph at n=10 has girth 5
        # and 5-cycles, but 8-cycles too).
        print("\nPHASE 4 — hill-climbing 4-cycle removal on cubic graphs (n even, 18..32)")
        print("-" * 70)
        hc_trials_per_n = 200
        for n in range(18, 33, 2):  # even n only (cubic feasibility)
            elapsed = time.time() - overall_start
            remaining = overall_budget_s - elapsed
            if remaining <= 10:
                break
            budget = min(60.0, remaining * 0.4)
            print(f"  n={n} forbidden={forbidden_lengths_for_n(n)} budget={budget:.0f}s")
            start = time.time()
            trials = 0
            converged_to_4cycle_free = 0
            still_has_4cycle = 0
            rejected_by_8 = 0
            rejected_by_16 = 0
            witness_dict = None
            while trials < hc_trials_per_n and (time.time() - start) < budget:
                trials += 1
                G = random_cubic_graph(n, rng)
                if G is None:
                    continue
                G = repair_phase(G, rng, max_swaps=100)
                # Repair phase may have broken min-degree-3; re-check
                if min(d for _, d in G.degree()) < 3:
                    continue
                # Test for 4-cycle still present
                if has_cycle_of_length(G, 4):
                    still_has_4cycle += 1
                    continue
                converged_to_4cycle_free += 1
                # No 4-cycle — check 8- and 16-cycle
                has_any = False
                for k in [8, 16]:
                    if k > n:
                        continue
                    if has_cycle_of_length(G, k):
                        has_any = True
                        if k == 8:
                            rejected_by_8 += 1
                        else:
                            rejected_by_16 += 1
                        break
                if not has_any:
                    witness_dict = verify_candidate(G, n)
                    break
            r = {
                "phase": "hill_climbing",
                "n": n,
                "trials": trials,
                "elapsed_s": round(time.time() - start, 2),
                "converged_to_4cycle_free": converged_to_4cycle_free,
                "still_has_4cycle_after_repair": still_has_4cycle,
                "rejected_by_8_cycle": rejected_by_8,
                "rejected_by_16_cycle": rejected_by_16,
                "found": witness_dict is not None,
            }
            results["search_log"].append(r)
            print(f"    trials={trials} converged_4cycle_free={converged_to_4cycle_free} rejected_by_8={rejected_by_8} rejected_by_16={rejected_by_16}")
            if witness_dict and witness_dict["is_counterexample"]:
                results["found_witness"] = witness_dict
                results["search_bound_reached"] = n
                print(f"  >>> COUNTEREXAMPLE FOUND at n={n}!")
                break

    results["finished_at"] = time.strftime("%Y-%m-%d %H:%M:%S")
    results["total_elapsed_s"] = round(time.time() - overall_start, 2)
    if results["found_witness"] is None:
        # search_bound_reached = max n attempted
        try:
            results["search_bound_reached"] = max(r["n"] for r in results["search_log"])
        except ValueError:
            results["search_bound_reached"] = None
        results["honest_assessment"] = (
            "No counterexample found via random sampling. "
            "Random 3-regular graphs are dominated by 4-cycles at small n. "
            "Literature (Hu-Shen 2024, Hegde et al Feb 2025) requires cubic > 30, "
            "bipartite > 32 — random sampling at n ≤ 25 cannot reach this regime. "
            "A real CNF SAT encoding with a state-of-the-art solver (cadical/kissat) "
            "and a beefier machine is required to push n into the 28–40 range "
            "where a counterexample, if any, is most likely to live."
        )

    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    with open(OUTPUT, "w") as f:
        json.dump(results, f, indent=2)
    print()
    print(f"Saved: {OUTPUT}")
    print(f"Witness found: {results['found_witness'] is not None}")
    print(f"Search bound reached: {results['search_bound_reached']}")
    print(f"Total elapsed: {results['total_elapsed_s']}s")


if __name__ == "__main__":
    main()
