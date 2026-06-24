#!/usr/bin/env python3
"""
bhk_engine.py — GPU-batched Björklund–Husfeldt–Koivisto inclusion–exclusion engine
for 3-colorability counting and the E944 (k=4, r=1) witness predicate.

Algorithm: Björklund, Husfeldt, Koivisto, "Set Partitioning via Inclusion–Exclusion",
SIAM J. Comput. 39(2):546-563, 2009.

Number of ways to (ordered-)cover V by 3 independent sets:
    c3(G) = sum_{S subset of V} (-1)^(n-|S|) * i(S)^3
where i(S) = number of independent sets that are subsets of S.
Then  chi(G) <= 3  <=>  c3(G) != 0  (a proper 3-coloring is an ordered cover of V by
3 independent sets, up to the standard surjectivity bookkeeping the IE sum performs).

The independent-set-count subset table i[.] obeys the DP (v = the highest set bit of S):
    i[S] = i[S \ {v}] + i[S \ N[v]]
with i[emptyset] = 1, where N[v] is the CLOSED neighborhood of v (v plus its neighbors).
We compute the whole i-table over all 2^n subsets, vectorized in bit-blocks: block b
covers subsets S in [2^b, 2^(b+1)); for those S, the highest bit is exactly b, so
    i[S] = i[S ^ (1<<b)]            (drop bit b: S \ {v})
         + i[(S ^ (1<<b)) & ~Nmask] (drop closed nbhd of b)
The two gather sources are already-finalized lower-index entries, so one vectorized
gather+add per block. n blocks total, 2^n gathered adds per graph.

ARITHMETIC: i(S) can be as large as 2^n, and i(S)^3 up to 2^(3n); the IE sum can be
astronomically large. We work modulo two ~31-bit primes; a count is declared ZERO only
if it is 0 modulo BOTH primes (false-zero probability ~ (1/p1)*(1/p2) ~ 1e-18). The GPU
is a SCREEN; any witness-shaped hit is re-verified by the exact CPU gate (checkers.py).

WITNESS PREDICATE (E944 k=4, r=1), all derived from c3 on subgraphs:
    chi >= 4                 <=>  c3(G) == 0
    chi == 4                 <=>  c3(G) == 0  AND  G is 4-colorable (checked on CPU at the gate;
                                  for the screen we treat c3(G)==0 as "chi>=4 candidate")
    v is vertex-critical     <=>  chi(G - v) <= 3  <=>  c3(G - v) != 0
    e is a critical edge     <=>  chi(G - e) <= 3  <=>  c3(G - e) != 0
    (4,1)-witness candidate  <=>  c3(G)==0  AND  for all v c3(G-v)!=0  AND  for all e c3(G-e)==0
                                  (4-vertex-critical with NO critical single edge)
    B1 (for diagnostics)     =  sum_e [c3-style proper-count of G-e] - m * (proper count of G);
                                here we report instead num_critical_edges directly, which is the
                                quantity the screen needs; B1 is computed by the 3^n oracle, not BHK.

Per-vertex c3(G - v): G - v is the induced subgraph on V \ {v}; its i-table is the
restriction of the SAME global i-table to subsets avoiding v, so c3(G-v) is a masked
re-sum over that sub-lattice — no new DP. Per-edge c3(G - e): independent-set counts
change (a previously-forbidden set becomes allowed), so we RERUN the DP on G - e (the
simplest correct thing; m extra DPs per graph, each 2^n — still cheap relative to the
search). A rank-correction shortcut exists but is only used if it validates against the
rerun.
"""
from __future__ import annotations

from typing import Dict, List, Optional, Sequence, Tuple

import torch

# Two ~31-bit primes (products of two such fit in int64 before reduction:
# (2^31)^2 ~ 4.6e18 < 9.2e18 = int64 max). i(S)^3 mod p computed as ((a*a)%p)*a%p.
P1 = 2_147_483_647        # 2^31 - 1 (Mersenne prime)
P2 = 2_147_483_629        # largest prime below 2^31-1 ... (a distinct ~31-bit prime)


def _device(device: Optional[str]) -> torch.device:
    if device is not None:
        return torch.device(device)
    return torch.device("mps") if torch.backends.mps.is_available() else torch.device("cpu")


def _closed_nbhd_masks(n: int, edges: Sequence[Tuple[int, int]]) -> List[int]:
    """N[v] closed-neighborhood bitmask for each v (includes v itself)."""
    nb = [1 << v for v in range(n)]
    for (a, b) in edges:
        nb[a] |= (1 << b)
        nb[b] |= (1 << a)
    return nb


def _indep_count_table(n: int, nbhd: List[int], p: int, dev: torch.device) -> torch.Tensor:
    """Return i[.] over all 2^n subsets, as int64 values mod p, on device.
    i[S] = i[S\\{v}] + i[S\\N[v]],  v = highest set bit of S,  i[0]=1."""
    size = 1 << n
    i = torch.zeros(size, dtype=torch.int64, device=dev)
    i[0] = 1 % p
    for v in range(n):
        bit = 1 << v
        lo, hi = bit, bit << 1            # block [2^v, 2^(v+1)) : highest bit == v
        S = torch.arange(lo, hi, dtype=torch.int64, device=dev)
        drop_v = S ^ bit                  # S \ {v}   (clears bit v) -> indices < lo
        drop_N = (S & ~nbhd[v])           # S \ N[v]  (clears v's closed nbhd) -> indices < lo
        i[lo:hi] = (i.gather(0, drop_v) + i.gather(0, drop_N)) % p
    return i


def _c3_from_itable(i_tab: torch.Tensor, n: int, p: int,
                    sign: torch.Tensor, popcount: torch.Tensor) -> int:
    """c3 = sum_S (-1)^(n-|S|) i(S)^3  (mod p).  sign[S] = (-1)^(n-|S|) in {+1,-1}."""
    cube = ((i_tab * i_tab) % p) * i_tab % p          # i(S)^3 mod p
    term = (cube * sign) % p                           # signed; sign is +-1
    s = term.sum() % p
    return int(s.item()) % p


def _indep_count_table_batch(n: int, nbhd_b: torch.Tensor, p: int,
                             dev: torch.device) -> torch.Tensor:
    """Batched i-table over a batch of graphs sharing vertex count n.

    nbhd_b: int64 [B, n] closed-neighborhood bitmasks (nbhd_b[g, v] = N[v] for graph g).
    Returns i: int64 [B, 2^n] mod p. The block recurrence is vectorized over both the
    batch and the block: for block v (subsets with highest bit v),
        i[:, S] = i[:, S^bit] + i[:, S & ~nbhd_b[:, v]]   (gather along the subset axis).
    `S^bit` is shared across graphs (a row index < lo), `S & ~N[v]` is per-graph."""
    B = nbhd_b.shape[0]
    size = 1 << n
    i = torch.zeros((B, size), dtype=torch.int64, device=dev)
    i[:, 0] = 1 % p
    for v in range(n):
        bit = 1 << v
        lo, hi = bit, bit << 1
        S = torch.arange(lo, hi, dtype=torch.int64, device=dev)       # [bs]
        drop_v = (S ^ bit).unsqueeze(0).expand(B, -1)                  # [B, bs] shared row
        # per-graph mask: S & ~N[v]  -> [B, bs]
        notN = (~nbhd_b[:, v]).unsqueeze(1)                            # [B, 1]
        drop_N = (S.unsqueeze(0) & notN)                              # [B, bs]
        block = (i.gather(1, drop_v) + i.gather(1, drop_N)) % p        # [B, bs]
        i[:, lo:hi] = block
    return i


def _c3_from_itable_batch(i_tab: torch.Tensor, p: int, sign: torch.Tensor) -> torch.Tensor:
    """Batched c3: i_tab [B, 2^n], sign [2^n] -> c3 [B] mod p (int64 on device)."""
    cube = ((i_tab * i_tab) % p) * i_tab % p
    term = (cube * sign.unsqueeze(0)) % p
    return term.sum(dim=1) % p


class BHKEngine:
    """Inclusion-exclusion 3-colorability engine for a fixed vertex count n.

    Per-n constants (sign vector, popcount) are built once and cached on device.
    """

    def __init__(self, n: int, device: Optional[str] = None):
        if n < 1 or n > 26:
            raise ValueError("n out of supported range [1,26]")
        self.n = n
        self.dev = _device(device)
        self.size = 1 << n
        # popcount and sign over all subsets (depends only on n)
        S = torch.arange(self.size, dtype=torch.int64, device=self.dev)
        pc = torch.zeros(self.size, dtype=torch.int64, device=self.dev)
        x = S.clone()
        for _ in range(n):
            pc += (x & 1)
            x >>= 1
        self.popcount = pc
        # sign[S] = (-1)^(n - |S|)
        parity = ((n - pc) & 1)
        self.sign = torch.where(parity == 0,
                                torch.ones(self.size, dtype=torch.int64, device=self.dev),
                                torch.full((self.size,), -1, dtype=torch.int64, device=self.dev))

    # ----------------------------------------------------------------- core counts
    def _c3_both(self, edges: Sequence[Tuple[int, int]], n: Optional[int] = None) -> Tuple[int, int]:
        """c3(G) mod P1 and mod P2 for a graph on `n` vertices (default self.n).
        For subgraphs on fewer vertices we re-use a fresh smaller engine path via
        an explicit n; here we keep n == self.n and pass induced edges (extra
        isolated vertices only scale nothing — c3 with an isolated vertex is 0 by
        IE? no: handled by callers using a dedicated sub-engine)."""
        nn = self.n if n is None else n
        nbhd = _closed_nbhd_masks(nn, edges)
        if nn == self.n:
            sign, pc = self.sign, self.popcount
        else:
            raise ValueError("use sub-engine for n != self.n")
        i1 = _indep_count_table(nn, nbhd, P1, self.dev)
        c1 = _c3_from_itable(i1, nn, P1, sign, pc)
        i2 = _indep_count_table(nn, nbhd, P2, self.dev)
        c2 = _c3_from_itable(i2, nn, P2, sign, pc)
        return c1, c2

    @staticmethod
    def _is_zero(c1: int, c2: int) -> bool:
        return c1 % P1 == 0 and c2 % P2 == 0

    # ----------------------------------------------------------------- public API
    def chi_le_3(self, edges: Sequence[Tuple[int, int]]) -> bool:
        """True iff G (on self.n vertices) is 3-colorable, by the IE screen."""
        c1, c2 = self._c3_both(self._norm(edges))
        return not self._is_zero(c1, c2)

    def _nbhd_batch_tensor(self, edge_lists: Sequence[Sequence[Tuple[int, int]]]) -> torch.Tensor:
        """Build int64 [B, n] closed-neighborhood masks for a batch of graphs."""
        B = len(edge_lists)
        nb = torch.zeros((B, self.n), dtype=torch.int64, device=self.dev)
        # seed diagonal (v in N[v]); build on host then move (n,B small relative to 2^n)
        host = [[1 << v for v in range(self.n)] for _ in range(B)]
        for g, edges in enumerate(edge_lists):
            for (a, b) in self._norm(edges):
                host[g][a] |= (1 << b)
                host[g][b] |= (1 << a)
        return torch.tensor(host, dtype=torch.int64, device=self.dev)

    def chi_le_3_batch(self, edge_lists: Sequence[Sequence[Tuple[int, int]]]) -> List[bool]:
        """Batched 3-colorability screen — the marathon hot path.

        Returns [B] bools (True = 3-colorable). One batched DP per modulus shared
        across the whole batch; the per-n sign vector is resident and reused. This
        is the PRIMARY API: a fixed-n candidate stream is screened in one GPU pass."""
        if not edge_lists:
            return []
        nb = self._nbhd_batch_tensor(edge_lists)
        i1 = _indep_count_table_batch(self.n, nb, P1, self.dev)
        c1 = _c3_from_itable_batch(i1, P1, self.sign)            # [B] mod P1
        i2 = _indep_count_table_batch(self.n, nb, P2, self.dev)
        c2 = _c3_from_itable_batch(i2, P2, self.sign)            # [B] mod P2
        z1 = (c1 % P1 == 0)
        z2 = (c2 % P2 == 0)
        is_zero = (z1 & z2).cpu().tolist()                       # chi>=4 iff both zero
        return [not z for z in is_zero]

    def analyze(self, edges: Sequence[Tuple[int, int]]) -> Dict:
        """Full witness-predicate analysis for the E944 (k=4,r=1) screen.

        Returns chi_le_3, plus per-vertex / per-edge 3-colorability flags (the
        criticality predicates) and the witness verdict. All quantities are the
        IE screen; the marathon re-verifies any witness candidate on the exact CPU
        gate. Output schema mirrors hunter's 3^n oracle for direct comparison.
        """
        n = self.n
        edges = self._norm(edges)
        m = len(edges)

        # c3(G)
        cG1, cG2 = self._c3_both(edges)
        g_3col = not self._is_zero(cG1, cG2)

        # per-vertex: c3(G - v) on the induced subgraph V\{v}. We relabel to n-1
        # vertices and use a sub-engine cached per (n-1).
        vert_3col: List[bool] = []
        for v in range(n):
            sub_edges, sub_n = self._induced_minus_vertex(edges, n, v)
            vert_3col.append(self._sub_3col(sub_edges, sub_n))

        # per-edge: c3(G - e), rerun DP on the same n vertices minus edge e.
        edge_3col: List[bool] = []
        for j in range(m):
            sub = [e for k, e in enumerate(edges) if k != j]
            c1, c2 = self._c3_both(sub)
            edge_3col.append(not self._is_zero(c1, c2))

        # E944 (4,1)-witness candidate: chi>=4 (not 3col) AND every vertex critical
        # (G-v IS 3col) AND no critical edge (no G-e is 3col).
        is_vertex_critical = (not g_3col) and all(vert_3col)
        no_critical_edge = not any(edge_3col)
        witness_candidate = (not g_3col) and is_vertex_critical and no_critical_edge

        return {
            "n": n,
            "m": m,
            "chi_le_3": g_3col,
            # match hunter's oracle field names where possible:
            "vertex_3col": vert_3col,           # G-v 3-colorable?  (== vertex critical when chi(G)=4)
            "edge_3col": edge_3col,             # G-e 3-colorable?  (== critical edge when chi(G)=4)
            "num_critical_vertices": int(sum(vert_3col)) if not g_3col else 0,
            "num_critical_edges": int(sum(edge_3col)) if not g_3col else 0,
            "is_vertex_critical": bool(is_vertex_critical),
            "no_critical_edge": bool(no_critical_edge),
            "witness_candidate": bool(witness_candidate),
        }

    def analyze_batch(self, edge_lists: Sequence[Sequence[Tuple[int, int]]],
                      full_on_chi4_only: bool = True) -> List[Dict]:
        """Batched witness-predicate analysis (the marathon's screen+gate driver).

        Strategy (the efficient path for a search stream):
          1. Batch-screen all graphs for chi<=3 in ONE GPU pass per modulus.
          2. Graphs that ARE 3-colorable are immediately rejected (cannot be a
             chi=4 witness) — no per-vertex/per-edge work.
          3. Only the chi>=4 candidates get the full per-vertex + per-edge analysis
             (the per-edge rerun-DPs and per-vertex sub-DPs).
        With `full_on_chi4_only=False` every graph gets the full analysis (used by
        the validation harness to exercise the criticality vectors on 3-colorable
        graphs too)."""
        norm = [self._norm(e) for e in edge_lists]
        screen = self.chi_le_3_batch(norm)         # [B] is-3-colorable
        out: List[Dict] = []
        for g_3col, edges in zip(screen, norm):
            if g_3col and full_on_chi4_only:
                m = len(edges)
                out.append({
                    "n": self.n, "m": m, "chi_le_3": True,
                    "vertex_3col": [True] * self.n, "edge_3col": [True] * m,
                    "num_critical_vertices": 0, "num_critical_edges": 0,
                    "is_vertex_critical": False, "no_critical_edge": (m == 0),
                    "witness_candidate": False,
                })
            else:
                out.append(self.analyze(edges))
        return out

    # ----------------------------------------------------------------- sub-engine cache
    _sub_cache: Dict[int, "BHKEngine"] = {}

    def _sub_engine(self, sub_n: int) -> "BHKEngine":
        if sub_n < 1:
            return None
        eng = BHKEngine._sub_cache.get((sub_n, str(self.dev)))
        if eng is None:
            eng = BHKEngine(sub_n, device=str(self.dev))
            BHKEngine._sub_cache[(sub_n, str(self.dev))] = eng
        return eng

    def _sub_3col(self, sub_edges, sub_n) -> bool:
        if sub_n == 0:
            return True
        eng = self._sub_engine(sub_n)
        c1, c2 = eng._c3_both(sub_edges)
        return not self._is_zero(c1, c2)

    # ----------------------------------------------------------------- helpers
    def _norm(self, edges: Sequence[Tuple[int, int]]) -> List[Tuple[int, int]]:
        seen = set()
        out = []
        for e in edges:
            a, b = int(e[0]), int(e[1])
            if a == b:
                continue
            if a > b:
                a, b = b, a
            if a < 0 or b >= self.n:
                raise ValueError(f"edge {(a,b)} out of range for n={self.n}")
            if (a, b) in seen:
                continue
            seen.add((a, b))
            out.append((a, b))
        return out

    @staticmethod
    def _induced_minus_vertex(edges, n, v) -> Tuple[List[Tuple[int, int]], int]:
        keep = [u for u in range(n) if u != v]
        relabel = {u: i for i, u in enumerate(keep)}
        sub = [(relabel[a], relabel[b]) for (a, b) in edges if a != v and b != v]
        return sub, n - 1


# convenience builders for fixtures -------------------------------------------------
def circulant_edges(n: int, conns: Sequence[int]) -> List[Tuple[int, int]]:
    E = set()
    for d in conns:
        for i in range(n):
            a, b = i, (i + d) % n
            if a != b:
                E.add((min(a, b), max(a, b)))
    return sorted(E)


def cocktail_party_edges(parts: int) -> Tuple[int, List[Tuple[int, int]]]:
    n = 2 * parts
    pair = {2 * i: 2 * i + 1 for i in range(parts)}
    pair.update({2 * i + 1: 2 * i for i in range(parts)})
    E = [(a, b) for a in range(n) for b in range(a + 1, n) if pair[a] != b]
    return n, E


if __name__ == "__main__":
    import sys
    dev = sys.argv[1] if len(sys.argv) > 1 else "mps"
    eng = BHKEngine(13, device=dev)
    r = eng.analyze(circulant_edges(13, [1, 2, 5]))
    print(f"C13(1,2,5) BHK on {dev}: chi_le_3={r['chi_le_3']} "
          f"critV={r['num_critical_vertices']} critE={r['num_critical_edges']} "
          f"vertex_critical={r['is_vertex_critical']} no_crit_edge={r['no_critical_edge']} "
          f"witness={r['witness_candidate']}")
