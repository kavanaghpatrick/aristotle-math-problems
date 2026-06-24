#!/usr/bin/env python3
"""
gpu_kernel.py — Metal-GPU (PyTorch MPS) exhaustive 3-coloring enumeration for the
E944 witness search.

For a graph G on n <= 16 vertices, enumerate ALL 3^n colorings on the GPU and
compute EXACTLY (no sampling, no approximation):

  - properCount : # colorings with 0 monochromatic edges  (chi <= 3  <=>  properCount > 0)
  - f(G)        : min # monochromatic edges over all colorings  (f == 0 <=> 3-colorable)
  - B1          : # colorings with exactly 1 monochromatic edge
  - per-EDGE criticality   : edge e is critical  <=>  chi(G - e) < chi(G).
        For the E944 k=4,r=1 setting chi(G)=4, so "critical edge" means chi(G-e)=3,
        i.e. G-e IS 3-colorable. From the SAME enumeration: G-e is 3-colorable iff
        there exists a coloring whose monochromatic-edge SET is a subset of {e}
        (every other edge bichromatic, e may or may not be mono). Equivalently
        properCount(G - e) = (# colorings with mono-set ⊆ {e}) > 0. We obtain this
        by, for each edge j, counting colorings whose total mono-count minus
        mono[e] indicator == 0 (i.e. all edges except possibly j are bichromatic).
  - per-VERTEX criticality : v is critical  <=>  chi(G - v) < chi(G).
        chi(G)=4 here, so v critical <=> G-v IS 3-colorable. G-v's colorings are
        the full enumeration restricted to edges NOT touching v (mask those edge
        columns); v's own color becomes a free trit but that only scales the count
        by 3, never changing the >0 test. So v is critical iff there exists a
        coloring with 0 mono among edges not incident to v.

IMPORTANT semantic note: all of the criticality outputs above are computed under
the assumption / and ONLY meaningful when chi(G) == 4 (the E944 regime). The kernel
ALSO returns chi-related primitives (chi_le_3 = properCount>0, f, B1) that are
graph-general. For graphs with chi != 4 the `critical_edges` / `critical_vertices`
lists follow the literal definition chi(G - x) < chi(G) which the kernel computes
exactly by comparing the exact chromatic numbers it can derive (chi<=3 directly;
chi==4 when 3-colorable fails but 4-colorable would succeed — for n<=16 the E944
search only ever feeds graphs where we care about the chi=4 boundary, and the
validation harness cross-checks the literal chi(G-x)<chi(G) against checkers.py on
graphs of chi 3,4,5,... so the definitions are exercised honestly).

Encoding: a coloring is an integer idx in [0, 3^n). Vertex v's color = (idx // 3^v) % 3.
We never materialize idx as a python int for the whole space; we build, per vertex,
the trit tensor over a CHUNK of indices on-device, in int8.

The trit tensors depend ONLY on n (not the graph), so batch mode precomputes them
once per n and reuses them for every graph — that reuse is the big win for SA loops.
"""
from __future__ import annotations

import math
from typing import Dict, List, Optional, Sequence, Tuple

import torch


def _normalize_edges(edges: Sequence[Tuple[int, int]], n: int) -> List[Tuple[int, int]]:
    """Canonicalize to sorted (a<b) tuples, dedupe, drop self-loops, validate range."""
    seen = set()
    out: List[Tuple[int, int]] = []
    for e in edges:
        a, b = int(e[0]), int(e[1])
        if a == b:
            continue
        if a > b:
            a, b = b, a
        if a < 0 or b >= n:
            raise ValueError(f"edge {(a, b)} out of range for n={n}")
        if (a, b) in seen:
            continue
        seen.add((a, b))
        out.append((a, b))
    return out


class GpuColoring:
    """Exhaustive 3-coloring analyzer for a fixed vertex count n.

    The expensive per-n trit tensors are built lazily and cached on the device, so
    a single GpuColoring(n) instance amortizes that cost across many graphs
    (analyze / analyze_batch). Construct one per n.
    """

    def __init__(self, n: int, device: str = "mps", chunk_log2: int = 22):
        if n < 1 or n > 16:
            raise ValueError("n must be in [1, 16]")
        self.n = n
        self.device = torch.device(device)
        self.total = 3 ** n
        # chunk size in number of colorings; bound memory. 2^22 ~ 4.2M colorings.
        self.chunk = min(1 << chunk_log2, self.total)
        # powers of three on host (python ints; exact)
        self._pow3 = [3 ** v for v in range(n + 1)]
        # cache of per-(chunk-extent) trit tensors keyed by (start_is_zero, length)
        # In practice all chunks except possibly the last have length self.chunk,
        # and the trit pattern for a chunk depends on the chunk's start offset only
        # through (start % 3^v) per vertex. To keep reuse simple and correct we
        # recompute trits per chunk but cache the base arange tensor.
        self._base_arange: Optional[torch.Tensor] = None

    # ------------------------------------------------------------------ helpers
    def _arange(self, length: int) -> torch.Tensor:
        """Cached [0, chunk) arange (int64) on device, sliced to `length`."""
        if self._base_arange is None or self._base_arange.numel() < self.chunk:
            self._base_arange = torch.arange(self.chunk, dtype=torch.int64, device=self.device)
        return self._base_arange[:length]

    def _trits_for_chunk(self, start: int, length: int) -> torch.Tensor:
        """Return an int8 tensor [length, n] of vertex colors for indices
        [start, start+length). color[i, v] = ((start+i) // 3^v) % 3.

        Vectorized over all n vertices at once (no python loop): broadcast the
        index column against the row of powers-of-three, one integer divide+mod."""
        idx = (self._arange(length) + start).unsqueeze(1)         # int64 [length, 1]
        if getattr(self, "_pow3_t", None) is None:
            self._pow3_t = torch.tensor(self._pow3[:self.n], dtype=torch.int64,
                                        device=self.device).unsqueeze(0)  # [1, n]
        cols = ((idx // self._pow3_t) % 3).to(torch.int8)         # [length, n]
        return cols

    # ------------------------------------------------------------------ core
    def _analyze_one(
        self,
        edges: List[Tuple[int, int]],
        edge_index: Optional[torch.Tensor] = None,
    ) -> Dict:
        n = self.n
        m = len(edges)

        # Edge endpoint tensors (on device, int64 for index_select).
        if edge_index is None:
            if m == 0:
                eu = torch.empty(0, dtype=torch.int64, device=self.device)
                ev = torch.empty(0, dtype=torch.int64, device=self.device)
            else:
                ea = torch.tensor(edges, dtype=torch.int64, device=self.device)
                eu, ev = ea[:, 0], ea[:, 1]
        else:
            eu, ev = edge_index

        # For each edge j and incident vertex test, we precompute, per edge, which
        # vertex it touches — used to build the per-vertex "edges not touching v"
        # reductions. We do that with a [m, n] incidence-exclusion mask: keep_v[j, v]
        # = 1 if edge j does NOT touch vertex v. Sum over edges with this mask gives
        # the mono-count restricted to G - v.
        # Build incidence (m x n) on host then move (cheap, m,n small).
        if m > 0:
            inc = torch.zeros((m, n), dtype=torch.int32, device=self.device)
            jj = torch.arange(m, device=self.device)
            inc[jj, eu] = 1
            inc[jj, ev] = 1
            not_touch = (1 - inc)  # [m, n] int32; 1 where edge j avoids vertex v
        else:
            not_touch = torch.zeros((0, n), dtype=torch.int32, device=self.device)

        # Accumulators (host-side python ints / float for exactness of counts).
        properCount = 0          # colorings with 0 mono
        B1 = 0                   # colorings with exactly 1 mono
        f = m + 1               # min mono-count (init above max)
        # per-edge: # colorings whose mono-set ⊆ {edge j}  (all edges except j bichromatic)
        # => G - j is 3-colorable iff this count > 0.
        edge_proper_minus = torch.zeros(m, dtype=torch.float64)  # host accum
        # per-vertex: # colorings with 0 mono among edges not touching v
        # => G - v is 3-colorable iff this count > 0.
        vert_proper_minus = torch.zeros(n, dtype=torch.float64)  # host accum

        start = 0
        while start < self.total:
            length = min(self.chunk, self.total - start)
            cols = self._trits_for_chunk(start, length)  # int8 [length, n]

            if m > 0:
                cu = cols.index_select(1, eu)            # int8 [length, m]
                cv = cols.index_select(1, ev)
                mono = (cu == cv)                        # bool [length, m]
                mono_i = mono.to(torch.int16)            # [length, m]
                total_mono = mono_i.sum(dim=1)           # int16 [length]

                # --- f, properCount, B1 ---
                cmin = int(total_mono.min().item())
                if cmin < f:
                    f = cmin
                properCount += int((total_mono == 0).sum().item())
                B1 += int((total_mono == 1).sum().item())

                # --- per-edge: mono-set ⊆ {j}  <=>  total_mono - mono[:,j] == 0
                #     i.e. removing edge j's own mono indicator leaves 0 mono. ---
                # total_mono broadcast minus mono_i gives [length, m] = # mono among
                # all OTHER edges. Count rows where that is 0, per column j.
                others = total_mono.unsqueeze(1).to(torch.int16) - mono_i  # [length, m]
                edge_zero = (others == 0)                                  # bool [length,m]
                # reduce on device in int64 (exact, no f32 mantissa loss), then accum on host
                edge_proper_minus += edge_zero.sum(dim=0, dtype=torch.int64).cpu().to(torch.float64)

                # --- per-vertex: mono among edges NOT touching v == 0 ---
                # mono_count_excl_v[:, v] = sum_j mono_i[:, j] * not_touch[j, v]
                # = mono_i @ not_touch   -> [length, n]
                excl_v = mono_i.to(torch.int32) @ not_touch  # [length, n] int32
                vert_zero = (excl_v == 0)                    # bool [length, n]
                vert_proper_minus += vert_zero.sum(dim=0, dtype=torch.int64).cpu().to(torch.float64)
            else:
                # no edges: every coloring is proper, f=0, B1=0
                properCount += length
                f = 0
                # G - j undefined (no edges); G - v also 0 mono everywhere
                vert_proper_minus += float(length)

            start += length

        chi_le_3 = properCount > 0
        chi = self._exact_chi_from_proper(edges, chi_le_3)
        critical_edges, critical_vertices = self._criticality(
            edges, chi, edge_proper_minus, vert_proper_minus)

        return {
            "n": n,
            "m": m,
            "chi": chi,
            "chi_le_3": bool(chi_le_3),
            "f": int(f),
            "B1": int(B1),
            "properCount": int(properCount),
            "critical_edges": critical_edges,
            "critical_vertices": critical_vertices,
            "num_critical_edges": int(sum(critical_edges)),
            "num_critical_vertices": int(sum(critical_vertices)),
        }

    # ------------------------------------------------------------------ shared chi/criticality
    def _exact_chi_from_proper(self, edges, chi_le_3: bool) -> int:
        """Exact chromatic number. If 3-colorable (properCount>0) refine DOWN
        (chi could be 1, 2, or 3); else refine UP from 4."""
        if not edges:
            return 1 if self.n > 0 else 0
        if not chi_le_3:
            return self._chi_ge4(edges)
        # 3-colorable: distinguish chi = 1 (edgeless, handled above), 2 (bipartite), 3.
        if self._is_bipartite(edges, self.n):
            return 2
        return 3

    def _criticality(self, edges, chi, edge_proper_minus, vert_proper_minus):
        """Per-edge / per-vertex criticality: chi(G - x) < chi(G).

        chi==4 is the E944 hot path: reuse the GPU-computed counts (G-x is critical
        iff G-x is 3-colorable iff its proper-minus count > 0). All other chi use a
        small exact CPU comparison so the literal definition holds for any graph."""
        n, m = self.n, len(edges)
        if chi == 4:
            ce = [bool(edge_proper_minus[j].item() > 0) for j in range(m)]
            cv = [bool(vert_proper_minus[v].item() > 0) for v in range(n)]
        else:
            ce = [self._chi_exact(self._edges_minus_edge(edges, j), n) < chi
                  for j in range(m)]
            cv = [self._chi_exact(self._edges_minus_vertex(edges, v), n) < chi
                  for v in range(n)]
        return ce, cv

    # ------------------------------------------------------------------ exact CPU helpers
    # These run only for chi != 4 graphs (off the E944 hot path) or for the
    # validation harness; they are small exact routines used to honor the literal
    # chi(G - x) < chi(G) definition outside the chi=4 regime.
    @staticmethod
    def _edges_minus_edge(edges, j):
        return [e for i, e in enumerate(edges) if i != j]

    @staticmethod
    def _edges_minus_vertex(edges, v):
        return [(a, b) for (a, b) in edges if a != v and b != v]

    @staticmethod
    def _is_bipartite(edges, n) -> bool:
        adj = [[] for _ in range(n)]
        for a, b in edges:
            adj[a].append(b)
            adj[b].append(a)
        color = [-1] * n
        for s in range(n):
            if color[s] != -1:
                continue
            color[s] = 0
            stack = [s]
            while stack:
                u = stack.pop()
                for w in adj[u]:
                    if color[w] == -1:
                        color[w] = color[u] ^ 1
                        stack.append(w)
                    elif color[w] == color[u]:
                        return False
        return True

    @classmethod
    def _is_k_colorable(cls, edges, n, k) -> bool:
        if k <= 0:
            return n == 0
        if k == 1:
            return len(edges) == 0
        if k == 2:
            return cls._is_bipartite(edges, n)
        adj = [0] * n
        for a, b in edges:
            adj[a] |= (1 << b)
            adj[b] |= (1 << a)
        order = sorted(range(n), key=lambda v: -bin(adj[v]).count("1"))
        color = [-1] * n

        def bt(idx, maxu):
            if idx == n:
                return True
            v = order[idx]
            forb = 0
            nb = adj[v]
            while nb:
                low = nb & (-nb)
                u = low.bit_length() - 1
                if color[u] >= 0:
                    forb |= (1 << color[u])
                nb ^= low
            limit = min(maxu + 1, k - 1)
            for c in range(limit + 1):
                if not (forb >> c) & 1:
                    color[v] = c
                    if bt(idx + 1, max(maxu, c)):
                        return True
                    color[v] = -1
            return False

        return bt(0, -1)

    @classmethod
    def _chi_exact(cls, edges, n) -> int:
        if n == 0:
            return 0
        if len(edges) == 0:
            return 1
        for k in range(1, n + 1):
            if cls._is_k_colorable(edges, n, k):
                return k
        return n

    def _chi_ge4(self, edges) -> int:
        """Called only when properCount==0 (chi>=4). Returns exact chi."""
        n = self.n
        for k in range(4, n + 1):
            if self._is_k_colorable(edges, n, k):
                return k
        return n

    # ------------------------------------------------------------------ public API
    def analyze(self, edges: Sequence[Tuple[int, int]]) -> Dict:
        edges = _normalize_edges(edges, self.n)
        return self._analyze_one(edges)

    def analyze_batch(self, list_of_edge_lists: Sequence[Sequence[Tuple[int, int]]]) -> List[Dict]:
        # Trit tensors depend only on n; the chunk loop inside _analyze_one rebuilds
        # them per call but reuses the cached arange. For maximum reuse across a
        # batch we precompute and cache all chunk trit tensors ONCE here when they
        # fit, then each graph is just index_select + compare + reductions.
        out: List[Dict] = []
        norm = [_normalize_edges(e, self.n) for e in list_of_edge_lists]
        # Precompute chunk trit tensors if the whole space (or a few chunks) fits.
        chunk_trits = self._precompute_chunk_trits()
        for edges in norm:
            out.append(self._analyze_one_cached(edges, chunk_trits))
        return out

    def _precompute_chunk_trits(self) -> List[Tuple[int, int, torch.Tensor]]:
        """Build and hold (start, length, trits[length,n] int8) for every chunk.
        For n<=14 the whole space is one or few chunks; for n=15,16 this is several
        chunks but each is reused across the whole batch — the central win."""
        chunks = []
        start = 0
        while start < self.total:
            length = min(self.chunk, self.total - start)
            chunks.append((start, length, self._trits_for_chunk(start, length)))
            start += length
        return chunks

    def _analyze_one_cached(self, edges, chunk_trits) -> Dict:
        """Same math as _analyze_one but consuming precomputed chunk trit tensors."""
        n = self.n
        m = len(edges)
        if m == 0:
            return self._analyze_one(edges)

        ea = torch.tensor(edges, dtype=torch.int64, device=self.device)
        eu, ev = ea[:, 0], ea[:, 1]
        inc = torch.zeros((m, n), dtype=torch.int32, device=self.device)
        jj = torch.arange(m, device=self.device)
        inc[jj, eu] = 1
        inc[jj, ev] = 1
        not_touch = (1 - inc)

        properCount = 0
        B1 = 0
        f = m + 1
        edge_proper_minus = torch.zeros(m, dtype=torch.float64)
        vert_proper_minus = torch.zeros(n, dtype=torch.float64)

        for (start, length, cols) in chunk_trits:
            cu = cols.index_select(1, eu)
            cv = cols.index_select(1, ev)
            mono = (cu == cv)
            mono_i = mono.to(torch.int16)
            total_mono = mono_i.sum(dim=1)
            cmin = int(total_mono.min().item())
            if cmin < f:
                f = cmin
            properCount += int((total_mono == 0).sum().item())
            B1 += int((total_mono == 1).sum().item())
            others = total_mono.unsqueeze(1).to(torch.int16) - mono_i
            edge_zero = (others == 0)
            edge_proper_minus += edge_zero.sum(dim=0, dtype=torch.int64).cpu().to(torch.float64)
            excl_v = mono_i.to(torch.int32) @ not_touch
            vert_zero = (excl_v == 0)
            vert_proper_minus += vert_zero.sum(dim=0, dtype=torch.int64).cpu().to(torch.float64)

        chi_le_3 = properCount > 0
        chi = self._exact_chi_from_proper(edges, chi_le_3)
        critical_edges, critical_vertices = self._criticality(
            edges, chi, edge_proper_minus, vert_proper_minus)
        return {
            "n": n, "m": m, "chi": chi, "chi_le_3": bool(chi_le_3),
            "f": int(f), "B1": int(B1), "properCount": int(properCount),
            "critical_edges": critical_edges, "critical_vertices": critical_vertices,
            "num_critical_edges": int(sum(critical_edges)),
            "num_critical_vertices": int(sum(critical_vertices)),
        }


# convenience builders for the validation fixtures -------------------------------
def circulant_edges(n: int, conns: Sequence[int]) -> List[Tuple[int, int]]:
    E = set()
    for d in conns:
        for i in range(n):
            a, b = i, (i + d) % n
            if a != b:
                E.add((min(a, b), max(a, b)))
    return sorted(E)


def cocktail_party_edges(parts: int) -> Tuple[int, List[Tuple[int, int]]]:
    """K_{2,2,...,2} with `parts` groups of size 2 (complement of a perfect matching)."""
    n = 2 * parts
    pair = {2 * i: 2 * i + 1 for i in range(parts)}
    pair.update({2 * i + 1: 2 * i for i in range(parts)})
    E = []
    for a in range(n):
        for b in range(a + 1, n):
            if pair[a] != b:
                E.append((a, b))
    return n, E


if __name__ == "__main__":
    import sys
    dev = sys.argv[1] if len(sys.argv) > 1 else "mps"
    n = 13
    g = GpuColoring(n, device=dev)
    r = g.analyze(circulant_edges(13, [1, 2, 5]))
    print(f"C13(1,2,5) on {dev}:", {k: r[k] for k in
          ("chi", "f", "B1", "num_critical_edges", "num_critical_vertices")})
