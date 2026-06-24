"""
e944 GPU verification kernel (hunter, team-lead GPU directive 2026-06-11).

Enumerates ALL 3^n colorings of a graph on the GPU (PyTorch MPS, Apple Silicon) in ONE pass and
extracts EXACTLY, with no re-enumeration:
  - chi <= 3  (a proper 3-coloring exists)  -> if False and 4-colorable then chi == 4
  - f(G)      = min monochromatic-edge count over all 3-colorings (0 iff chi<=3)
  - B1        = number of colorings with exactly 1 monochromatic edge (min-conflict mass)
  - per-EDGE criticality:   chi(G - e) <= 3 ?  (deleting e makes it 3-colorable -> e is critical)
  - per-VERTEX criticality: chi(G - v) <= 3 ?  (deleting v makes it 3-colorable -> v is critical)

Method (vectorized over a CHUNK of colorings at a time):
  color of vertex v in coloring k = (k // 3^v) % 3.   We materialize the n trits for a chunk of
  colorings as an int8 tensor [chunk, n] on MPS. For each edge (a,b) the indicator
  (color[:,a]==color[:,b]) is a monochromatic-edge boolean; summing over edges gives the per-coloring
  mono count [chunk]. From the per-coloring mono counts and per-edge mono booleans we read off all the
  quantities above:
    - a coloring is proper for the FULL graph iff its mono count == 0.
    - a coloring is proper for G - e iff its mono count, MINUS this edge's own mono indicator, == 0
      (i.e. it is proper on every edge except possibly e). So "G-e is 3-colorable" iff
      exists a coloring with (mono_total - mono_edge_e) == 0.
    - a coloring is proper for G - v iff it is proper on every edge NOT incident to v. We compute the
      per-coloring count of monochromatic edges incident to v; G-v 3-colorable iff exists a coloring
      with (mono_total - mono_incident_to_v) == 0.
  All as reductions over the chunk; accumulate across chunks.

Exactness: this is a COMPLETE enumeration of the 3-coloring space, so every result is exact (no
heuristic). 4-colorability (for chi==4) is checked once on CPU via the validated backtracking
(4^n is large; we only need a yes/no and backtracking is instant for these graphs).

VALIDATION against checkers.py on the known census is MANDATORY before any production use (see
gpu_verifier_validate.py). Any mismatch => stop.
"""
import torch

def _device():
    return torch.device("mps") if torch.backends.mps.is_available() else torch.device("cpu")


def gpu_coloring_analysis(n, edges, incident_vertex=True, chunk_log2=22, device=None):
    """Full 3-coloring enumeration analysis on GPU.
    edges: list of (a,b), a<b, 0-indexed. Returns dict with f, chi_le_3, B1,
    per-edge 'G-e 3-colorable' flags, per-vertex 'G-v 3-colorable' flags.
    """
    dev = device or _device()
    m = len(edges)
    total = 3 ** n
    ea = torch.tensor([a for (a, b) in edges], dtype=torch.long, device=dev)
    eb = torch.tensor([b for (a, b) in edges], dtype=torch.long, device=dev)
    pow3 = torch.tensor([3 ** v for v in range(n)], dtype=torch.long, device=dev)  # [n]

    # ON-DEVICE accumulators (synced to host ONCE at the end — no per-chunk .item() stalls).
    f_min_t = torch.full((), m + 1, dtype=torch.long, device=dev)            # global min mono count
    B1_t = torch.zeros((), dtype=torch.long, device=dev)                     # count of mono_total==1
    # per-edge / per-vertex: track the MIN over colorings of the residual; ==0 iff G-e / G-v 3-colorable
    edge_resid_min = torch.full((m,), m + 1, dtype=torch.long, device=dev)
    vert_resid_min = torch.full((n,), m + 1, dtype=torch.long, device=dev)

    chunk = 1 << chunk_log2
    start = 0
    while start < total:
        end = min(start + chunk, total)
        ks = torch.arange(start, end, dtype=torch.long, device=dev)            # [c]
        colors = (ks.unsqueeze(1) // pow3.unsqueeze(0)) % 3                    # [c, n] int64
        ca = colors[:, ea]                                                     # [c, m]
        cb = colors[:, eb]
        mono = (ca == cb)                                                      # [c, m] bool
        mono_l = mono.long()
        mono_total = mono_l.sum(dim=1)                                         # [c]

        f_min_t = torch.minimum(f_min_t, mono_total.min())
        B1_t = B1_t + (mono_total == 1).sum()

        # G-e residual = mono_total - mono_e ; min over colorings (on-device, no sync)
        resid_e = mono_total.unsqueeze(1) - mono_l                            # [c, m]
        edge_resid_min = torch.minimum(edge_resid_min, resid_e.min(dim=0).values)

        if incident_vertex:
            inc = torch.zeros((end - start, n), dtype=torch.long, device=dev)
            inc.index_add_(1, ea, mono_l)
            inc.index_add_(1, eb, mono_l)
            resid_v = mono_total.unsqueeze(1) - inc                           # [c, n]
            vert_resid_min = torch.minimum(vert_resid_min, resid_v.min(dim=0).values)

        start = end

    f_min = int(f_min_t.item())
    return {
        "n": n, "m": m,
        "chi_le_3": f_min == 0,
        "f": f_min,
        "B1": int(B1_t.item()),
        "edge_3col": (edge_resid_min == 0).cpu().tolist(),   # per-edge: G-e is 3-colorable (edge critical)
        "vert_3col": (vert_resid_min == 0).cpu().tolist(),   # per-vertex: G-v is 3-colorable (vertex critical)
        "device": str(dev),
    }


def gpu_is_witness(n, edges, chunk_log2=22, device=None):
    """Full (4,1)-witness decision via GPU enumeration + CPU 4-colorability check.
    Witness iff: chi==4 (not 3-colorable AND 4-colorable), every vertex critical (G-v 3-colorable
    for all v), and NO critical edge (G-e NOT 3-colorable for all e). Returns (bool, info)."""
    a = gpu_coloring_analysis(n, edges, incident_vertex=True, chunk_log2=chunk_log2, device=device)
    if a["chi_le_3"]:
        return False, {**a, "reason": "chi<=3"}
    # 4-colorable? (cheap CPU backtracking)
    import sys
    sys.path.insert(0, "/Users/patrickkavanagh/math/analysis/e944/team")
    from checkers import is_k_colorable_backtrack, edges_to_adj
    if not is_k_colorable_backtrack(edges_to_adj(edges, n), n, 4):
        return False, {**a, "reason": "chi>=5"}
    # vertex-critical: all G-v 3-colorable
    if not all(a["vert_3col"]):
        return False, {**a, "reason": "not vertex-critical"}
    # no critical edge: no G-e is 3-colorable
    if any(a["edge_3col"]):
        return False, {**a, "reason": "has critical edge"}
    return True, {**a, "reason": "WITNESS"}


def num_critical_edges(n, edges, chunk_log2=22, device=None):
    a = gpu_coloring_analysis(n, edges, incident_vertex=False, chunk_log2=chunk_log2, device=device)
    return sum(1 for x in a["edge_3col"] if x)  # edges whose deletion makes G 3-colorable
