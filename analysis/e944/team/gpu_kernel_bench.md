# GPU Kernel Benchmark — E944 exhaustive 3-coloring analysis

Device: `mps` (PyTorch 2.12.0, Apple MPS).  
Full-exact analysis = chi + f + B1 + properCount + per-edge criticality + per-vertex criticality, all exact over the entire 3^n coloring space.

Each graph is 6-regular at the given n (the E944 witness-search regime); the n=13..16 row's first graph is the canonical circulant C_n(1,2,5).

| n | graphs | m (ex.) | GPU single (g/s) | GPU batch (g/s) | checkers.py (g/s) | speedup (batch) |
|---|--------|---------|------------------|-----------------|-------------------|-----------------|
| 13 | 50 | 39 | 23.0 | 32.6 | 342.877 | 0x |
| 14 | 30 | 42 | 7.1 | 10.3 | 194.979 | 0x |
| 15 | 12 | 45 | 2.2 | 3.2 | 169.424 | 0x |
| 16 | 6 | 48 | 0.7 | 1.0 | 198.381 | 0x |

Notes:
- `checkers.py (g/s)` is the rate of the full backtracking dual-path analysis (chi + per-vertex + per-edge) used by the verification gate; timed on a capped subset per row (cap shown below) since it is ~exponential per graph.
- Batch mode precomputes the per-n trit tensors once and reuses them across all graphs (they depend only on n, not the graph) — the central win for SA objective loops that evaluate thousands of candidates at fixed n.
- The kernel is EXACT (full 3^n enumeration), not sampled. At n=16 that is 43,046,721 colorings per graph.

Per-row checkers cap (graphs timed): n=13:12, n=14:12, n=15:6, n=16:6.
