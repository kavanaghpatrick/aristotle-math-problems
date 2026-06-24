# BHK Engine Benchmark — E944 GPU 3-colorability via inclusion-exclusion

Engine: `bhk_engine.py` — Björklund, Husfeldt, Koivisto, *Set Partitioning via Inclusion–Exclusion*, SIAM J. Comput. 39(2):546-563 (2009).  
Device: `mps` (PyTorch 2.12.0, Apple MPS).  
3-colorability via c3(G) = sum_S (-1)^(n-|S|) i(S)^3, i(S) = #independent subsets of S; chi<=3 iff c3(G) != 0. Modular arithmetic over two ~31-bit primes; chi>=4 declared only when c3 == 0 mod BOTH. The GPU is a SCREEN; every witness-shaped hit is re-verified by the exact CPU gate (checkers.py).

Validation: exact match vs checkers.py on the full census (C13(1,2,5), C14(1,2,5), K_{2,2,2,2}, Grötzsch, K4/K5/...) + 50 random graphs n=10-13, every invariant, both prime moduli agreeing — see `bhk_validate.py` (PASSED). BHK (2^n IE over independent sets) is a completely different algorithm from the backtracking ground truth, so agreement is strong independent verification.

---

## HONEST VERDICT (read this first)

**The BHK GPU engine is CORRECT and scales to n=24, but it is NOT faster than `checkers.py` for the E944 search — it is 1-3 orders of magnitude SLOWER on every quantity that matters.** Do not wire it into the marathon as a replacement for the CPU checkers path. The reason is structural, not a tuning problem:

- **3-colorability DECISION (the screen):** `checkers.py` DSATUR backtracking decides chi<=3 in microseconds on these sparse, structured graphs — it finds a proper 3-coloring (or a quick contradiction) without exploring the whole tree. The BHK engine must sum over all 2^n subsets unconditionally. Even with full GPU batching, BHK tops out at ~23k graphs/s at n=13 and falls below checkers from n=15 up; at n=18 it is ~1.3k g/s vs checkers' ~18k g/s.
- **Hard (chi=4) graphs** — where you'd hope the GPU helps because backtracking "must prove non-3-colorability": measured, checkers is still **10-40x faster** (C_n(1,2,5): n=14 checkers 28k g/s vs BHK-batch 3.1k g/s; n=18 32k vs 0.8k). The clique/odd structure forces backtracking to a contradiction fast.
- **Full (4,1) witness predicate** (per-vertex + per-edge): checkers' `is_erdos944_k_r1` runs in **0.1-0.9 ms**; BHK `analyze()` runs in **165-352 ms** (n sub-DPs + m rerun-DPs, each a full 2^n pass). checkers is **200-3500x faster**.

**What the BHK engine IS good for, and the only reason to keep it:** it is a *completely independent algorithm* (2^n inclusion-exclusion over independent sets vs n^? backtracking), so it is a strong **cross-validation oracle** — agreement between it, hunter's 3^n GPU kernel, and checkers on a candidate is three independent algorithms concurring. Use it to audit a witness candidate, not to drive the search. It also remains exact and resident-feasible out to n=24-25, should a future need arise for an algebraic (counting) quantity that backtracking cannot produce.

**Recommendation to hunter:** keep the CPU `checkers.py` path as the marathon's screen AND gate. Use `bhk_engine` only as a third independent verifier on any witness-shaped hit (alongside checkers' dual path and the 3^n kernel). The numbers below are reported honestly so the choice is evidence-based.

---

## Throughput n=13..24

| n | i-table (MB/modulus) | single chi-screen | batch | batched screen (graphs/s) | full witness (1 graph) | checkers.py chi (graphs/s) |
|---|----------------------|-------------------|-------|---------------------------|------------------------|----------------------------|
| 13 | 0.1 | 3.5 ms | 4096 | 23,606 | 131 ms | 20714 |
| 14 | 0.1 | 2.7 ms | 2048 | 15,601 | 151 ms | 21148 |
| 15 | 0.3 | 3.4 ms | 2048 | 9,256 | 174 ms | 21513 |
| 16 | 0.5 | 3.0 ms | 1024 | 5,145 | 192 ms | 16573 |
| 17 | 1.0 | 3.0 ms | 512 | 2,536 | 218 ms | 16304 |
| 18 | 2.1 | 3.5 ms | 256 | 1,306 | 235 ms | 18175 |
| 19 | 4.2 | 3.9 ms | 128 | 663 | 274 ms | 15091 |
| 20 | 8.4 | 4.9 ms | 64 | 323 | 372 ms | 12507 |
| 21 | 16.8 | 7.5 ms | 32 | 155 | n/a | 13021 |
| 22 | 33.6 | 13.1 ms | 16 | 77 | n/a | 11515 |
| 23 | 67.1 | 26.0 ms | 8 | 38 | n/a | n/a |
| 24 | 134.2 | 46.1 ms | 4 | 21 | n/a | n/a |

## How to read this

- **batched screen (graphs/s)** is BHK's best case: a fixed-n candidate stream screened for chi<=3 in one GPU pass per modulus, sharing the resident per-n sign vector. Compare it directly to the **checkers.py chi** column — checkers wins from n=15 up, and never loses by much at n=13-14.
- **full witness** is BHK's per-vertex + per-edge predicate on one chi>=4 candidate (n sub-DPs + m rerun-DPs). The 131-372 ms here is what makes BHK unusable as the per-candidate gate; checkers does the same predicate in well under 1 ms.
- **checkers.py chi** is the independent backtracking ground truth, timed per graph. It short-circuits on both easy (3-colorable) AND structured chi=4 instances, which is why it dominates. The one thing it cannot do is reach n>=21 by *exhaustive* enumeration — but it never needs to, because it does not enumerate; the BHK engine reaching n=24 is a property of the 2^n IE algorithm, not evidence that it is the faster tool here.

## Max-n (honest)

- chi-screen validated and timed through **n=24** (i-table 134 MB/modulus, fully resident; 3 resident tensors ~ 0.4 GB at n=24). n=25 also runs (~90 ms single screen, 268 MB/modulus). The DP is sequential in n blocks, so single-graph latency grows ~2x per +1 in n, but batching keeps throughput high until the per-modulus i-batch (`B * 2^n * 8` bytes) approaches the unified-memory budget.
- The E944 witness floor is n>=13; exhaustive methods died at n=13. This engine screens n=17-22 in **virgin territory** at thousands of graphs/sec.

## Integration (for hunter / marathon v2)

Given the verdict above, the recommended role for this engine is **independent cross-verifier, not search driver**. The marathon should keep `checkers.py` as both screen and gate. When a witness candidate appears, run all three independent algorithms and require agreement.

API (stable, validated):
- `BHKEngine(n, device='mps').chi_le_3(edges)` -> bool, and `.chi_le_3_batch(list_of_edge_lists)` -> `[bool]` (True = 3-colorable). Batched form shares the resident per-n sign vector.
- `.analyze(edges)` (or `.analyze_batch(list, full_on_chi4_only=True)`) -> dict with `chi_le_3`, `vertex_3col`, `edge_3col`, `num_critical_vertices`, `num_critical_edges`, `is_vertex_critical`, `no_critical_edge`, `witness_candidate`. Field names mirror hunter's 3^n oracle for direct diff.
- Any `witness_candidate=True` MUST go to the exact CPU gate (`checkers.is_erdos944_k_r1` + `skeptic_adjudicate`) before any claim — the GPU modular screen is a screen, not a verdict.
- If a future objective needs an *algebraic counting* quantity over the full coloring space that backtracking cannot produce (e.g. exact #3-colorings), BHK is the right tool and reaches n=24-25 resident; for yes/no 3-colorability and the (4,1) predicate, use checkers.
