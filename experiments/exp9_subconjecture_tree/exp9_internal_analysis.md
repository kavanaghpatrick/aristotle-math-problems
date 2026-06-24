# EXP9 Internal Analysis (pre-Codex)

(Used to validate Codex's review; redundancy mapping done independently before reading Codex output.)

## Redundancy mapping (Grok tree → existing slots 1259-1343)

| Grok ID | Sketch matched | Verdict |
|---|---|---|
| W3 (Chan d ≫ N^{1/2-ε} extension) | yolo_e938_deep_abc, erdos938_chan_abc_conditional_iter2 | DUPLICATE |
| W4 (3-APs inside squares) | implicit in yolo_w4a_e938_unconditional_extract (uses intervening-square bound) | PARTIAL DUPLICATE |
| W5 (mod-72 admissibility) | yolo_mega11_e938_e364_joint_mod | DUPLICATE |
| W7 (range-bounded numerical search to 10^20) | yolo_mega7_e938_pell_classification | DUPLICATE |
| R1 (A_1 family finite) | yolo_mega2_e938_van_doorn_verification (verifies first triple, falsification frame) | PARTIAL DUPLICATE (different direction) |
| R2 (square-only powerful) | yolo_w4a_e938_unconditional_extract (square-gap bound) | PARTIAL DUPLICATE |
| R3 (cubes only) | implicit in Chan 2025 / She 2025 already cited | LIT-DUPLICATE not slot-duplicate |
| D2 (Frey-Hellegouarch surface finiteness) | erdos938_fusion, yolo_w3_e938_direct, yolo_w4_e938_final | DUPLICATE |
| D7 (Pell x²-2y²=±1 powerful solutions) | yolo_mega7_e938_pell_classification | PARTIAL DUPLICATE |
| C2 (local + Frey height) | erdos938_chan_abc_conditional_iter2 + erdos938_fusion implicit conjunction | PARTIAL DUPLICATE |
| C6 (Chan + A_1 split) | yolo_e938_deep_abc + yolo_mega7_e938_pell_classification implicit | PARTIAL DUPLICATE |
| N1 (van Doorn A_1 infinitude) | yolo_mega2_e938_van_doorn_verification | DUPLICATE |

NOT obviously in any prior slot (candidate NEW angles):
- **R5** (b = prime 3, Thue over Q(√-3)) — Thue-equation per-prime restriction
- **R6** (≡1 mod 9 progression, cubic-residue descent)
- **R7** (5-smooth powerfuls, S-unit / Baker)
- **S5** (common difference not square — generalized Pell)
- **S6** (gap-spacing growth ≫ log N — Frey height)
- **C3** (squares ∧ cubes parametrization split) — clean a²b³ logic split; not directly in any slot
- **C4** (2-adic ∧ odd valuation split)
- **C7** (cube-middle Chan 2025 ∧ non-cube-middle remainder)
- **D1** (b₁X² + b₃Z² = 2b₂Y² ternary quadratic — kernel-quadratic isolated as INDEPENDENT statement)
- **D5** (Markoff surface analog)
- **N3** (cube-middle infinitude after She)
- **N5** (CRT local-to-global construction)
- **G2** (4-term consecutive powerful AP — extends from m=3 to m=4)

## Score corrections I would propose (before reading Codex)

### Underrated (T or I too low):

1. **D1 (b₁X² + b₃Z² = 2b₂Y² powerful solutions)** — Grok: T=5, I=9, EV=45.
   - Tractability: SHOULD BE 7. Per-kernel Mordell-Siegel is UNCONDITIONAL and in Mathlib reach (NumberTheory.Pell + SiegelsLemma). The L5 lemma in `yolo_e938_meta` already targets exactly this.
   - Adjusted EV = 63.

2. **C3 (squares ∧ non-square-non-cube)** — Grok: T=5, I=9, EV=45.
   - Impact: SHOULD BE 9 (correct). Tractability: SHOULD BE 6 — square case follows Erdős-Mollin-Walsh framework (open but heavily studied); the non-square case is genuinely E938-hard.
   - Adjusted EV stays ~45-54. Reasonable but does not break new ground.

3. **C7 (cube-middle Chan 2025 ∧ non-cube-middle)** — Grok: T=5, I=9, EV=45.
   - Impact: 10 (resolution implies E938) — bump to 10. T fine.
   - Adjusted EV = 50. Best clean decomposition that actually leverages a published partial theorem.

4. **R7 (5-smooth powerfuls, Baker linear forms)** — Grok: T=7, I=6, EV=42.
   - Both correct. Baker linear forms IS in Mathlib (`Mathlib.NumberTheory.Transcendental` partial). Real impact lever: S-unit kernel finiteness uniformizable across smooth primes.
   - Hold at 42.

5. **N5 (local-to-global lifting)** — Grok: T=5, I=7, EV=35, Novelty=8.
   - Most underrated. If a constructive CRT lifting of powerful 3-AP residues from mod-M to mod-2M works, it would establish a STRUCTURAL FAMILY independent of A_1 — actually a path to FALSIFY E938. Impact should be 9 (resolution either way).
   - Adjusted EV = 45.

### Overrated:

1. **D2 (Frey-Hellegouarch surface)** — Grok: T=2, I=10, EV=20.
   - Already attempted (slots 752 fusion, w3, w4). Aristotle returned compiled_no_advance because level-lowering Mathlib infrastructure missing. T should be 1 (not just hard — known-blocked at Mathlib level).
   - Adjusted EV = 10.

2. **D7 (Pell x²-2y²=±1 powerful solutions imply E938)** — Grok: T=6, I=9, EV=54.
   - Impact OVER-CLAIMED: A_1 family is not the only family. Resolving Pell-powerful does NOT cover non-A_1 families. Impact should be 7.
   - Tractability: 4 (open per van Doorn).
   - Adjusted EV = 28.

3. **S2 (Effective bound on largest 3-AP)** — Grok: T=2, I=9, EV=18.
   - Properly low; flag this as correctly scored but Grok placed it in top-10 ranking which is misleading.

4. **C5 (kernel Mordell-Siegel ∧ surface Vojta)** — Grok: T=2, I=10, EV=20.
   - Same trap as D2: Vojta on dim-2 general type is way out of reach. Even isolated as a decomposition, both halves are open. T=1.
   - Adjusted EV = 10.

5. **G1 (k-powerful generalization)** — Grok: T=3, I=7, EV=21.
   - Impact should be lower (4). A general-k uniform abc statement is HARDER than k=2 and does not back-implicate E938 cleanly because the uniform constant in k is the bottleneck.

### Missed decomposition (what Grok did not propose):

**E938 ⇔ (PURE SQUARE-FREE-PART STABILITY) ∧ (BOUNDED-RADICAL UNIQUENESS)**

X := "For any fixed sequence of squarefree (b_0, b_1, b_2), the set of 3-APs (a_0²b_0³, a_1²b_1³, a_2²b_2³) of consecutive powerful is finite."
Y := "The set of squarefree triples (b_0, b_1, b_2) that admit ANY such 3-AP solution is finite."

Then E938 ⇔ X ∧ Y.

X is essentially per-kernel Mordell-Siegel (D1 territory). Y is the open dim-2 / Bombieri-Lang side. Crucially: Y is sometimes provable WITHOUT Vojta when one shows the height of (b_0, b_1, b_2) on a single S-arithmetic surface is bounded by elementary descent — this happens for several Mordell-curve transfers but Grok did not extract it as a clean decomposition.

This decomposition is structurally CLEANER than C2 (local+height) or C5 (kernel+Vojta) because the second component is **purely combinatorial over squarefree triples** — exactly what arithmetic-statistics methods (Bhargava-Shankar-Tsimerman) could attack.

## Pre-Codex top 5 (my own)

By Codex-adjusted EV:
1. **D1** — EV 63 (kernel quadratic ternary, T-underrated; unconditional Mordell-Siegel route)
2. **C7** — EV 50 (Chan 2025 + non-cube remainder, leverages published theorem)
3. **N5** — EV 45 (CRT lifting; the falsification-by-construction angle most distinct from prior work)
4. **R7** — EV 42 (S-unit / Baker on 5-smooth powerfuls)
5. **C3** — EV 45 (squares + cubes parametrization split, distinct from C7)

NONE of these top-5 are exact duplicates of slots 1259-1343, though D1 overlaps significantly with `yolo_e938_meta` L5 sublemma and `yolo_d3_e938_coprime_finite` framing. R7, N5, and C7 are CLEAN new angles.
