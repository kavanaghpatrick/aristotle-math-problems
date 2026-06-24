# EXP4 "E938 → Mordell Reduction" — Adversarial Verification Verdict

**Date:** 2026-05-31
**Subject:** EXP4 claim that consecutive powerful 3-term APs reduce to the equation `x² + w³ = y²` ("the Mordell equation") via the map `(8kw³, 4ky², 8kx²)`, "unlocking vast machinery."
**Method:** 9 independent structured verdicts + synthesis-agent re-verification (sympy, DB query).

## Overall verdict: **OVERSOLD**

The forward construction is a correct, trivially-elementary identity. The converse — the only direction that would make this a *reduction* — is **provably false** (refuted by an explicit published counterexample). The "vast machinery" framing is a mirage. There is no novel valid result, and no new tractable formal target for Aristotle. Recommendation: **DO_NOT_SUBMIT**.

---

## Claim-by-claim verdicts

### Verdict 1 — Forward construction: **CONFIRMED** (but trivial)
For every `(w,x,y)` with `x²+w³=y²` and `x²>w³`, the triple `(8w³, 4y², 8x²)` is a powerful, increasing 3-term AP.

- **Re-verified by synthesis agent (sympy):** F1 `(6,15,21)→(1728,1764,1800)` and F2 `(45,302,427)→(729000,729316,729632)` are both valid APs, all three terms powerful, middle term a perfect square. Equation holds exactly in both cases.
- **Why it's trivial:** The *powerful* property is **unconditional** — `8w³=2³·w³`, `4y²=2²·y²`, `8x²=2³·x²` are powerful for *any* positive integers (prefactor gives 2 with exponent ≥2; the square/cube gives every odd prime exponent ≥2). No equation is needed. The *AP* property is **literally the equation rescaled**: `2·(4ky²) − (8kw³+8kx²) = 8k·(y²−w³−x²)` (synthesis agent confirmed this collapses to `8k·(y²−x²−w³)`). So "AP" is equivalent to, not a consequence of, the equation.
- **Caveat:** The map produces **non-consecutive** APs in general — and consecutiveness is the entire difficulty of E938. The literal `(8w³,4y²,8x²)` shape misses 2 of the 4 known consecutive APs up to 2M (those need the `k`-multiplier).

### Verdict 2 — The converse ("the reduction"): **REFUTED** (confidence 0.97)
Claim: every consecutive powerful 3-AP has the form `(8kw³, 4ky², 8kx²)`.

- **Explicit counterexample (synthesis agent independently re-verified):**
  `(149022674775, 149022848000, 149023021225)`, `d = 173225`.
  - `n0 = 3³·5²·13³·317²` — **ODD**, powerful
  - `n1 = 2¹⁰·5³·13²·83²` — even, powerful
  - `n2 = 5²·13²·5939²` — **ODD**, powerful
  - `2·n1 = n0+n2` confirmed; `n0 ≡ 7 (mod 8)`, `n2 ≡ 1 (mod 8)`.
- Because `8kw³` and `8kx²` are **always even**, an odd `n0` (or `n2`) can never equal them. The claimed form is **arithmetically impossible** for this triple. This is a hard structural refutation, not a borderline numerical one.
- **Triangulated:** this triple is row 7 of an independent `a²b³` sieve and appears **verbatim** in arXiv:2605.06697 (van Doorn) Table 1.

### Verdict 3 — "Exactly 6 up to 10¹¹, all Mordell, only 2 primitive bases": **REFUTED** (confidence 0.97)
- Artifact baseline reproduced (6 consecutive 3-APs up to 1e11, all Mordell), but the bound `1e11` sat *just below* the first counterexample at `~1.49e11`.
- Extended sieve (validated complete against brute force to 1e6): **10** consecutive 3-APs up to 1e12; **15** up to 1e13. Only 6 fit the Mordell form; **9 do not** (including the odd `n0` above and two more `≡4 (mod 8)`). The "empirical pattern from 6 examples" was an **undersized-window artifact**.

### Verdict 4 — "Vast machinery (Hall, Coates-Wiles, elliptic curves)": **OVERSOLD** (confidence 0.9)
- `x²+w³=y² ⇔ y²−x²=w³` is a **3-variable difference-of-squares-equals-a-cube** surface with **infinitely many** solutions (≥1 per `w`), solved by elementary factoring `w³=(y−x)(y+x)`. It is **NOT** the classical Mordell equation `y²=x³+k` (fixed `k`, finitely many points). Rank/descent/Coates-Wiles **do not apply** — there is no single finite-rank curve.
- The only genuine deep content is a Hall/abc-type bound on `|y²−2w³|`, which is **precisely Chan 2022's existing conditional result** (arXiv:2210.00281), not something the "Mordell" relabel unlocks.

### Verdict 5 — CLAIM 5 (Type-B emptiness + 3+2√2 control): **PARTLY_TRUE** (confidence 0.9)
- **SC7 algebra CONFIRMED (synthesis agent, sympy):** `(b³−a³)²+(2ab)³ − (b³+a³)² = 4a³b³ > 0`. The naive Type-B formula never satisfies the equation. **But the implication "two-type only" is FALSE/oversold:** brute-force divisor enumeration finds 5405 primitive Mordell solutions for `w≤2000`, of which **3416 have even `w`** (e.g. real solution `(8,127,129)`). EXP4's Type A + Type C cover only ~20%. EXP4 had the *wrong parametrization* for even-`w`, not a proof of emptiness.
- **Claim B CONFIRMED in mechanism (synthesis agent):** deficit ratio `= ¼(r+1/r−6)` with `r=(b/a)³`; positive iff `r²−6r+1>0`, roots **exactly `3±2√2`**, threshold `b/a = (3+2√2)^(1/3) = 1.799632`. The checkable headline numbers (F2's `79/91125`, the convergent `424877/236091` with ratio `~7e-12`) verify.
- **Sloppiness:** the artifact ships *fabricated* intermediate "convergents" (`1798/999`, `1807/1004`) and a wrong CF `[1;1,3,1,33,…]` (true: `[1;1,3,1,107,…]`) — float64-precision corruption. Non-load-bearing but a quality red flag.

### Verdict 6 — Novelty ("Mordell generative family is NEW"): **REFUTED** (confidence 0.9)
- The square-times-4 / cube-times-8 Pell construction **and** the `(3+2√2)` control are **explicit in Chan 2022, Theorem 3** (`X²−2Y²=1`, solutions `(3+2√2)^m`, `x=8Y²`, `x+4=4X²` — numerically verified). The underlying machinery is **Golomb 1970** (`a²b³` form, consecutive powerful pairs via `x²−ny²=±1` with `n` a cube) and **Walker 1976** (Pell-based, one term a square). **van Doorn 2026** (arXiv:2605.06697) develops the same `A_0/A_1/A_2` square-count taxonomy.
- EXP4's `(8w³,4y²,8x²)` notation is fresh; the mathematics is a known classical decomposition relabeled. Renaming `y²=x²+w³` "the Mordell equation" adds **no theorem**.

### Verdict 7 — "Addresses the OPEN direction of E938": **OVERSOLD** (confidence 0.9)
- E938 is stated correctly (finitely many consecutive powerful 3-APs; Erdős 1976). The Mordell angle **re-describes** the 6 known examples but **does not bound or exclude new APs**: consecutiveness is an uncontrolled side-condition; the converse is an admitted 6-point fit (artifact lines 108/188/230 say "only an empirical pattern"); the equation is an infinite-solution surface.
- **Wrong truth-value risk:** the most recent paper (van Doorn, arXiv:2605.06697) **conjectures E938 is FALSE** (infinitely many consecutive progressions, via Pell `x²−7³y²=2`). EXP4's reduction is built to prove *finiteness* — opposite to the field's current leading evidence — and never engages it.

### Verdict 8 — Mining the 18 prior Aristotle returns: **PARTLY_TRUE** (confidence 0.9)
- **(a) FALSE as stated.** The DB-labeled `disproven` submission (`yolo_e938_deep_stark`, id 1312) leaves `erdos_938` as `sorry`, has zero axioms, and negates **no** lemma. It honestly notes (in a docstring) that the CM-curve approach `y²=x(x+d)(x+2d)` fails — a *true* statement that an approach fails, not a false lemma. **The DB `disproven` label is a misclassification**; `false_lemmas` correctly has no E938 entry. (Recommended fix: relabel id 1312 to `compiled_partial` or `compiled_no_advance`.)
- **(b) TRUE for 1 of 4 partials.** `yolo_e938_deep_abc` (id 1315) fully proves (sorry-free, axiom-clean) the unconditional bound `d < 2√N + 2` plus the AP identity `n₁²=n₀n₂+d²` and supporting radical lemmas; only the abc lower bound is `sorry`. The other 3 prove only trivial lemmas. This is real but **FOLKLORE** (matches Chan-2022-style results).
- **(c) TRUE and important.** ≥6 of the 18 reference Pell/Mordell. `yolo_mega2_e938_van_doorn_verification` contains a **fully-proved, sorry-free, axiom-clean** construction of infinitely many *powerful* (not consecutive) 3-APs via Pell `x²−343y²=2`. **EXP4's own artifact (lines 178/197) admits MEGA-7 already had the Pell `x²−7³y²=2` setup and the `427²−302²=5³·3⁶` identity.** EXP4's specific `(8w³,4y²,8x²)` family *is* algebraically distinct from the van Doorn Pell family (F2 has `N=729000`, not a perfect square, so F2 ∉ van Doorn family) — so EXP4 is not *pure* relabeling — but the ground was already substantially covered by Aristotle before EXP4.

### Verdict 9 — "A 19th Mordell-framed FUSION submission would do better": **REFUTED** (confidence 0.82)
- Four reasons tractability fails: (1) infinite-solution surface, not a finite curve; (2) finiteness still hinges entirely on the open deficit bound `x²−w³ ≤ w^1.5`, which the reparametrization does nothing for; (3) the converse is a 6-point empirical fit (only ~1.3% of general powerful 3-APs fit the form); (4) **mathematically equivalent to the already-failed Pell framing** (MEGA7), where Aristotle left it `sorry` and the heuristic *predicts the answer is FALSE*.
- DB confirms (synthesis agent re-queried): **18/18 E938 = 0 advances** (13 `compiled_no_advance`, 4 `compiled_partial`, 1 `disproven`). Calibrated probability of advancing the gap: **~1–2%**, barely above the 0.8% base rate.

---

## The crux: forward holds, converse is false

A "reduction of E938 to Mordell" requires the **converse**: that controlling `x²+w³=y²` would control all consecutive powerful 3-APs. That direction is **refuted** by an explicit, published, independently-reproduced counterexample with an **odd** first term, which the (always-even) `8kw³`/`8kx²` form cannot represent. Verdicts 2 and 3 (both 0.97) agree; the synthesis agent re-verified the triple's factorization and AP property from scratch.

What remains is only the **forward** map — and that map is the equation rescaled by `8k` (synthesis agent: residual `= 8k·(y²−x²−w³)`). It is a correct identity that parametrizes one special *shape* of AP, contributes nothing toward **consecutiveness** (E938's actual difficulty), and generates **non-consecutive** APs in general.

## Computational results (synthesis-agent re-verified)

| Check | Result |
|---|---|
| Counterexample `(149022674775, ...)` AP + all-powerful + n0,n2 odd | **Confirmed exactly** (`n0=3³·5²·13³·317²`, `n0≡7 mod 8`) |
| AP residual `2n1−(n0+n2)` under the form | `= 8k·(y²−x²−w³)` — **the equation itself** |
| Type-B excess `(b³−a³)²+(2ab)³−(b³+a³)²` | `= 4a³b³` — **SC7 algebra confirmed** |
| Deficit-feasibility roots of `r²−6r+1` | **`3±2√2`** confirmed → threshold `(3+2√2)^(1/3)≈1.79963` |
| F1, F2 forward map (powerful + AP + square middle) | **Both valid, exact** |
| E938 DB status | **18 total, 0 advances** (13 no-advance / 4 partial / 1 disproven) |

**New primitive base?** No — verdict 3 found no new primitive Mordell base appeared (still only `(6,15,21)` and `(45,302,427)`); the new consecutive APs past 1e11 are mostly **not Mordell-derived at all**.
**New counterexample?** Yes — a concrete, reproducible non-Mordell consecutive powerful 3-AP at `n0≈1.49e11` (refutes the reduction; does **not** itself resolve E938).

## Novelty & citations

- **FOLKLORE / KNOWN.** Core construction: **Golomb 1970** (Amer. Math. Monthly 77:848–852); **Walker 1976** (Fibonacci Quart. 14(2):111–116).
- **Decisive prior art:** **Chan 2022** (arXiv:2210.00281), Thm 3 contains EXP4's claimed-novel `(3+2√2)^m`, `x=8Y²`, `x+4=4X²` scaling verbatim; the genuine deep input (abc/Hall bound) is Chan's existing conditional result.
- **Most relevant current paper:** **van Doorn 2026** (arXiv:2605.06697) — `A_0/A_1/A_2` square-count taxonomy, the 18-triple count to 1e14, and (notably) **conjectures E938 is FALSE**. EXP4's reduction targets the opposite truth-value.
- EXP4 re-derived published results without citing them and rebranded an elementary identity as a "Mordell reduction." Notation fresh; mathematics not.

## Recommendation: **DO_NOT_SUBMIT**

1. The "reduction" (converse) is **false** — not a candidate theorem.
2. The forward map is **folklore** and produces only non-consecutive APs — it does not address E938's open core.
3. The framing invokes machinery (Hall/Coates-Wiles/elliptic curves) that **does not apply** to a genus-context infinite-solution surface.
4. A 19th submission is the same open problem reworded, **equivalent to the already-failed Pell framing** (MEGA7), against **18 prior 0-advance results** and a ~0.8% base rate.
5. E938 may well be **false** per the field's current leading conjecture, making a finiteness-oriented reduction the wrong bet entirely.

**Cleanup actions worth taking (independent of resubmission):**
- Relabel DB id 1312 (`yolo_e938_deep_stark`) from `disproven` → `compiled_partial`/`compiled_no_advance` (it negates no lemma; honest docstring only).
- Record the verified unconditional bound `d < 2√N + 2` + identity `n₁²=n₀n₂+d²` from id 1315 as a real (folklore) partial-progress artifact.
- Note in `false_lemmas`/notes that the `(8kw³,4ky²,8kx²)` converse is **refuted** by the odd-`n0` counterexample, to prevent re-exploration.

**If E938 is ever revisited:** pivot to the **van Doorn `A_2` / Pell `x²−7³y²=2`** angle and the *falsity* conjecture, not the Mordell relabel — but expect no advance from bare/fusion submission given the 18-for-18 record. This is beyond current reach.
