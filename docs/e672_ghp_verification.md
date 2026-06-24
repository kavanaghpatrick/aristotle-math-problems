# E672 GHP 2009 Verification — Verdict A: CONFIRMED SOLVED

**Agent:** E1 of 10 | **Date:** 2026-05-30
**Verdict:** **(A) CONFIRMED SOLVED** — formal-conjectures `Erdos672With 4 3` (positive integers) is fully closed by the existing literature, both unconditionally.

---

## 1. The formal-conjectures statement (exact)

From `/Users/patrickkavanagh/math/formal-conjectures/FormalConjectures/ErdosProblems/672.lean`:

```lean
def Erdos672With (k l : ℕ) : Prop :=
  ∀ (s : Finset ℕ), s.card = k → ∀ᵉ (n > 0) (d > 0), n.gcd d = 1 →
    Set.IsAPOfLengthWith s k n d → ∀ q, ∏ i ∈ s, i ≠ q ^ l
```

Specialization `Erdos672With 4 3` asks: for all **positive** integers n, d with gcd(n,d)=1, the product n(n+d)(n+2d)(n+3d) is never a perfect cube.

The Lean file lists:
- (4, 2) Euler — `solved` lemma `variants.euler`
- (5, 2), (3, 3), (3, 4), (3, 5) Obláth — `solved` lemma `variants.oblath`
- (k=4, ℓ=3) is **not listed as solved** in the file — this is the "open" target.

But the registry is incomplete: the (k=4, ℓ=3) case has been settled in print since 2006.

---

## 2. The actual settling result (NOT GHP 2009)

**Bennett, Bruin, Győry, Hajdu (2006)** — *Powers from products of consecutive terms in arithmetic progression*, Proc. London Math. Soc. (3) **92**, 273–306.

**BBGH Theorem 1.1:** *The product of k consecutive terms in a coprime positive arithmetic progression with 4 ≤ k ≤ 11 can never be a perfect power.*

- Unconditional. No abc dependency.
- Hypothesis: positive integers, gcd(n,d)=1, k in {4,…,11}, exponent ℓ ≥ 2.
- Covers (k=4, ℓ=3) directly. Provenance: cases k=4, 5 are credited to **Győry, Hajdu, Saradha** within BBGH.
- Method: Frey curves + level-lowering + modularity (Bennett-Skinner style).
- PDF: https://personal.math.ubc.ca/~bennett/BBGH.pdf

**Hajdu, Tengely, Tijdeman (2009)** — *Cubes in products of terms in arithmetic progression*, Publ. Math. Debrecen **74** (1–2), 215–232.

**HTT Theorem 2.1 (verbatim from the paper):**
> Suppose that (n, d, k, y) is a solution to equation (2) [i.e., n(n+d)…(n+(k−1)d) = y³] with b=1 and k < 39. Then we have (n, d, k, y) = (−4, 3, 3, 2), (−2, 3, 3, −2), (**−9, 5, 4, 6**), (**−6, 5, 4, 6**).

- All four exceptional solutions have **n < 0**.
- For n > 0, d > 0, gcd(n,d)=1, k=4: no solutions. Settles `Erdos672With 4 3`.
- Method: extends [1] (= BBGH 2006) with Selmer cubic equations + elliptic Chabauty.
- PDF: https://pub.math.leidenuniv.nl/~tijdemanr//hateti.pdf

**Győry, Hajdu, Pintér (2009)** — *Perfect powers from products of consecutive terms in arithmetic progression*, Compositio Math. **145**(4), 845–864.

**GHP Theorem 1.1 (per abstract/summary):** For positive integers x, d, k with gcd(x,d)=1 and 3 < k < 35, the product x(x+d)…(x+(k−1)d) is never a perfect power.

- Unconditional. Extends BBGH from k ≤ 11 to k ≤ 34.
- Also covers (k=4, ℓ=3), but is **redundant** for this case — BBGH already covered it.
- Cambridge URL: https://www.cambridge.org/core/journals/compositio-mathematica/article/AABF84B6AEDB5FF9A80D357180CE837D

---

## 3. Gap analysis (overlap vs distinct)

| Source | k=4, ℓ=3, n>0, d>0, gcd=1 | abc-conditional? | Notes |
|---|---|---|---|
| Euler (1738) | — | — | k=4, ℓ=2 only |
| Obláth (1951) | — | — | k=3 and k=5, ℓ=2 |
| Erdős-Selfridge (1975) | — | — | d=1 case only |
| Győry-Hajdu-Saradha (BBGH ref) | **SETTLES** | No | k=4,5 cubes/powers, in BBGH |
| **BBGH 2006** | **SETTLES** | **No** | 4 ≤ k ≤ 11 all powers, Frey/modular |
| **HTT 2009** | **SETTLES** | **No** | k < 39 cubes, b=1, only n<0 exceptions |
| GHP 2009 | settles (redundantly) | No | 3 < k < 35 all powers, extends BBGH |

The formal-conjectures target `Erdos672With 4 3` is **fully covered, redundantly, by three independent results**. None depend on the abc conjecture. None require the b=1 hypothesis to restrict anything beyond what `Erdos672With` already restricts (the Lean statement bakes in n>0, d>0, gcd(n,d)=1, which matches the b=1, positive-integer setting precisely).

The S6 LLM-scouting consensus ("GHP 2009 Theorem 1.1 unconditionally settles E672 k=4 ℓ=3") was **directionally correct** but **misattributed**: GHP 2009 does cover it, but the historical credit belongs to **BBGH 2006** (with the k=4 case credited there to Győry-Hajdu-Saradha). HTT 2009 is the cleanest standalone reference for the (k=4, ℓ=3) cube-only case.

No "b=1 restricts to coprime-AP subcase only" issue: the Lean statement already restricts to gcd(n,d)=1, which is the b=1 case (b is the largest-prime-divisor cofactor in the general Erdős-Selfridge equation n(n+d)…(n+(k-1)d) = b·y^ℓ; setting b=1 means "perfect cube" rather than "almost cube").

---

## 4. Verdict: **(A) Confirmed Solved**

`Erdos672With 4 3` is **closed** in the published mathematical literature, unconditionally, since 2006 (BBGH) and again in 2009 (HTT, GHP). Any AI proof attempt on this target is **duplicating known results** — at best a formalization exercise, never a novel contribution.

The formal-conjectures Lean file is **stale**: it should list (k=4, ℓ=3) as solved by BBGH 2006, with HTT 2009 as the cleanest cube-specific citation.

---

## 5. Implications for the math pipeline

### Direct
- E672 at (k=4, ℓ=3) is **NOT an open gap**. Remove from S2 portfolio.
- All four prior Aristotle submissions (slot698, erdos672_ap_resub, erdos672_l3_v2, erdos672_l3_bare) targeted a closed problem. None achieved `target_resolved=1` and none should — the target is non-novel.
- The slot734/738 work and the Frey-curve dossier (`research_fusion_erdos672.md`) have indeed been **duplicating a 16-year-old paper** (BBGH 2006, with the relevant k=4 cubes case originally due to Győry-Hajdu-Saradha that BBGH cites).

### LLM-scout reliability
- All 3 LLMs (Codex/Grok/Gemini) converged on GHP 2009 as the killer, which is correct-but-suboptimal: the *earliest* killer is BBGH 2006.
- Codex's "b=1" flag was a real concern — but resolved as a non-issue once we read the actual statements. The "b=1" hypothesis matches the Lean statement's "perfect cube" target (vs. "almost cube" b > 1).
- Net signal: LLM lit-search is **trustworthy for confirming a target is dead**, but should be cross-checked for earliest credit. For *finding open gaps*, LLM scouts remain useful screens but every fusion-candidate must pass a literature kill-list audit before sketch submission.

### Action items
1. **(DONE)** Append `erdos_672` entries to `analysis/literature_kill_list.csv` with BBGH 2006 + HTT 2009 citations.
2. **(TODO by S2)** Remove E672 from the portfolio. Mark `research_fusion_erdos672.md` as "target closed pre-pipeline, do not submit."
3. **(TODO by MEMORY.md keeper)** Add "Erdős 672 (k=4, ℓ=3): closed unconditionally by BBGH 2006 / HTT 2009 — never sketch" to FALSIFIED APPROACHES.
4. **(TODO by formal-conjectures pipeline)** File upstream patch noting that `Erdos672With 4 3` should be marked `category research solved` with `[BBGH2006, HTT2009]` references — though this is a meta-action on the upstream repo, not internal pipeline state.
5. **(TODO if scope expands)** Aristotle could legitimately attempt the **k=4, ℓ ≥ 36** range or **k ≥ 39, ℓ=3** range (genuinely open per GHP/HTT bounds), but these are likely too hard.

---

## 6. References

- M. A. Bennett, N. Bruin, K. Győry, L. Hajdu. *Powers from products of consecutive terms in arithmetic progression*. Proc. London Math. Soc. (3) **92** (2006), 273–306. PDF: https://personal.math.ubc.ca/~bennett/BBGH.pdf
- L. Hajdu, Sz. Tengely, R. Tijdeman. *Cubes in products of terms in arithmetic progression*. Publ. Math. Debrecen **74** (2009), 215–232. PDF: https://pub.math.leidenuniv.nl/~tijdemanr//hateti.pdf
- K. Győry, L. Hajdu, Á. Pintér. *Perfect powers from products of consecutive terms in arithmetic progression*. Compositio Math. **145**(4) (2009), 845–864. DOI: 10.1112/S0010437X09004114
- formal-conjectures: `/Users/patrickkavanagh/math/formal-conjectures/FormalConjectures/ErdosProblems/672.lean`
- Prior in-house analysis: `/Users/patrickkavanagh/math/analysis/research_fusion_erdos672.md` (Section A item 1 already flagged "the problem is **arguably already solved** by Győry-Hajdu-Pintér 2009 — needs literature verification" — now verified).
