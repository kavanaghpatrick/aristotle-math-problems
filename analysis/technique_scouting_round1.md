# Technique Scouting Round 1 — Cross-Domain Inventory

**Agent:** S6 of 10 | **Date:** 2026-05-30 | **Budget consumed:** ~$15-30 across 5 debates

Five debates run via `scripts/debate_fusion.py` over the top 5 active fusion candidates, using the 6 templates I7 built. All 3 models (grok-4, gemini-3-pro-preview, codex/GPT-5.2) responded; no model failures. 2 rounds each.

---

## Summary Table

| Problem | Template | Named technique (single best) | Bridge / obstruction | Lane recommendation |
|---|---|---|---|---|
| **E672 k=4 ℓ=3** | bridge_lemma | **GHP 2009 Theorem 1.1 literature import** (Győry-Hajdu-Pintér, Compositio 145) | Bridge: import the existing theorem `∀ 3<k<35, no coprime AP cube`. NOT a math gap. | **NEITHER — problem likely already CLOSED**; verify GHP polarity in Lean file. |
| **E64 Erdős-Gyárfás** | obstruction_diagnosis | **No cross-domain unlocker found** — top 3 obstructions are: (1) sparse-cubic δ≥3 critical threshold, (2) accidental relator concatenation in Cayley constructions, (3) dyadic lacunarity in cycle spectra | Obstruction: Liu-Montgomery / Gao-Huo-Liu-Ma need δ ↑ ∞; downgrade to δ=3 leaks expansion control. Cayley disproof template fails due to identity-word leakage. | **BARE lane** — 10-year closure 8-15%. No fusion unlocker. Suggest narrow SAT search on cubic Cayley candidates ≤400 vertices as parallel track. |
| **E1003 φ(n)=φ(n+1) ∞-often** | technique_scout | **S-unit / Subspace Theorem stratification** (Evertse-Schlickewei-Schmidt 2002 Annals) — *as stratification engine*; with **Tao 2016 entropy decrement** for `(n, n+1)` multiplicative independence as cross-domain second pillar | Bridge: prove finiteness for fixed-support `(ω(n)=r, ω(n+1)=s)` via S-units. If finite for all `(r,s)`, infinitude requires unbounded support, pushing entropy/transference up. | **FUSION lane** — has a concrete intermediate target (fixed-support stratification theorem). Ready for sketch attempt. |
| **E1052 unitary perfect finite** | adjacent_analog | **Bilu-Hanrot-Voutier / Bang-Zsigmondy primitive divisor theorem** (Bang 1886, Zsigmondy 1892, BHV 2001 Math. Ann. 316) | Bridge: **support-closure lemma** — `∃K. no E1052 support graph has >K prime vertices`. Encode each `1+p_i^{a_i}` requirement as edge in directed prime-support graph; Zsigmondy forces leakage outside finite supports. | **FUSION lane** — strongest concrete bridge in this batch. Promote to sketch. |
| **E267 lacunary Fibonacci recip.** | technique_scout | **Parry-Schmidt Pisot β-expansion + φ-normalization transducers** (Parry 1960, Schmidt 1980, Frougny 1992) | Bridge: prove `lacunary sum of normalized φ-expansion atoms of 1/F_n cannot become eventually periodic` — converts irrationality (Archimedean) into a finite-state symbolic periodicity obstruction. | **FUSION lane** — validates Codex F8's Pisot β-shift conjecture. Strong unanimous unlocker pick. |

---

## Per-Problem Distillation

### 1. E672 k=4 ℓ=3 (bridge_lemma)

**Most surprising debate output:** Codex Round 2 reads the GHP 2009 paper and reports:
> "Győry-Hajdu-Pintér state Theorem 1.1 as: for `3 < k < 35`, the product of `k` consecutive terms in a coprime positive arithmetic progression is never a perfect power. Their equation is exactly `x(x+d)...(x+(k-1)d)=b y^n`, with `gcd(x,d)=1`; for our case take `k=4`, `b=1`, `n=3`."

If correct, **E672 at (k=4, ℓ=3) is NOT OPEN**. The whole framing as a fusion candidate may be a labeling error in `formal-conjectures/.../672.lean`. Codex's "Single Most Important Next Step": open `FormalConjectures/ErdosProblems/672.lean` and check whether the statement is the false direction (asking for a witness that doesn't exist).

Both Grok and Gemini converged in R2 on agreement with this finding. The "bridge lemma" is a literature import, not a math gap.

**Recommendation:** STOP working on E672 as a fusion candidate. Open the Lean file, check polarity, and import GHP 2009 Theorem 1.1 as the entire proof.

### 2. E64 Erdős-Gyárfás (obstruction_diagnosis)

**Most surprising debate output:** All three models REJECTED the "Cayley small-cancellation counterexample" route that the existing `analysis/research_fusion_erdos64.md` proposed. Codex stated:
> "In a Cayley graph, cycles correspond to all short identity words in the chosen generators, not just defining relators. Small-cancellation controls van Kampen diagrams and systoles; it does not by itself give modular control of every null word length."

This is the load-bearing claim of our prior fusion analysis (F5's note), and the debate killed it. Both Grok and Gemini accepted Codex's correction in R2.

Severity-ranked obstructions (consensus):
1. Critical-minimum-degree-3 barrier (Liu-Montgomery requires δ→∞)
2. Sparse-target / dyadic lacunarity (no infinite AP contains 2^k's)
3. Predominantly-cubic minimal counterexample (Carr 2026, arXiv:2605.22844)
4. Cayley/finite-quotient leakage (kills the counterexample template)

10-year closure probabilities: Grok 8%, Gemini 15%, Codex 12%. Mean: **~12%**.

**Recommendation:** BARE lane only. No cross-domain unlocker. Continue narrow SAT-search on cubic Cayley candidates up to 400 vertices as a Codex-style parallel track, not a fusion sketch.

### 3. E1003 φ(n)=φ(n+1) infinitely often (technique_scout)

**Most surprising debate output:** Codex argues that **standard Furstenberg recurrence is dead** for E1003 because the set has zero density, and the only ergodic-theoretic technique that could survive is RELATIVE transference (Green-Tao 2008, Conlon-Fox-Zhao). All three models initially proposed Furstenberg; the debate forced a downgrade.

Cross-domain finalists:
- **S-unit / Subspace** (Codex): formal Diophantine stratification engine. Top Bayesian pick (16%).
- **Entropy decrement** (Codex, Tao 2016): two-point multiplicative independence at `n, n+1`. Adjacent to Chowla two-point.
- **Sum-product / additive energy** (Codex, Bourgain-Katz-Tao 2004): mixes additive `+1` with multiplicative φ-structure.
- **Pila-Wilkie** (Gemini): André-Oort-style. Grok and Codex disputed: not o-minimal-definable unless rationality forces it.
- **Ratner / Furstenberg** (Grok, Gemini): proposed but Codex called both "metaphor, not bridge yet."

**The bridge lemma (consensus):** Fix `(r, s)` and classify solutions of `φ(n) = φ(n+1)` with `ω(n) = r, ω(n+1) = s`. If all finite, infinitude requires unbounded ω. If a "toric degeneracy" appears for some `(r,s)`, that becomes the new Fermat-tower candidate.

**Recommendation:** FUSION lane. Submit a sketch targeting the bridge: "For fixed `(r,s) ≤ (3,3)`, finitely many `n` with `φ(n)=φ(n+1)`, `ω(n)=r`, `ω(n+1)=s`." This is sub-quadratic in difficulty from infinitude and unlocks Aristotle.

### 4. E1052 unitary perfect numbers finite (adjacent_analog)

**Most surprising debate output:** Gemini coined the most useful term in the entire scouting round: **"UnitaryDependencyGraph"** — nodes = primes in support, edges `p_i → q` if `q | 1+p_i^{a_i}`. The unitary-perfect identity forces this graph to be a closed system (every required prime must already be a node). Codex extended this to **support-closure lemma**: ∃K. no E1052 support graph has >K vertices.

All three models converged in R2 on:
- BHV / Bang-Zsigmondy primitive divisors as the cross-domain ingredient
- Directed prime-support graph as the structural object  
- Wall (1972) closes fixed-k; bridge closes variable-k

**Concrete next step (Codex):** Build the support-valuation graphs for the 5 known unitary perfect numbers; classify possible one-prime extensions using valuation balance + Zsigmondy + LTE.

**Recommendation:** FUSION lane. Strongest concrete bridge in this batch. Submit a sketch: "Support-closure lemma for unitary perfect numbers — ∃K. ω(n) ≤ K for all unitary perfect n."

### 5. E267 lacunary Fibonacci reciprocals (technique_scout)

**Most surprising debate output:** Codex's R2 self-correction:
> "I changed my mind on one part of my Round 1 framing. I wrote that the key lemma should be about 'sparse signed φ-digit streams with support gaps tending to infinity.' That is too naive. Fact: the exact identity `1/F_n = sqrt(5) · φ^{-n} / (1 - (-φ^{-2})^n)` expands into exponents `(2j+1)n`, not only `n`. So the object is not a sparse digit stream; it is an infinite sum of periodic 'reciprocal atoms' with periods tied to `n_k`."

This refined the bridge from "sparse digit streams" to **"normalized φ-expansion atoms with period tied to n_k"** — a much more tractable formulation.

Cross-domain finalists:
- **Parry-Schmidt Pisot β-expansion + φ-normalization transducer** (Codex, Frougny 1992): converts Archimedean irrationality into symbolic finite-state periodicity. Bayesian top pick (37%).
- **Cobham-Durand automatic/substitutive rigidity** (Codex): Zeckendorf numeration as backbone.
- **p-adic Skolem-Mahler-Lech via Strassmann** (Codex): handles indices with `v_p(F_n)` isolation.
- **Pila-Wilkie** (Gemini): rejected by Codex — Fibonacci subsequences aren't o-minimal-definable.
- **Ledrappier-Young, Ratner** (Grok): rejected by Codex — Pisot companion is hyperbolic, not unipotent; no Ratner setup.

This is the cleanest convergence in the batch: all three models agree the answer lives in **β-shift symbolic dynamics on Q(φ)**, validating Codex F8's earlier Pisot β-shift conjecture exactly.

**Recommendation:** FUSION lane. Submit a sketch targeting the symbolic bridge: "Lacunary sum of φ-normalized atoms of 1/F_{n_k} with n_{k+1}/n_k ≥ c > 1 cannot be eventually periodic in the φ-base." This is a hard but well-defined symbolic claim.

---

## Lane Routing After Round 1

| Lane | Problems |
|---|---|
| **CLOSE-OUT (verify literature)** | E672 k=4 ℓ=3 |
| **BARE lane** | E64 Erdős-Gyárfás |
| **FUSION lane (ready for sketch)** | E1003 (fixed-support stratification), E1052 (support-closure lemma), E267 (φ-normalization periodicity) |

---

## Cost Accounting (approximate)

| Problem | Debate text (chars) | Rounds | Models | Estimated cost |
|---|---|---|---|---|
| E672 | 21,343 | 2 | 3 | ~$3 |
| E64 | 33,172 | 2 | 3 | ~$5 |
| E1003 | 37,324 | 2 | 3 | ~$5 |
| E1052 | 32,629 | 2 | 3 | ~$5 |
| E267 | 42,400 | 2 | 3 | ~$6 |
| **TOTAL** | **166,868** | — | — | **~$25** |

Cost is rough — exact figures depend on per-model token pricing. All under budget ($50-100 target).

---

## The Single Most Surprising Output

**E672 may not be open.** Codex's R2 literature audit (with arXiv URL) claims Győry-Hajdu-Pintér 2009 Theorem 1.1 unconditionally settles the (k=4, ℓ=3) case. If true, our entire E672 sub-program (slot 734, slot 738, the Frey curve attempts) was attempting to reprove a 2009 result. The action: open `FormalConjectures/ErdosProblems/672.lean` and check whether the formal statement matches GHP's polarity, and whether the prime-support hypothesis covers all coprime APs at this parameter pair.

This is the kind of finding that justifies running scouting debates BEFORE more solver iterations.

---

## Documentation

- Raw debate transcripts (all 5): `/Users/patrickkavanagh/math/research_fusion/runs/erdos_{672,64,1003,1052,267}/debates/`
- Context dossiers used:
  - Pre-existing: `analysis/research_fusion_erdos{672,64}.md`
  - **NEW (created this round)**: `analysis/research_fusion_erdos{1003,267,1052}.md`
- Summary: this file.
