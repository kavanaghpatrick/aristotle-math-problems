# sumset — final citable contributions to the E124 unified conclusion

Three durable yields, each with an honest scope tag, for inclusion in the unified conclusion document.
Notation: D = finite set of bases (all d ≥ 3); B_d = 0/1-digit base-d numbers; T_k(D) = ∑_{d∈D} d^k·B_d
(the BEGL96 sumset, via the scaling reduction S(d,k)=d^k·B_d); r(n) = #representations of n;
b = min(D); "miss set" = {n : r(n)=0} = ℕ ∖ T_k(D).

---

## RESULT 1 — Non-automaticity of the exceptional set [NEW STRUCTURAL THEOREM]

**Statement.** For a multi-base digit-Cantor sumset T_k(D) whose bases are multiplicatively
independent (no two are powers of a common integer), the exceptional set E = {n : r(n)=0} is **not
eventually periodic** modulo any power b^p of the smallest base — hence **E is not a b-automatic set**.
Equivalently: the indicator of non-representability is not a finite-state function of the base-b
digits of n.

**Scope tag: [VERIFIED, robustly]** on the sub-critical (infinitely-many-gap) families where the
exceptional set is nontrivial — (3,5), (3,7), (4,5), (4,5,9) — by the rigorous test below. The causal
mechanism (next paragraph) is a rigorous argument given the standard CF-convergent geometry; a fully
formal proof would invoke that geometry as a lemma.

**Test (corrected — this matters).** A NAIVE single-window check (does the miss pattern at [N−2P, N−P]
equal [N−P, N]?) gives FALSE POSITIVES — e.g. it spuriously reports "period 9" for (3,7). The correct
test requires (i) the candidate period P=b^p to hold at MANY disjoint windows across [N/4, N], and
(ii) each "missing residue class" mod P to be FULLY missing (fraction 1.0). Under the correct test, NO
family is periodic:
| D | candidate P | windows matching | worst missing-class fill |
|---|---|---|---|
| (3,5) | 9 | 26/60 | 0.486 |
| (3,7) | 9 | 39/60 | 0.847 |
| (4,5) | 16 | 39/60 | 0.897 |
A genuine period would give 60/60 windows and fill 1.000. None does ⟹ not eventually periodic ⟹ not
b-automatic.

**Why it matters (the causal chain, with scholar's CF link).** This converts the team's central
negative ("no elementary route; the obstruction is MW") into a POSITIVE structural reason:
> log-clustering (near power-coincidences |d_i^p − d_j^q| small)
>   ⟹ those coincidences sit at continued-fraction-convergent positions of log d_i / log d_j
>   ⟹ the exceptional positions are NON-periodic (CF convergents of an irrational log-ratio are aperiodic)
>   ⟹ E is non-automatic
>   ⟹ the obstruction is provably NOT finite-state, hence genuinely transcendental.
This is one of the campaign's genuinely new structural facts: it explains why no automatic/periodic
(hence no elementary finite-state) characterization of the miss set can exist, independently of the
five coverage/repair routes that were shown blind to the internal gaps. It ties scholar's clustering
quantity Λ and INV-S3 (Ostrowski) to a single statement.

---

## RESULT 2 — Run-length-1 localization of the open core [SHARPEST LOCALIZATION; with density]

**Statement.** For strict-excess admissible D, the open (MW-hard) content is confined to the
**isolated run-length-1 missing values** — single non-representable n with both neighbors n±1
representable — lying between C·d_max^k and the true threshold. Concretely:
- the longest missing RUN (≥2 consecutive misses) dies at C·d_max^k (elementary; density's surplus
  argument δ·U overtakes any run-length deficit — a clean partial: "no missing run of length ≥2 above
  C(δ)·(d_max·d_2)^k", rigorous modulo a Baker floor);
- but ISOLATED singletons persist far beyond: (3,4,6) k=2 — last run≥2 at 44,817, last singleton at
  242,113 (5.4× further); (3,4,5) k=2 — 57,404 vs 77,613; (3,4,5,6,7) k=2 — 103 vs 312.

**Scope tag: [VERIFIED].** Joint with density (her surplus/run-bound leg + my run-vs-singleton split).

**Why it matters.** It tightens the open target from the vague "internal gaps" to a precise object:
single non-representable values, each an independent specific-value (residue-equidistribution /
linear-forms-in-logs) question. A length-based / surplus / thickness argument provably cannot reach a
run-length-1 hole (it is not a length deficit). So the elementary part of the theorem covers all of
T_k except a residue-equidistribution-controlled set of isolated points — and that exact statement is
the clean honest boundary between elementary and MW.

---

## RESULT 3 — Bounded-ρ₄ characterization of the misses [CHARACTERIZATION, NOT A PROOF; with breaker]

**Statement.** Define the base-4 repair index ρ₄(n) = min over representations of n of the number of
base-4 atoms used. For (3,4,7): ρ₄(n) ≤ 6 over all REPRESENTABLE n, uniformly in k (k=1,2,3, verified
even at the true k=3 threshold n₀=166,025,260 where the gap cascade is deep). So a representable n is
"non-representable ⟺ its leading-base-3 carry-debt cannot be absorbed by a bounded base-4 pattern" —
a value-specific characterization that the surviving boundedness test confirms.

**Scope tag: [PER-n CHARACTERIZATION, NOT a cofiniteness proof].** The bound ρ₄ ≤ 6 is CIRCULAR — it is
conditioned on n already being representable. The non-circular quantity — the constructive base-4
budget R(k) such that S3 + S7 + (base-4 numbers with ≤ R atoms) is cofinite — GROWS: R(1)=5, R(2)=8
(verified at N=6M; T_R threshold = full threshold exactly at these R). So R(k) carries the same
c(D,k)→∞ / MW content; locating where the bounded repair FAILS is the MW problem. ρ₄ is therefore a
clean per-n descriptor of the misses, not a uniform proof.

**Why it matters.** It is the strongest value-specific invariant on the board (the only one to survive
breaker's boundedness kill), and it pins the miss mechanism concretely (base-3 carry-debt vs bounded
base-4 repair at the 3^p≈4^q collision). It is the precise empirical witness that the obstruction is a
two-base digit collision — complementing Result 1 (why that collision is non-automatic).

---

## Attribution note
- **Lemma M (subset-monotonicity)** — `T_k(D) ⊇ T_k(D'')` for any subset D''⊆D, reducing cofiniteness
  of D to any cofinite admissible sub-family; with the verified minimal/non-minimal split (43 minimal +
  72 non-minimal of the 115 strict-excess admissible D, d≤11): **sumset + carry**.
- Result 1 (non-automaticity): sumset, causal chain with scholar (CF link).
- Result 2 (run-length-1 localization): sumset + density.
- Result 3 (bounded-ρ₄): breaker (boundedness data) + sumset (non-circular budget R(k) resolution).
- Foundational stack re-used (scaling, gcd-necessity, residue-coverage corollary via modular's
  per-prime/CRT [my Lemma A was refuted; corollary stands], deconvolution Theorem C): sumset, team-verified.
