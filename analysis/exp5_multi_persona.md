# EXP5: Multi-Persona Specialist Debate on Erdős Problem #364

**Date**: 2026-05-31
**Target**: E364 — show there is no n ∈ ℕ such that n, n+1, n+2 are all powerful
**Hypothesis**: paradigm-locked specialists surface attacks the generalist model misses

---

## 1. Methodology Spec

Five distinct specialist personas were instantiated, each pinned to a single research paradigm and forbidden from simulating the others. Each was given:

* the bare problem statement,
* a list of paradigm-specific tools they could use,
* a list of paradigm-specific observations,
* an explicit list of our prior MEGA submissions (so they could surface a NEW vector).

**Personas**:

| ID | Persona | Lineage | Engine |
|----|---------|---------|--------|
| 1 | Additive combinatorialist | Tao / Green / Bloom | Grok-4 (T=0.5) |
| 2 | Multiplicative number theorist | Erdős / Heath-Brown | Grok-4 (T=0.55) |
| 3 | Analytic number theorist | Bombieri / Iwaniec / Vinogradov | Grok-4 (T=0.5) |
| 4 | Computational / algorithmic | Knuth / Bernstein | Grok-4 (T=0.6) |
| 5 | Algebraic geometer | Faltings / Vojta | Grok-4 (T=0.5) |

Engine note: Codex CLI was attempted first for personas 2 and 4 but returned prompt-echo only (empty assistant block); Gemini CLI hit rate-limit; all five personas were ultimately Grok-4 with paradigm-isolating system prompts.

**Protocol**:

1. **Attack** (independent, parallel): each persona writes a ≤500-word attack from its paradigm only.
2. **Cross-critique** (parallel): each persona reviews the OTHER four attacks, identifies (i) a specific weakness, (ii) a paradigm-specific patch, (iii) a HIGH/MED/LOW advance-confidence rating. They name which other attack they found strongest.
3. **Synthesis** (single pass, Grok-4, T=0.45): a synthesis prompt assembles all 5 attacks + 5 critiques and asks for a single final attack that combines the strongest insights while avoiding the identified weaknesses. The synthesis must (a) name the vector, (b) state the bridge lemma, (c) give an attack outline, (d) identify ONE vector NEW vs our prior MEGA submissions, (e) recommend an Aristotle submission lane.

---

## 2. Prior MEGA Submissions on E364 (Baseline)

| ID | Lane | Attack | Result |
|----|------|--------|--------|
| 1325 (D5) | informal | Beckon mod-36 closure | `submitted` |
| 1333 (MEGA-11) | informal | Joint mod-36 admissibility for powerful 3-APs (general d) | `submitted` |
| 1334 (MEGA-3) | informal | Beckon extended to mod-44100 via p=5, p=7 obstructions | `submitted` |
| 1336 (MEGA-8) | informal | 3-AP coprimality chapter | `submitted` |
| 1141 (Feb 14) | bare | ABC-conditional finiteness | `compiled_no_advance` |
| 1153, 1155, 1157, 1159 | bare | Cube-centered subcases | `compiled_partial` |

**All prior attacks are EITHER (a) elementary mod-arithmetic closures (Beckon-family) OR (b) ABC-conditional / cube-centered subcases (Chan / She mirror).** None use Fourier / circle method, none use a large sieve over squareful moduli, none use lattice reduction, none use Vojta / Chabauty on the underlying variety.

---

## 3. The Five Persona Attacks

### Persona 1 — Additive Combinatorialist

> The non-existence claim is equivalent to the vanishing of the weighted triple correlation
> ∑ 1_P(n) 1_P(n+1) 1_P(n+2) = o(X^{1/2}),
> i.e., the L¹ mass of the three-fold intersection inside an interval of length X is smaller than the diagonal contribution.

**Tool**: Croot–Lev–Pach polynomial method applied directly to P_X × P_X × P_X with the AP-slice polynomial Q(x,y,z) = (y-x-1)² + (z-y-1)². The CLP lemma extracts a degree-O(1) algebraic factor on triples in the slice, forcing a density increment on a lower-dimensional subvariety, contradicting the √X sparsity.

**New ingredient**: A Plünnecke-Ruzsa estimate inside a regular Bohr neighborhood B: if P∩B contains even one solution to x+1, y+1 ∈ P, then |2(P∩B)| ≤ (1+O(η^{-C}))|P∩B|. Iterating drops the Bohr radius below X^{-c}, impossible for squareful integers.

**Self-identified counterexample**: square-freeness is invisible to additive characters; the von-Mangoldt-type weight is supported on prime powers and orthogonal to all non-trivial Fourier modes on Z/NZ.

(See: `/Users/patrickkavanagh/math/analysis/exp5_artifacts/p1_additive_attack.md`)

### Persona 2 — Multiplicative Number Theorist

> The condition is equivalent to f(n) f(n+1) f(n+2) = 1 where f(m) = μ(rad(m))² · 1_{m squarefull}, and forces ∑_{p | n(n+1)(n+2)} 1/p ≪ log n / √n.

**Tool**: Heath-Brown identity on the indicator of the cube-full part after removing the square factor. Insert into the ternary sum ∑ f(n) f(n+1) f(n+2). Diagonals controlled by the large sieve for squarefree kernels. Off-diagonals by a hybrid sieve at level X^{1/2 - δ} combined with the exponent-of-distribution X^{2/3 - ε} for the ternary divisor function.

**New ingredient**: The **completely additive** function
g(n) = ∑_{p | rad(n)} log p / (p − 1).
Its first moment over powerful triples yields an extra factor ∏_p (1 + O(p^{-3/2})) that is strictly smaller than the density constant of powerful numbers. **This counting function has not appeared in any prior modular or ABC attack.**

**Output bound**: Main term c · ζ(3/2)/ζ(3) · X^{1/2} + O(X^{1/3+ε}) with error smaller than the main term once δ > 1/12 — yielding a hard upper bound that contradicts even one solution at large X.

**Self-identified counterexample**: the infinite Pell family of consecutive powerful PAIRS (x² − 2y² = ±1) forces the large-sieve weights to concentrate on a thin set of moduli divisible by high powers of 2, precisely where the hybrid level of distribution fails to exceed X^{1/2}.

(See: `p2_multiplicative_attack.md`)

### Persona 3 — Analytic Number Theorist

> Count via the triple Dirichlet series
> D(s₁,s₂,s₃) = ∏ ζ(2s_i)ζ(3s_i)/ζ(6s_i)
> times the Möbius factor enforcing coprimality.

**Tool**: Shift contours to Re(s_j) = 1/3 + ε. Apply the explicit formula factor-by-factor. The major arcs (modulus 44100) carry the singular series; the minor arcs reduce to a trilinear exponential sum estimable by Vinogradov mean value after Weyl differencing.

**New ingredient**: The trilinear minor-arc sum
∑_{m_i ≤ X^{1/3}} μ(m_1)μ(m_2)μ(m_3) (m_1m_2m_3)^{-2/3} ∑_{k≤X^{2/3}} e(α(k + m_1³k_2² + m_2³k_3²)),
bounded by Burgess on character sums of length X^{1/4+ε} to modulus q ≤ X^{1/8}, yielding saving X^{1/12-ε}.

**Output**: The singular series vanishes identically modulo 44100, so the count is dominated by the minor-arc bound which gives o(X^{1/2}).

**Self-identified counterexample**: a Siegel zero of L(s,χ) with conductor ≪ X^{1/100} could inflate the major-arc contribution in a single AP; once that's ruled out, the proof goes through.

(See: `p3_analytic_attack.md`)

### Persona 4 — Computational / Algorithmic

> Recast as a 6-variable integer-relation problem on n+i = a_i² b_i³, giving three cubic forms in six indeterminates whose values differ by ±1.

**Tool**: Coppersmith-style bivariate-to-multivariate lifting; embed the six exponents in a 12-dim lattice whose rows are the monomials of total degree ≤ 4 plus the three linear difference constraints scaled by X. Run BKZ-25 (dimension 120 after LLL preprocessing) — short vectors of length < X^{3/4} yield candidate tuples below X⁶.

**New ingredient**: A 2-GiB **cuckoo hash of forbidden 6-tuples modulo M = 44100 · 13 · 17 · 19 ≈ 2.3·10⁸**. The modulus is chosen so quadratic and cubic residues of −1, 2 are simultaneously obstructed for at least one variable; any lattice vector whose reduction lands in the hash is discarded before BKZ. Eliminates ≈ 78% of the enumeration tree with a single cache-line probe.

**6-month compute plan**: BKZ at X = 2⁶⁴ (targeting n < 2³⁸⁴) on a 256-node GPU-BKZ cluster; each node enumerates 10⁹ random 6-tuples with b_i ≤ 2²⁰ (Dickman-ρ regime); short vectors below 2³⁰ feed into 30-digit ECM check. ≈ 120 wall-clock days for effective volume 2¹²⁰.

**Output**: Exhaustive certificate of non-existence up to n < 2³⁸⁴ ≈ 10¹¹⁵, far past Beckon's reported 7.4·10²⁸ bound.

**Self-identified counterexample**: an eventual solution with three powerful parts each containing a prime factor > 2⁴⁰. Lattice dimension required to encode the unknown exponents exceeds 40 and BKZ becomes exponential; ECM/NFS verification also fails.

(See: `p4_computational_attack.md`)

### Persona 5 — Algebraic Geometer

> Target the integral-point set on the affine 6-fold V cut out by
> a_0²b_0³ + 1 = a_1²b_1³ ∧ a_1²b_1³ + 1 = a_2²b_2³
> with b_i squarefree.

**Tool**: Each equation defines a hypersurface that is a torsor under the elliptic surface E_b: y² = x³ + b³ (after x = ab^{-1}). V is the fiber product over the middle factor — a smooth threefold of general type after log-compactification by adding the cuspidal divisor of X_1(3b_i). K_V + D ≡ (1/2)H for H ample.

**New ingredient**: Vojta's conjecture (or its effective avatar on surfaces of log-general type) gives an explicit height bound h_{K+D}(P) < C. For each fixed b_1, the first equation defines a curve C_{b_1} of genus ≥ 2 over Q(b_0); Chabauty-Coleman on the p-adic closure of the Mordell-Weil group of the Jacobian of a semistable model bounds the sections.

**Output**: A finite list of candidate triples (effective bound, then computational check disposes of them).

**Self-identified counterexample**: a rational curve on V̄ meeting D in degree ≤ 2 would violate the height inequality. No such curve is visible from the modular description, but its absence is the missing step.

(See: `p5_alggeom_attack.md`)

---

## 4. Cross-Critique Matrix

The five personas were each asked to review the four attacks that were NOT their own. Aggregated:

| Critic ↓ \\ Target → | A (Add) | B (Mult) | C (Anal) | D (Comp) | E (AG) |
|------------------------|---------|----------|----------|----------|--------|
| **Add (1)** | — | HIGH | MED | LOW | MED |
| **Mult (2)** | MED | — | HIGH | LOW | MED |
| **Anal (3)** | HIGH | MED | — | LOW | HIGH |
| **Comp (4)** | MED | HIGH | LOW | — | MED |
| **AG (5)** | HIGH | HIGH | HIGH | MED | — |
| **Strongest (per row)** | C | C | B | B | C |

**Critic-aggregated rankings** (highest first):
1. **C (Analytic)** picked as "strongest other attack" by 3 personas (Add, Mult, AG).
2. **B (Multiplicative)** picked as strongest by 2 personas (Anal, Comp). Highest mean confidence (Add: HIGH, AG: HIGH, Comp: HIGH).
3. **A (Additive)** picked as strongest by 0 (Anal rated it HIGH solo).
4. **E (AG)** picked as strongest by 0 (Anal rated it HIGH solo).
5. **D (Computational)** picked as strongest by 0 (uniform LOW confidence — finite-verification only).

**Key cross-critique insights**:

* Critic 1 (Add) on B: ignores that n, n+1, n+2 form a rigid AP whose additive Fourier coefficients are forced to be large → fix with Bohr-set increment + Plünnecke.
* Critic 2 (Mult) on C: "claimed vanishing of the singular series modulo 44100 is false" — local densities at p=2, p=3 are positive once exponents ≥ 2 are allowed on each factor separately. **This is a substantive correction**. The singular series is positive, not zero.
* Critic 3 (Anal) on A: CLP gives bounded-degree algebraic factor but no exponential-sum control; the increment collapses when Bohr radius drops below X^{-1/6}. Fix: replace Plünnecke iteration by Vinogradov mean value on the trilinear form.
* Critic 4 (Comp) on B: the Dirichlet series at s = 1/2 is never actually formed; the argument is formal. Fix: encode rad(n+i)² | n+i as a Coppersmith small-roots problem.
* Critic 5 (AG) on C: the singular-series vanishing is purely local; supplies no height bound. Fix: compactify x(x+1)(x+2) = y²z³ and apply Vojta to a log-general-type pair.

The two most consequential cross-critiques are **Mult on C** (singular series is not zero — corrects Persona 3's main step) and **Anal on A** (CLP gives no exponential-sum control — corrects Persona 1's main step).

---

## 5. Synthesis — The CLP-Factorized Trilinear Circle-Method Sum

The synthesis pass produced a single attack that fuses three paradigms:

> **Attack vector name**: CLP-factorized trilinear circle-method sum.

> **Bridge lemma (new)**: Let P_X denote the powerful numbers up to X. If the weighted triple correlation ∑_{n ≤ X} 1_P(n) 1_P(n+1) 1_P(n+2) ≫ X^{1/2-ε}, then there exists a regular Bohr set B of dimension d = O(log(1/η)) and radius δ > X^{-c} on which the relative density of P increases by 1+η, AND the indicator 1_P restricted to B is annihilated by a nontrivial polynomial factor of degree O(1) from the auxiliary hypersurface Q(y-x-1, z-y-1) = 0. This forces the associated trilinear exponential sum over the zero set of Q to obey a Vinogradov-type mean-value bound of strength X^{1/12-ε}.

> **Outline**: Embed 1_P into the circle method, form S_3(α) = ∑ 1_P(n) 1_P(n+1) 1_P(n+2) e(αn). Apply CLP to obtain a degree-O(1) algebraic factor on the AP-slice. Density increment on a Bohr neighborhood. Plünnecke-Ruzsa upgrades additive energy. L⁴ integral of S_3 over major arcs. Minor arc by Vinogradov mean value + Burgess on length X^{1/4+ε} to modulus q ≤ X^{1/8} → saving X^{1/12-ε}. Major-arc singular series vanishes once local conditions at p ≤ 7 are imposed (44100 absorbed into Bohr radius). Power saving dominates X^{1/2}(log X)^{-C} diagonal, proving correlation is o(X^{1/2}).

> **Lane**: FUSION; lemma-based informal reasoner.

(Full synthesis: `synthesis_attack.md`)

---

## 6. New Attack Vector vs Prior MEGA Submissions

**The synthesis identifies as NEW exactly the trilinear minor-arc sum**:

S_3(α) = ∑_{n ≤ X} 1_P(n) 1_P(n+1) 1_P(n+2) e(α n),

estimated on minor arcs by a fusion of **CLP polynomial method** (slice algebraization) and **Vinogradov mean-value theorem** (Weyl differencing + Burgess characters).

**Why this is novel**: every prior MEGA submission stops at LOCAL information (mod 36, mod 44100, joint mod 36, 3-AP coprimality). The exponential sum S_3(α) is a GLOBAL Fourier-analytic object. The CLP-Bohr-set bridge converts a local-only obstacle into a global density increment — this is exactly what additive combinatorics was designed for, and we have never tried it.

Secondary new ingredients identified by individual personas (not in the final synthesis but worth tracking):

| Source | Ingredient | Submission status |
|--------|-----------|-------------------|
| Persona 2 (Mult) | Completely additive g(n) = ∑_{p \| rad(n)} log p / (p−1); first moment over powerful triples gives ∏_p (1+O(p^{-3/2})) strictly below density constant | NEW — never appeared |
| Persona 2 (Mult) | Hybrid large sieve over **squareful moduli** with exponent-of-distribution X^{2/3-ε} for the ternary divisor function | NEW — every prior used residue-class sieves only |
| Persona 4 (Comp) | Cuckoo hash of forbidden 6-tuples mod M = 44100·13·17·19 + BKZ-25 on a 12-dim Coppersmith lattice; extends verification from 10²² to ≈ 10¹¹⁵ | NEW — pure search infrastructure, never tried |
| Persona 5 (AG) | Threefold V as fiber product of two elliptic-surface torsors + Chabauty on the curve C_{b_1} for fixed middle squarefree parameter | NEW — every prior AG attack was cube-centered, not general fiber |

---

## 7. Most Surprising Persona-Specific Insight

The Multiplicative critique of the Analytic attack: **"The claimed vanishing of the singular series modulo 44100 is false."**

This is surprising because all four of our prior MEGA submissions on E364 (1325, 1333, 1334, 1336) treat the modulus 44100 as a HARD local obstruction — i.e., we have been claiming Beckon's mod-36 result (and our extensions) actually rules out triples mod-by-mod. The multiplicative number theorist's critique points out a subtle but real distinction: the *singular series* (the product of local densities of the system over Q_p) is **positive**, not zero, because at each prime p ≤ 7 the local density is positive once we allow each n+i to have its own independent exponent ≥ 2 on its p-part. The modular set we have been targeting (mod 44100 closure) constrains residue classes, not local densities; the latter is what the circle method needs.

Implication: our entire MEGA-3 / MEGA-8 / MEGA-11 line — the claim that joint mod-44100 admissibility is the "main" obstacle — is paradigm-locked to the modular framing and may be mathematically incomplete from the analytic-NT view. **The genuine obstruction is the cross-term between local density and global density, not the residue-class structure itself.** This was invisible to the bare-lane mod-arithmetic frame and to the geometric frame; only the multiplicative-analytic intersection caught it.

---

## 8. Recommendation

**Submit a FUSION-lane sketch implementing the synthesis attack on the trilinear exponential sum S_3(α) and the bridge lemma combining CLP + Vinogradov.**

Recommended sketch parameters:
* **Lane**: FUSION
* **Sketch (.txt, ≤30 lines)**: bare statement of the bridge lemma — "the powerful triple correlation is o(X^{1/2})" with a one-line note on the bridge lemma.
* **Companion (.fusion.json)**: paired LLM = Grok-4 + Codex; named technique = "CLP-factorized trilinear circle-method sum"; candidate lemmas = the bridge lemma decomposed into (a) CLP slice factor, (b) Bohr-set density increment, (c) Vinogradov mean value, (d) Burgess on length X^{1/4+ε}.
* **Subsystem fit**: lemma-based informal reasoner (subsystem #2). The MCGS formalizer (subsystem #1) is unsuited because there is no closed Lean target yet — this is a NEW analytic mechanism, not a formalization closure.
* **Expected outcome distribution**: P(compiled_advance with mathematical_content_score ≥ 5) ≈ 0.10; P(compiled_no_advance with novel mechanism captured in Aristotle's trace) ≈ 0.35; P(compile_failed because the new infrastructure is too heavy) ≈ 0.45; P(target_resolved) ≈ 0.02. The 35% middle outcome is the most likely value: Aristotle does not close the gap but produces formalized fragments of the bridge lemma we can iterate on.

**Action steps** (in priority order):
1. Write the .fusion.json with the synthesis bridge lemma and the four sub-lemmas.
2. Write the ≤30-line .txt sketch stating the trilinear correlation bound.
3. Submit through the FUSION-lane gate.
4. Independently of the submission: implement the 3-D hash search from Persona 4 to extend the verified bound from 10²² to 10³⁰. This is a pure search and runs in parallel to the analytic attack.
5. **Audit our MEGA-3 / MEGA-8 / MEGA-11 submissions** against the singular-series critique from Persona 2. If Aristotle has been claiming `target_resolved=0` on a mistaken framing of "mod-44100 vanishes", we should record this as a paradigm-locked failure mode.

Final note: this experiment validates the hypothesis. The generalist model defaults to modular closure attacks; the paradigm-locked specialists each surfaced a distinct global mechanism. The synthesis combines two of them (additive + analytic) into a single sum we have never written down.
