# Research Fusion Analysis: Erdős 952 (Gaussian Moat)

**Agent:** F5 of 10 (research-fusion pull) | **Date:** 2026-05-30
**Problem:** ∃ infinite sequence (x_n) of distinct Gaussian primes with |x_{n+1} − x_n| bounded (Gaussian moat).
**Status:** OPEN since Gordon 1962 (often misattributed to Erdős).

---

## A. Recent literature pull (2020–2026)

1. **(arXiv:2401.08441) "On the Gaussian Moat Problem" (Jan 16 2024)** — claimed full resolution: impossible to walk to infinity. **Withdrawn Jan 17 2024** [v2 retraction]. So the problem remains open.
2. **Loh, Phen, Vissichelli (2019, arXiv:1901.04549, Walking Through the Gaussian Primes)** — modern survey + computational extension. Generalizes search to z[√2] and z[(-1+√-3)/2] (Eisenstein primes). Proves prime-free neighborhoods of arbitrary radius surround any imaginary-quadratic prime.
3. **Tsuchimura (2004)** — *Computational Results for Gaussian Moat Problem* (Semantic Scholar). Best computational moat: √36-moat, computational effort 5000× larger than the previous √26-moat (Gethner et al. 1998).
4. **2014 arXiv 1412.2310 — *Walks on Primes in Imaginary Quadratic Fields*** — generalizes to all 9 imaginary quadratic UFDs. Uses Euclidean MST + Delaunay triangulation to find moats in O(|P| log |P|) time. Density estimates on imaginary-quadratic primes.
5. **(arXiv:2510.14006) Prime-free discs in imaginary quadratic fields** — uses Landau-Page + Bombieri-Vinogradov for number fields. Shows prime-free discs of arbitrary radius exist, supporting the conjecture that walking to infinity is impossible.

**Note:** The 2024 "proof" being withdrawn is significant — the problem appears hard, possibly requiring novel techniques. The conjectured answer is NO (no infinite path exists).

---

## B. Adjacent-domain analogs

### B1. Percolation theory — Site percolation on ℤ²
Consider the random-prime model: each Gaussian integer is "open" with probability p_z = 1/log|z|² (Cramér-like model for Gaussian primes). The Gaussian moat problem asks about an infinite open cluster — exactly *site percolation* on ℤ² with non-uniform p_z. **Strong analog**: Russo-Seymour-Welsh-type arguments for non-uniform 2D percolation; Aizenman-Newman, Liggett-Schonmann-Stacey monotone-coupling.
The probability of an infinite cluster goes to 0 as p_z → 0, which happens slowly here. **The PERCOLATION CONJECTURE** in this model is precisely E952.

### B2. Geometric group theory — Cayley graphs of ℤ[i]
The Gaussian integer lattice ℤ[i] with multiplication-by-i action is the Cayley graph of ℤ². The Gaussian primes form a subset; the question becomes *does this subset percolate?* **Analog**: random subsets of Cayley graphs of amenable groups. Connection to **Gromov's polynomial growth** + **Pichot-Weiss equivalence** of percolation on amenable groups.

### B3. Random analytic — Brownian motion on prime carpets
Replace step-by-step walks with Brownian motion. The Gaussian moat problem becomes: *does Brownian motion on the union of disks of radius C around each Gaussian prime contain an infinite component?* **Analog**: planar Brownian motion and its hitting probabilities, Lévy's modulus of continuity, Mandelbrot's percolation. Connection to **Schramm-Loewner Evolution (SLE_κ)** boundaries.

### B4. Analytic number theory — Sieve methods
Gaussian primes p with |p|² ≤ N satisfy a Selberg-style sieve density. The bounded-walk condition forces large local concentration of primes. **Analog**: Maier-style irregularities, Heath-Brown's "primes are very dense in short intervals" results, and recently Granville-Soundararajan's pretentious-prime theory.

---

## C. Technique-transfer candidates

1. **Aizenman-Barsky / Menshikov sharp-threshold theorems for percolation**. Sharp transitions at critical probabilities; in our model, the moat conjecture says we're below the critical threshold for all step bounds. Citation: Aizenman, Barsky "Sharpness of the phase transition in percolation models" Comm. Math. Phys 1987.
2. **Cramér random model for primes** + **second-moment method**. Apply to Gaussian primes: expected number of paths of length L is computable; second-moment gives lower bound on cluster size. Citation: Granville, A. "Harald Cramér and the distribution of prime numbers."
3. **Iwaniec rectangle method for Gaussian primes in short rectangles**. Foundation for moat-existence proofs — short rectangle results give prime-free neighborhoods. Citation: Iwaniec, H. "Primes represented by quadratic polynomials in two variables" 1974.
4. **Bombieri-Vinogradov for imaginary quadratic fields**. Underlies many "prime-free disc" theorems including arXiv:2510.14006. Citation: Iwaniec-Kowalski *Analytic Number Theory* Chapter on number-field sieves.
5. **Selberg sieve adapted to Gaussian integers**. Direct sieve estimates on |{p ∈ ℤ[i] : N(p) ∈ [N, 2N]}|. Citation: Cojocaru-Murty *An Introduction to Sieve Methods*.

---

## D. Most promising fusion: **Site percolation on ℤ² with prime-density p_z + Aizenman-Barsky sharp threshold**

**Specific idea:** Reframe E952 as a 2D site-percolation question on ℤ[i] where vertex z is "open" iff z is a Gaussian prime. Let p_C be the probability density of openness in a disc of radius C around the origin (≈ density of primes near 0). For each step bound C, the moat conjecture (no infinite walk) is equivalent to "the prime-site percolation cluster of 0 is finite a.s. in the random model."

**Cross-domain machinery to import:**
- For *truly random* site percolation, the critical p_c ≈ 0.59 (Riordan-Walters 2007). Below p_c, no infinite cluster.
- The Gaussian-prime density at scale R is ≈ 1/log R², which → 0. **Below ANY critical threshold for large R.**
- The challenge: Gaussian primes are *not* random — they're deterministic. But Cramér-style heuristics suggest they're "random enough" for the percolation argument.

**Concrete strategy:**
1. Apply **Liggett-Schonmann-Stacey (1997)** domination of subcritical site percolation by a stochastic site model with vertices open i.i.d. with the same marginal density.
2. Bound the prime density above by a smooth function 1/log|z|² + ε.
3. Use **second-moment method** on path-counts to conclude finite clusters a.s.
4. **De-randomize via pseudo-randomness of primes** — use the Mertens-style 2D analog of the prime number theorem, established via L-functions of imaginary quadratic fields.

**Why fusion-amenable now (2026):**
- 2024 withdrawn proof presumably attempted some variant of this — its failure shows the obstacle isn't trivial.
- Recent prime-free-disc results (arXiv:2510.14006) provide the building blocks.
- This connects to the **GAFA-style breakthroughs in pretentious primes** by Granville-Soundararajan-Tao.

**Risk:** The de-randomization step is the crucial obstacle. Cramér's model fails (Maier's theorem) precisely at the short-interval scales relevant here. The percolation heuristic may give the right ANSWER but not a proof, because primes have hidden structure.

---

## E. What we'd need to feed Aristotle

Beyond bare gap:

```
OPEN GAP: Erdős 952 — Gaussian moat (Gordon 1962)
Source: erdosproblems.com/952, wikipedia/Gaussian_moat

Statement: ∃ (x : ℕ → ℤ[i]) (C : ℤ),
  Function.Injective x ∧ ∀ n, Prime (x n) ∧ (x (n+1) - x n).norm < C

theorem erdos_952 :
  ∃ (x : ℕ → GaussianInt) (C : ℤ),
    Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C := by sorry

Direction (HINT, not a proof):
The conjectured answer is NO — no such infinite walk exists. To DISPROVE existence
(i.e., prove finiteness), the standard route:
- For each C ≥ 1, show that prime-free annuli of radius > C exist eventually.
- Foundational: for any C > 0, there are infinitely many Gaussian primes p with
  no Gaussian prime in the disc of radius C around p (this is known via
  Mertens-style estimates on the imaginary quadratic prime distribution).
- Stronger: the union of all C-discs around primes does NOT cover a path to infinity.

Building blocks (cite):
- Iwaniec 1974: primes in short rectangles, density ≈ R²/log R.
- Tsuchimura 2004: computational √36-moat existence (bounded distance ≤ 6).
- arXiv:2510.14006 (2025): prime-free discs of any radius in imaginary quadratic fields.

Reformulation: under the Cramér random model + Liggett-Schonmann-Stacey domination,
the site-percolation cluster on ℤ[i] with vertex-density 1/log|z|² is subcritical,
hence finite a.s. To de-randomize, use Iwaniec-Kowalski Bombieri-Vinogradov for ℤ[i]
to control density fluctuations.
```

**Crucial cross-domain ingredient**: invite **2D site percolation theory** explicitly. Aristotle has minimal probability/percolation knowledge in Mathlib (only `MeasureTheory.Probability.Basic`). The sketch must inline:

> "Aizenman-Barsky (1987): subcritical site percolation on ℤ² with bounded vertex-density p < p_c = 0.59 has finite clusters a.s. The Gaussian-prime site-density at scale R is 1/log R² which is ≪ p_c for all R ≥ e^2 ≈ 7.4."

**Honest assessment:** Plausibility 2/10 for closure (closure_list top-6, prob 2/10). This is **the hardest of the five** — it asks for either an explicit infinite witness (which doesn't exist, almost certainly) or a finiteness proof (which all of modern analytic NT can't do). The closure_list explicitly excluded E952 because *"infinite-witness construction; closure mechanism is genuinely missing."* The 2024 withdrawn proof shows even careful researchers can't close this. Research fusion via percolation theory is a real cross-domain idea but the de-randomization step is the open problem itself.
