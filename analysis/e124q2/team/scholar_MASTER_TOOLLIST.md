# MASTER TOOL-LIST for Erdős #124 / Q2 (BEGL96 conjecture, finite case)

**Author:** scholar. Every theorem below is stated precisely with citation, sourced from PDFs I
read (BEGL96, Melfi04) or carefully-flagged secondary statements. **Confidence tags:**
[PDF] = read the actual paper; [SEC] = secondary/Grok, NOT independently PDF-verified — use with
care; [COMP] = computed by the team. Companion files: `scholar_BEGL96_proof_dissected.md`,
`scholar_Melfi_lineage_and_status.md`.

---

## A. THE PROBLEM (canonical, after sumset's reduction)

`B_d` := integers with only digits 0,1 in base d (= `sumsOfDistinctPowers d 0`).
`S(d,k) = d^k · B_d` [COMP, proved by sumset]. Open question **Q2**:

> For finite D, all d ≥ 3, with `∑_{d∈D} 1/(d−1) ≥ 1` and `gcd(D)=1`, is
> `R(D,k) = ∑_{d∈D} d^k·B_d` cofinite for every k ≥ 1? (= the "if" direction of BEGL96
> conjecture for finite A.) **STATUS: OPEN since 1996. TRUE expected** (all team computations
> cofinite; only (3,4,7) + small sets proven).

---

## B. NECESSITY (both directions settled — these are THEOREMS, in our Lean file)

1. **Pomerance density bound** [PDF, BEGL96 §1, attributed to C. Pomerance]. If
   `∑ 1/(d−1) < 1` then `Σ(Pow(D;s))` has upper density `< 1` (so NOT cofinite). Hence
   `∑1/(d−1) ≥ 1` is NECESSARY. Lean: `erdos124.converse`. Mechanism: standard diophantine-
   approximation counting; the per-base ray `d^k·B_d` covers a `1/(d−1)` fraction of [0,X]
   asymptotically, and `∏(1 − coverage)` argument bounds the union below 1.
   ⚠ [COMP, cassels] CAVEAT: the invariant is the SUM `∑1/(d−1)`, NOT the product
   `∏(1+1/(d−1))`. `∏ ≥ 2` is strictly WEAKER than `∑ ≥ 1`. Do not use the product form.

2. **gcd necessity** [COMP, sumset/cassels; trivial]. If `gcd(D)=g>1`, pick prime `p|g`; then
   `p^k | d^k |` every summand, so `R(D,k) ⊆ p^k·ℕ`, not cofinite, for k ≥ 1. (k=0 immune:
   `d^0=1`.) This is why BEGL add `gcd(D)=1` only for k ≥ 1.

---

## C. SUFFICIENCY — what is PROVEN, and the methods

3. **BEGL96 Theorem 1** [PDF]. If a sequence A of integers >1 has (i) `lim sup A(n)/n > 0`
   (POSITIVE UPPER DENSITY as a subset of ℕ) and (ii) `gcd{a∈A}=1`, then for any s there is a
   finite `A₀ ⊆ A` with `Pow(A₀;s)` complete. ⚠⚠ **DOES NOT APPLY TO FINITE D** (lim sup = 0
   for every finite set). NOT a lever for Q2. Proof = Claims 1–4 below.

4. **BEGL96 (3,4,7) and small sets** [PDF, §3]. Proven COMPLETE for all relevant s by
   **Mignotte–Waldschmidt linear forms** (tool #8), NOT by Theorem 1. Verbatim bound used:
   `|3^p − 4^q| > exp{ln3·(p − 500·ln4·(8+ln p)²)}` [MW Cor 10.1]. Largest miss (s=1), CORRECTED
   (BEGL96's printed numbers have an off-by-one in 3 of 4 secondary examples — see
   `scholar_BEGL96_largest_miss_audit.md`): (3,4,7)→**581** (BEGL✓, the only PROVED one),
   (3,4,5)→**79** (BEGL prints 78), (3,5,7,13)→**112** (BEGL prints 111), (3,6,7,13,21)→**17**
   (BEGL prints 16). [COMP, scholar+maverick, 3-method-verified, convention j≥1 = our k=1]
   ⚠ The DISPLAYED computations are s=1; the all-k claim (our Lean `ne_zero_three_four_seven`)
   relies on MW extending to exponents ≥ s [troika verifying].

5. **Melfi04 Proposition 1** [PDF]. The INFINITE BEGL conjecture is FALSE: ∃ infinite A with
   `∑1/(a−1) < ε` yet `Pow(A;s)` complete ∀s. Construction `A = R_p ∪ {p+1}`, `R_p={n²p}`, via
   Sprague (tool #9) + residue-sweep by `(p+1)^t mod p^s`. ⚠ Finite case (Q2) UNAFFECTED —
   Graham confirmed (pers. comm. 2004) A was always meant finite; "for finite sets... open."
   Lean: `erdos124.melfi_construction` (the ε-thin completeness statement).

---

## D. THE FOUR REUSABLE BEGL96 LEMMAS (k-uniform; the actual machinery) [all PDF]

6a. **Claim 1 — completeness/gap-filling engine.** Finite chunk B=(b₁<…<b_N) with
    `β := ∑ b_i^{−1} > 2` ⇒ `Σ(Pow(B;s))` has all gaps `≤ 2 b_N^{s+1}`. (Quantitative
    Cassels-type small-gaps criterion.) ⚠ Needs β STRICTLY > 2; the boundary `∑1/(d−1)=1`
    case cannot feed it — THE core obstruction for tight D. [cassels owns this]
6b. **Claim 2 — Prouhet–Thue–Morse moment-matching partition.** `{0,…,2^s−1}=C∪D` with
    `∑_C c^j = ∑_D d^j (j<s)` and `∑_C c^s − ∑_D d^s = s!2^{C(s,2)}`. Classical PTE ideal
    solution via recursion `C(k+1)=C(k)∪(2^k+D(k))`, etc. [maverick's recursion engine relates]
6c. **Claim 3 — AP manufacture.** Szemerédi [S] (positive-density block ⊃ 2^s-term AP) +
    affine-invariance of Claim 2 ⇒ sumset contains arbitrarily long APs of a FIXED step
    `D = s!2^{C(s,2)} d^s`.
6d. **Claim 4 — residue sweep (where gcd=1 is consumed).** For primes `q_i | D`, gcd=1 gives a
    base coprime to `q_i`; its powers fix a residue `c(i)` coprime to `q_i`; CRT-combine to
    `M` with `gcd(M,D)=1`; then `kM mod D` sweeps ALL residues mod D. ⇒ `Σ(Pow(A₀;s))` ⊇ full
    residue system mod D. [modular/lift own this]
    Assembly: Claim 3 + Claim 4 ⇒ block of `≥2b_N^{s+1}` consecutive ints; Claim 1 bootstraps
    to all large ints.

---

## E. CLASSICAL COMPLETENESS MACHINERY (background; [SEC] unless noted)

7. **Birch 1959** [SEC: B.J. Birch, "Note on a problem of Erdős", Proc. Camb. Phil. Soc. 55
   (1959) 370–373]. For coprime p,q ≥ 2, `{p^i q^j : i,j ≥ 0}` is complete. Effective (huge)
   bound. ⚠ [PDF, BEGL96 §1 cite it as [B] for exactly this]. **Shifted version** (i,j ≥ s):
   [SEC] no general theorem; requires separate argument (the BEGL/MW route). [COMP, cassels]:
   Birch's method survives a lower exponent bound (only finitely many small terms dropped), so
   the YES/NO answer is k-invariant for fixed D — only threshold N₀ moves.

8. **Mignotte–Waldschmidt 1989** [PDF via BEGL cite; [SEC] for general form]. "Linear forms in
   two logarithms and Schneider's method, II", Acta Arith 53 (1989) 251–287, Cor 10.1. Gives
   effective lower bounds on `|a^p − b^q|` for coprime a,b; explicit for (3,4). [SEC] the method
   yields an analogous effective `C(a,b)` for EVERY coprime pair — THE tool to extend (3,4,7)-
   style proofs to other admissible triples (troika's lever). ⚠ Exact general constant not
   PDF-verified; cite as "Mignotte–Waldschmidt-type effective bound" until checked.

9. **Sprague 1948** [SEC: R. Sprague, Math. Z. 51 (1948)]. For each fixed n≥2, every sufficiently
   large integer is a sum of DISTINCT n-th powers. Ineffective. (Melfi's input for Prop 1.)

10. **Interval-filling completeness criterion = "Brown's criterion"** [Crossref-VERIFIED].
    Strictly increasing (a_n), a₁=1: if `a_{n+1} ≤ 1 + ∑_{k≤n} a_k` for all n, then every nonneg
    integer is a sum of distinct a_n. **Cite: J. L. Brown Jr., "Note on Complete Sequences of
    Integers", Amer. Math. Monthly 68 (1961), 557–560, DOI 10.2307/2311150.** Follow-up:
    **P. Erdős, Acta Arith. 7 (1962), 345–354, DOI 10.4064/aa-7-4-345-354.**
    ⚠⚠ PHANTOM-CITATION CORRECTION: the previously-circulated "Cassels 1960 / Acta Sci. Math.
    Szeged 21" reference for this lemma DOES NOT EXIST — conflation with the Erdős 1962 Acta Arith
    paper. Cassels's real 1960 "On a conjecture of Bush" note does NOT contain this lemma. DROP all
    "Cassels 1960" citations. (The criterion is essentially classical/folklore.)

11. **Graham 1964 criterion** [SEC]. `a_{n+1}/a_n → 1` and `∑1/a_n = ∞` ⇒ complete. BEGL relax
    ratio to `a_{n+1} ≤ (1+ε)a_n`. ⚠ unverified attribution.

---

## F. RELATED / DENSITY LINE (NOT Q2, but the active neighbourhood)

12. **Melfi 2001** [SEC: Rend. Circ. Mat. Palermo (II) 50, 239–246]. For `{3,4}` (sub-critical,
    ∑=5/6<1): `n_k ≪ k^{1.0353}` (i.e. `P_{3,4}(x) ≫ x^{0.9659}`). ⚠ ATTRIBUTION FIX: this
    bound is Melfi 2001, NOT BEGL96 (Melfi04 ref [12]); Grok mis-attributes it to BEGL.
13. **Hasler–Melfi 2024** [PDF abstract: Comb. Number Theory 13(2), MSP, 1 Jul 2024]. Improves
    `{3,4}` to `P_{3,4}(x) ≫ x^{0.97777}`. Positive density of `Σ(Pow({3,4};1))` (Erdős's
    `n_k ≪ k`) STILL OPEN. Most recent work in the area; field's tools max at exponent ~0.978.
14. **Melfi04 Conjecture 1** [PDF]. Pairwise-coprime + `∑1/log a > 1/log 2` ⇒ positive lower
    density. ⚠ `gcd{A}=1` (not pairwise) is INSUFFICIENT: counterexample `{3,9,81,104}`
    (gcd=1, zero lower density). [COMP, scholar] but `∑1/(d−1)=0.647<1` there — sub-critical, so
    consistent with Q2. RAISES the prime-power-collinear test (tool #16).
15. **Erdős–Lewin** [PDF cite, EL Math.Comp.65(1996)837–840]. "d-complete sequences": for gcd=1
    set {a_i}, large ints = sums of `∏a_i^{r_i}` (r_i≥1) no term dividing another. Cousin
    problem, NOT Q2. False-trail caution: don't conflate "d-complete" with our completeness.

---

## G. NEW STRUCTURAL LEVERS the team generated (Q2-specific) [COMP]

16. **Prime-power-collinearity is harmonically bounded** [COMP, scholar]. Powers of a single odd
    prime p≥3 contribute `∑_j 1/(p^j−1) ≤ 0.682 (p=3) < 1` ⇒ NO admissible D is supported on one
    odd prime. But TWO prime-power families reach admissibility: e.g. D=(3,4,8,9) (∑=1.101),
    (3,4,8,32) (∑=1.008) — bases all `2^a` or `3^b`, gcd=1. These are the WORST-CASE residue-
    diversity admissible sets → strongest Q2 stress tests [breaker computing]. If cofinite, the
    harmonic condition demonstrably defeats Melfi's collinearity pathology = the reason Q2 holds.

17. **N₀(D,k) ≍ d_max^k** [COMP, cassels/breaker]. Threshold non-uniform in k (blows up
    geometrically). Floor (PROVED): `N₀ ≥ d_min^k − 1`. Why "apply k=0 + scale" FAILS (differing
    scale factors d^k don't commute with the sumset).

18. **Termination test discipline** [COMP, breaker]. "max exc ≈ N" is NOT non-termination;
    recompute at 2N,4N. (3,4,7) k=2 has rare large stragglers near 4^J bands (785743, 3982888) —
    the COMPUTATIONAL SHADOW of the MW bound; they terminate (BEGL proved finite).

---

## H. DEFINITIVE STATUS LINE (for write-up / submission framing)

Q2 = "if" direction of the BEGL96 conjecture, FINITE case, is **OPEN since 1996**. Disproven only
for infinite A (Melfi04). Proven only for (3,4,7) and a few small sets (BEGL96, via Mignotte–
Waldschmidt). No general finite-case result exists. All team computation says TRUE. The two
necessity conditions are settled theorems. The sufficiency obstruction is precisely: the
boundary harmonic case ∑=1 cannot feed the BEGL Claim-1 gap-filling engine (needs a chunk with
∑>2), so each admissible D needs an ad-hoc transcendence input — exactly why only finitely many
specific sets are resolved.

## I. ★ THE MIGNOTTE–WALDSCHMIDT ROUTE CANNOT PROVE Q2 (critical guardrail) [SEC, high-confidence]

The only known sufficiency method (BEGL's (3,4,7) route) is INTRINSICALLY case-by-case and CANNOT
scale to the full conjecture. Reason: the effective lower bounds on `|d_i^p − d_j^q|` carry
constants that grow with the logarithmic heights of the bases `d_i, d_j`. Admissible D may contain
ARBITRARILY LARGE elements while still satisfying `∑1/(d−1)≥1` and `gcd=1` (e.g. add many large
bases). So no single effective constant covers the infinite family of admissible D — each concrete
D needs its own D-dependent finite computation. **This is the deep structural reason the problem
has resisted since 1996, and it tells the team: a proof of Q2 needs a genuinely NEW gap-filling
idea that works UNIFORMLY at the harmonic boundary — NOT a refinement of the transcendence route.**
The team's (R)-half proof (residue coverage) is real progress; the (A)-half (uniform gap-filling at
∑=1) is where the genuine novelty must come from. Candidate new directions worth the team's effort:
(a) a self-similar/renormalization argument exploiting `R_{k+1} ⊆ R_k` (troika) + the `d^k·B_d`
Cantor-set structure; (b) a Fourier/circle-method bound on the exceptional set that is uniform in D
given `∑1/(d−1)≥1`; (c) the prime-power-collinearity bound (#16) promoted to a general "spread"
lemma forcing enough multiplicative independence. None of these is in the literature.
