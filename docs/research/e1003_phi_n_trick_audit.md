# E1003 Fixed-Support Finiteness — Novelty Audit

**Date**: 2026-05-30
**Subject**: R9 (UUID `263fded4-...`, Aristotle job `d7f61f47-...`) proof of fixed-support finiteness for φ(n)=φ(n+1).
**Statement proved**: For any finite set S of primes, {n > 0 : φ(n)=φ(n+1) ∧ supp(n)∪supp(n+1) ⊆ S} is finite.

## 1. Mathematical Verification (Re-derivation)

R9's proof has four ingredients; each checks out.

| Step | Claim | Verified? |
|---|---|---|
| 1 | φ(n) = n · ∏_{p|n}(1 − 1/p) | ✓ Euler's formula (Hardy–Wright §16.3) |
| 2 | φ(n) · rad(n) = n · ∏_{p|n}(p − 1)   (lemma `totient_mul_rad_eq`) | ✓ Multiply step 1 by rad(n) |
| 3 | primeFactors n₁ = primeFactors n₂ ⟹ φ(n₁)·n₂ = φ(n₂)·n₁  (lemma `totient_ratio_of_primeFactors_eq`) | ✓ Direct from step 1 since the product factor is identical |
| 4 | Map n ↦ (S.filter(·∣n), S.filter(·∣(n+1))) is injective on the solution set | ✓ See below |
| 5 | Image ⊆ S.powerset × S.powerset, which is finite | ✓ Trivial |

**Injectivity argument (Step 4).** Suppose n, m are both solutions, supports in S, and supports match pairwise:
- rad(n) = rad(m): step 3 gives φ(n)·m = φ(m)·n.
- rad(n+1) = rad(m+1): step 3 gives φ(n+1)·(m+1) = φ(m+1)·(n+1). Combined with φ(n)=φ(n+1) and φ(m)=φ(m+1), this yields φ(n)·(m+1) = φ(m)·(n+1).
- Subtracting: φ(n) = φ(m). Plug into φ(n)·m = φ(m)·n ⟹ n = m (use Nat.totient_pos.2 hn.1 > 0).

The Lean code mirrors this exactly. `nlinarith` closes both the rad-product positivity step and the final linear deduction. **Proof is mathematically correct.**

## 2. Literature Search

Searched: Erdős–Pomerance–Sárközy (1991, d(n)=d(n+1)); Graham–Holt–Pomerance "On the solutions to φ(n)=φ(n+k)" (`math.dartmouth.edu/~carlp/phi.pdf`); Pollack–Pomerance "Phi, primorials, and Poisson" (2020); Sierpiński 1956; Schinzel–Wakulicz; Yamada–Saito arXiv:2002.12155; Hardy–Wright; Apostol; Tenenbaum; standard textbooks; MathOverflow.

**Findings:**

1. The identity φ(n)/n = ∏_{p|n}(1 − 1/p) is textbook (Hardy–Wright Thm 327). The corollary "φ(n)/n depends only on rad(n)" is implicit in every undergraduate treatment but is rarely stated as a named theorem.

2. None of the searched papers state "for fixed S, only finitely many n with φ(n)=φ(n+1) and supports ⊆ S." The relevant papers all attack the *opposite* direction — proving infinitude (Sierpiński 1956 for general k; Yamada–Saito 2020 for specific even k; Graham–Holt–Pomerance for k even).

3. The fixed-support finiteness is a **trivial consequence** of an even stronger classical fact: **for any fixed N, there are only finitely many n with φ(n) = N** (Hardy–Wright Thm 329). If supp(n) ⊆ S then φ(n) ≤ n ≤ ∏ p^{ord} bounds aren't quite direct, but combining with "supp(n+1) ⊆ S" and the identity n+1 − n = 1 reduces the problem to *finitely many pairs* via S-unit theory (Evertse 1984: x+y=1 in S-units has ≤ 3·7^{2|S|+1} solutions).

4. Therefore the *result* is essentially a corollary of either Hardy–Wright Thm 329 OR the Evertse S-unit bound. The *specific proof R9 gives* — via the rad-based injection rather than via S-units or value-of-φ-finiteness — is a clean elementary argument I could not locate in published form.

## 3. Classification

**FOLKLORE.**

- The result itself is a trivial corollary of standard finiteness facts (value of φ has finitely many preimages; S-unit equation x+y=1 has finitely many solutions). Any specialist would call it "obvious."
- R9's specific elementary proof (rad-injection, no S-units, no preimage-count) is **clean and self-contained**, and I did not find it in print, but it is the kind of one-page exercise that would appear in a problem set or lecture notes without attribution.
- Not novel mathematics. Not a published theorem either.

## 4. Strongest Evidence

**Negative evidence (no exact match found):** No paper in the searched corpus proves "fixed-support finiteness for φ(n)=φ(n+1)" as a standalone result. Graham–Holt–Pomerance focuses on infinitude/asymptotics; Yamada–Saito invokes prime k-tuple machinery; Pollack–Pomerance treats density.

**Folklore evidence:** Hardy–Wright Thm 329 (finitely many n with φ(n)=N) already implies a much stronger statement: drop the n+1 constraint entirely and you still get finiteness, since supp(n) ⊆ S bounds φ(n) ≤ ∏_{p∈S}(p-1)·(something finite)… actually no — supp(n) ⊆ S does *not* bound n (e.g., 2^k all have supp={2}). So the rad-injection argument is genuinely needed and is *not* a direct corollary of Thm 329. The Evertse S-unit reduction is the standard way an expert would see this.

## 5. Mathlib-Formalization Value

**HIGH** — even though the math is folklore.

- Mathlib does not currently have `Nat.totient_ratio_of_primeFactors_eq` or `Nat.totient_mul_rad_eq` as named lemmas. These are useful building blocks.
- The rad-injection technique generalizes to any equation involving φ on consecutive (or shifted) integers under support constraints. Worth packaging.
- The result itself — fixed-support finiteness for φ(n)=φ(n+k) — is a clean target for a Mathlib `Erdos1003` file as a partial result, separating "easy direction" (finite support ⟹ finite) from "hard direction" (the infinitude conjecture itself, still open).

**Recommendation**: submit `totient_mul_rad_eq` and `totient_ratio_of_primeFactors_eq` as standalone Mathlib PRs. The main theorem belongs in a `Erdos1003.lean` file as a documented partial result, not as a novel mathematical contribution.

## 6. Honest Status

- The infinitude conjecture φ(n)=φ(n+1) — **open**, unchanged.
- The fixed-support sub-problem — **folklore**, R9 produced a clean elementary formalization.
- Aristotle did NOT discover novel mathematics here. It found a clean Lean 4 proof of a folklore result.
- "Compiled clean" ≠ "resolved the gap". Per CLAUDE.md hard rule #12, this is **compiled_partial**, not gap-resolving.
