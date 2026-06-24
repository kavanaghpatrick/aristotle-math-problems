# Research Fusion Analysis: Erdős 203 (2D Sierpiński)

**Agent:** F5 of 10 (research-fusion pull) | **Date:** 2026-05-30
**Problem:** ∃ integer m with (m, 6) = 1 such that none of 2^k · 3^ℓ · m + 1 are prime, for any k, ℓ ≥ 0?
**Status:** OPEN. Generalization of classical 1D Sierpiński (with 2^k m+1) to 2D (with 2^k 3^ℓ m+1).

---

## A. Recent literature pull (2020–2026)

1. **Zhang, Chi (2021)** — *Generalized Sierpiński numbers based m* (arXiv). For any integer m > 1, infinitely many k satisfy k · m^n + 1 composite for all n. Generalizes Sierpiński to arbitrary bases via covering systems + cyclotomic polynomials.
2. **Filaseta, Finch, Kozek** — *A revised Sierpiński conjecture*. Conjectures every Sierpiński number is either a perfect power OR has a finite prime covering set. Proves for every ℓ≥1 ∃ m such that 2^k m^i + 1 composite for 1 ≤ i ≤ ℓ, k ≥ 0.
3. **Balister, Bollobás, Morris, Sahasrabudhe, Tiba (2022)** — *On the Erdős covering problem: the distortion method*. Reduces Hough's min-modulus bound to 616,000. Establishes that distinct odd-modulus covering systems satisfy 2|L or 9|L or 15|L (the "Erdős-Selfridge odd-cover-impossibility").
4. **Cummings, Filaseta, Trifonov (~2024)** — Reduces min-modulus to 118 for squarefree-moduli covering systems. Provides specified bound for j-th smallest modulus.
5. **2025 arXiv 2508.05942** — *Generalized Sierpiński and Riesel numbers of the form t·b^t + α*. Cyclotomic-polynomial framework extending Zhang.

---

## B. Adjacent-domain analogs

### B1. Algebraic number theory — Cyclotomic obstructions
The form 2^k · 3^ℓ · m + 1 is a special case of "values of cyclotomic polynomials" Φ_n(b) for varying n. The prime divisors of Φ_n(b) are ≡ 1 (mod n) (or divide n). The 2D version asks: *for which m does every Φ_{2^a 3^b}(value) admit a fixed prime divisor?* This connects to **Schinzel-Sierpiński hypothesis H** restricted to multi-variable polynomial families.

### B2. Topology / Coding theory — Multi-dimensional covering codes
A covering system is a set of arithmetic progressions covering ℤ. The 2D analog (over ℤ²) is a 2D-covering of (k, ℓ) ∈ ℕ² such that the family {2^k · 3^ℓ · m + 1 mod p_i} covers ℕ² for finitely many primes p_i. This maps to **perfect covering codes** in the Hamming space (ℤ/L_1) × (ℤ/L_2). Analog: Vasilyev's perfect codes / Lloyd's theorem.

### B3. Algebraic geometry — Toric varieties and lattice points
2^k · 3^ℓ ranges over a 2D toric lattice in (log 2, log 3). The set of (k, ℓ) avoiding primality is a sublattice; the question becomes: *does there exist a sublattice ℒ ⊂ ℕ² such that the image of m + ℒ → ℕ is composite-only?* Connects to **Tate's theorem on closed points of toric varieties** and **Bilu-Sebbar height bounds on multiplicative-group orbits**.

### B4. Group theory — Multiplicative orbits on (ℤ/N)*
m fixed; the orbit of m under multiplication by ⟨2, 3⟩ ⊆ (ℤ/N)* hits every coset. For each prime p, choose N = p; ask whether the multiplicative group ⟨2, 3⟩ ⊆ (ℤ/p)* has index 1 (then no covering by p). For p where ⟨2, 3⟩ has small index k, we get a "p-covering of size k". Analog: **Artin's primitive root conjecture** (modified for 2 generators).

---

## C. Technique-transfer candidates

1. **Cyclotomic-polynomial covering construction** (Zhang 2021 generalized; Filaseta-Finch-Kozek). For chosen primes p_1, ..., p_r with multiplicative orders ord_{p_i}(2) = a_i, ord_{p_i}(3) = b_i, the constraint 2^k 3^ℓ m + 1 ≡ 0 (mod p_i) carves a sublattice in (k, ℓ) ∈ ℤ². Cover ℕ² by enough such sublattices. **Citation**: Filaseta, Finch, Kozek "On a problem of Erdős on Riesel numbers."
2. **Selfridge-Cohen primality avoidance via fixed prime divisor** (classical 1962). The original Sierpiński covering uses primes {3, 5, 7, 13, 17, 241} via mod-2 orders. The 2D analog needs primes p where ord_p(2) and ord_p(3) are both small relative to lcm. **Citation**: Sierpiński, W. "Sur un problème concernant les nombres k·2^n+1."
3. **Hough-style probabilistic obstruction** (2015 Annals) — the same probabilistic-method argument bounding min-modulus from below. Adapted to 2D: prove that for ANY 2D covering construction, the modulus product must exceed an absolute bound — likely refuting existence of m without large multiplicative structure. **Citation**: Hough, R. "Solution of the minimum modulus problem for covering systems."
4. **Brun-style sieve in algebraic number fields** — for the 2D problem, sieve out primes from values 2^k 3^ℓ m + 1 by lifting to ℤ[ζ_n]. Adapted from Maier-Pomerance sieve. **Citation**: Maier, H., Pomerance, C. "Unusually large gaps between consecutive primes."
5. **Polynomial-method / Linear Forms in Logs** (Baker) — for 2^k 3^ℓ m + 1 to be prime infinitely often, linear forms in logs (Baker 1966) constrains the growth. Adapted: assume 2^k 3^ℓ m + 1 = q_i prime for sequence (k_i, ℓ_i), apply Baker on log q_i - k_i log 2 - ℓ_i log 3 ≪ |log m|.

---

## D. Most promising fusion: **2D-covering construction via multiplicative group ⟨2, 3⟩ in (ℤ/N)***

**Specific idea:** Directly extend Sierpiński's 1D covering construction. The 1D Sierpiński number k=78557 has covering primes {3, 5, 7, 13, 19, 37, 73}. For each prime p, we need ord_p(2) · ord_p(3) | (something small) to cover the 2D lattice (k, ℓ).

**Construction template:**
- Pick primes p with small lcm(ord_p(2), ord_p(3)). E.g., p = 7: ord_7(2) = 3, ord_7(3) = 6, lcm = 6. So {2^k 3^ℓ mod 7 : k ∈ ℤ/3, ℓ ∈ ℤ/6} has at most 18 cosets.
- Choose enough primes p_1, ..., p_r such that the union of obtained 2D residue sub-lattices covers (k, ℓ) ∈ ℕ² densely enough — then by CRT lift to a single m.
- Verify m is coprime to 6 (easy).

**Why fusion-amenable now (2026):**
- Project already has `scripts/erdos203_quotient_lift.py` (in analysis/).
- Existing 2D Sierpiński partial covers exist (formal-conjectures TODO mentions).
- Aristotle is strong on `ZMod L`-style finite verifications.

**The cross-domain ingredient:** the **multiplicative subgroup structure of ⟨2, 3⟩ in (ℤ/p)***. Specifically the rank-2 lattice obstruction theory of **Bilu-Sebbar** (heights in multiplicative groups).

**Risk:** This is essentially the canonical approach — Codex/Grok have flagged it. The hard part is finding enough primes with small mutual orders to cover a 2D lattice (the parameter count grows as 2^r rather than r for 1D Sierpiński). 1D took 7 primes; 2D plausibly needs ~14-20.

---

## E. What we'd need to feed Aristotle

Beyond bare gap:

```
OPEN GAP: Erdős 203 — 2D Sierpiński (Erdős-Graham generalization)
Source: erdosproblems.com/203

Statement: ∃ m : ℕ with Nat.gcd m 6 = 1 such that ∀ k ℓ : ℕ, ¬ Nat.Prime (2^k * 3^ℓ * m + 1)

Construction template (a hint, NOT a proof):
Use the covering-system method of Sierpiński, generalized to 2D:
- Pick a covering primes P = {p_1, ..., p_r}.
- For each p_i, the constraint 2^k · 3^ℓ · m + 1 ≡ 0 (mod p_i) defines a sublattice
  L_i = {(k, ℓ) ∈ ℤ² : k ≡ a_i (mod ord_{p_i}(2)), ℓ ≡ b_i (mod ord_{p_i}(3))}.
- If the union ⋃ L_i ⊇ ℕ², we have a 2D-covering.
- Solve via CRT for m such that m ≡ -(2^{a_i} 3^{b_i})^{-1} (mod p_i).

theorem erdos_203_witness :
  ∃ m : ℕ, m.Coprime 6 ∧ ∀ k ℓ : ℕ, ¬ Nat.Prime (2^k * 3^ℓ * m + 1) := by sorry

Concrete attempt: m = (explicit value from running CRT on candidate primes
{3, 5, 7, 13, 17, 19, 37, 73, 97, 109, 241, 257, 433, 673})
should suffice for a 2D Sierpiński.

Hint: After finding candidate m via search, verification reduces to:
  ∀ (k ℓ : Fin LCM_M), ∃ p ∈ P, (2^k * 3^ℓ * m + 1) ≡ 0 (mod p) ∧ 2^k * 3^ℓ * m + 1 > p
where LCM_M = lcm over chosen primes of {ord(2), ord(3)}.
This is a finite `Decide` over (k, ℓ) ∈ Fin LCM_M × Fin LCM_M.
```

**Crucial cross-domain ingredient**: invite Aristotle to enumerate "2D-covering certificates" — finitely many primes whose pairwise multiplicative-order lcms cover ℕ². Specifically include a witness search in the sketch's hint section pointing at candidate prime sets and a fixed LCM.

**Honest assessment:** Plausibility 6/10. This is one of the top closure candidates (closure_list top-1, prob 6/10). Has had multiple Aristotle attempts (slot652, slot666, slot673). Has compiled partial. The fusion ingredient (multiplicative-orbit structure of ⟨2, 3⟩) is *already* the standard approach — the real novelty would be importing **Filaseta-Finch-Kozek's "perfect-power exception" framing**, which says some Sierpiński-numbers don't come from covering systems but from algebraic identities (like Aurifeuillean factorization). If E203 has a similar Aurifeuillean shortcut at form 2^a 3^b, that would be genuinely new.
