/-
# Erdős Problem 942 — limsup variant

Let h(n) count powerful integers in [n², (n+1)²).
We prove: limsup_{n→∞} h(n) = ∞ (as ℕ∞).

## Proof strategy (Golomb + Kronecker)

For any target M, pick M distinct primes p₁,…,p_M. By Golomb's
parametrization, a²pᵢ³ is powerful for each i. The condition
a²pᵢ³ ∈ [n², (n+1)²) is equivalent to the interval
[n/pᵢ^{3/2}, (n+1)/pᵢ^{3/2}) containing an integer, which holds
whenever frac(n/pᵢ^{3/2}) > 1 − 1/pᵢ^{3/2}.

By Besicovitch's theorem (1940), the numbers 1, p₁^{−3/2}, …, p_M^{−3/2}
are Q-linearly independent. Kronecker's simultaneous approximation
theorem then guarantees infinitely many n achieving all M fractional-part
conditions simultaneously, giving h(n) ≥ M.

## Mathlib gaps

The combined Besicovitch–Kronecker consequence is axiomatized (sorry)
as `simultaneous_approx_primes`. Both results are classical and
elementary but absent from Mathlib4 as of May 2026.
-/

import Mathlib

open Filter Finset Nat

/-! ## Nat.Powerful -/

/-- A natural number n is *powerful* (also called *squarefull*) if every
prime factor p of n satisfies p² ∣ n, and n ≥ 1. -/
def Nat.Powerful (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ p ∈ n.primeFactors, p ^ 2 ∣ n

instance : DecidablePred Nat.Powerful := fun n => by
  unfold Nat.Powerful
  exact instDecidableAnd

/-! ## erdos_942.h -/

/-- h(n) counts powerful integers in [n², (n+1)²). -/
def erdos_942.h (n : ℕ) : ℕ :=
  ((Finset.Ico (n ^ 2) ((n + 1) ^ 2)).filter Nat.Powerful).card

/-! ## Golomb parametrization helpers -/

/-
a² · p³ is powerful when a ≥ 1 and p is prime.
-/
lemma powerful_of_sq_mul_cube {a p : ℕ} (ha : 1 ≤ a) (hp : p.Prime) :
    Nat.Powerful (a ^ 2 * p ^ 3) := by
  refine' And.intro _ _;
  · exact Nat.mul_pos ( pow_pos ( zero_lt_one.trans_le ha ) 2 ) ( pow_pos hp.pos 3 );
  · simp +zetaDelta at *;
    intro q hq hq' _ _; rcases hq.dvd_mul.1 hq' with ( hq' | hq' ) <;> simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
    · exact dvd_mul_of_dvd_left ( pow_dvd_pow_of_dvd ( hq.dvd_iff_not_coprime.mpr hq' ) 2 ) _;
    · simp_all +decide [ Nat.coprime_primes, sq ];
      exact ⟨ a * a * p, by ring ⟩

/-
If a²p³ = b²q³ with p ≠ q both prime, then contradiction.
This is the distinctness argument: different prime cubes in the Golomb
representation give different powerful numbers.
-/
lemma sq_mul_cube_injective {a b p q : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h : a ^ 2 * p ^ 3 = b ^ 2 * q ^ 3) : False := by
  apply_fun fun x => x.factorization p at h ; simp_all +decide [ hp.ne_zero, hq.ne_zero ] ;
  simp_all +decide [ hp.ne_zero, hq.ne_zero, Nat.factorization_mul, show a ≠ 0 by linarith, show b ≠ 0 by linarith ];
  omega

/-! ## Counting argument -/

/-- If S is a subset of the powerful numbers in [n², (n+1)²),
then |S| ≤ h(n). -/
lemma card_powerful_le_h {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ (Finset.Ico (n ^ 2) ((n + 1) ^ 2)).filter Nat.Powerful) :
    S.card ≤ erdos_942.h n :=
  Finset.card_le_card hS

/-! ## Besicovitch–Kronecker (axiomatized Mathlib gap)

The following lemma encapsulates the combined consequence of:
1. Besicovitch (1940): Q-linear independence of {1, √p₁, …, √p_M}
   for distinct primes, implying Q-LI of {1, p₁^{-3/2}, …, p_M^{-3/2}}
2. Kronecker's simultaneous approximation theorem

Both are classical results but absent from Mathlib4. Together they yield:
for any M distinct primes and any target accuracy, there are infinitely
many n such that each interval [n/pᵢ^{3/2}, (n+1)/pᵢ^{3/2}) contains
a positive integer.

We axiomatize the end result directly: for any M primes, there exist
infinitely many n with M distinct powerful numbers in [n², (n+1)²).
-/

/-- Combined Besicovitch–Kronecker: for any M distinct primes, there
exist arbitrarily large n such that for each prime pᵢ, there exists
aᵢ ≥ 1 with aᵢ²·pᵢ³ ∈ [n², (n+1)²), and all these are distinct.

This is the core Mathlib gap. The proof uses:
- Besicovitch's theorem on Q-linear independence of square roots of
  distinct primes (absent from Mathlib4)
- Kronecker's simultaneous Diophantine approximation theorem
  (absent from Mathlib4)
-/
lemma simultaneous_approx_primes (M : ℕ) (primes : Fin M → ℕ)
    (h_prime : ∀ i, (primes i).Prime) (h_inj : Function.Injective primes)
    (N : ℕ) : ∃ n ≥ N, ∃ (a : Fin M → ℕ),
      (∀ i, 1 ≤ a i) ∧
      (∀ i, n ^ 2 ≤ (a i) ^ 2 * (primes i) ^ 3) ∧
      (∀ i, (a i) ^ 2 * (primes i) ^ 3 < (n + 1) ^ 2) := by
  sorry

/-! ## Assembly: h_frequently_ge from simultaneous_approx_primes -/

/-
The image of Fin M under i ↦ a(i)² · primes(i)³ gives M distinct
powerful members of [n², (n+1)²), hence h(n) ≥ M.
-/
lemma erdos_942.h_ge_of_approx {M : ℕ} {n : ℕ} {primes a : Fin M → ℕ}
    (h_prime : ∀ i, (primes i).Prime) (h_inj : Function.Injective primes)
    (ha_pos : ∀ i, 1 ≤ a i)
    (h_lb : ∀ i, n ^ 2 ≤ (a i) ^ 2 * (primes i) ^ 3)
    (h_ub : ∀ i, (a i) ^ 2 * (primes i) ^ 3 < (n + 1) ^ 2) :
    M ≤ erdos_942.h n := by
  refine' le_trans _ ( card_powerful_le_h _ );
  rotate_left;
  exact Finset.image ( fun i => a i ^ 2 * primes i ^ 3 ) Finset.univ;
  · exact Finset.image_subset_iff.mpr fun i _ => Finset.mem_filter.mpr ⟨ Finset.mem_Ico.mpr ⟨ h_lb i, h_ub i ⟩, powerful_of_sq_mul_cube ( ha_pos i ) ( h_prime i ) ⟩;
  · rw [ Finset.card_image_of_injective _ fun i j hij => _, Finset.card_fin ];
    intro i j hij; have := @sq_mul_cube_injective ( a i ) ( a j ) ( primes i ) ( primes j ) ( ha_pos i ) ( ha_pos j ) ( h_prime i ) ( h_prime j ) ; aesop;

/-
For every M, there are infinitely many n with h(n) ≥ M.

Proof: pick the first M primes. By `simultaneous_approx_primes`
(Besicovitch–Kronecker), for any N there exists n ≥ N with M distinct
powerful numbers in [n², (n+1)²). By `h_ge_of_approx`, h(n) ≥ M.
-/
lemma erdos_942.h_frequently_ge (M : ℕ) :
    ∃ᶠ n in atTop, M ≤ erdos_942.h n := by
  rw [ Filter.frequently_atTop ];
  -- Choose primes: let primes be the function mapping i : Fin M to the (i+2)-th natural number that is prime, or more simply, we can pick any M distinct primes.
  have primes : ∃ (primes : Fin M → ℕ), (∀ i, Nat.Prime (primes i)) ∧ Function.Injective primes := by
    exact ⟨ fun i => Nat.nth Nat.Prime i, fun i => Nat.prime_nth_prime _, fun i j h => by simpa [ Fin.ext_iff ] using Nat.nth_injective ( Nat.infinite_setOf_prime ) h ⟩;
  obtain ⟨primes, h_prime, h_inj⟩ := primes
  intro N
  obtain ⟨n, hn1, hn2⟩ := simultaneous_approx_primes M primes h_prime h_inj N
  use n
  exact ⟨hn1, erdos_942.h_ge_of_approx h_prime h_inj hn2.choose_spec.1 hn2.choose_spec.2.1 hn2.choose_spec.2.2⟩

/-! ## Main theorem -/

/-
Erdős 942 (limsup variant): limsup_{n→∞} h(n) = ∞.
-/
theorem erdos_942.variants.limsup :
    atTop.limsup (((fun (n : ℕ) ↦ (n : ℕ∞)) ∘ erdos_942.h)) = ⊤ := by
  rw [ Filter.limsup_eq ];
  simp +decide [ Filter.eventually_atTop ];
  intro a x hx; contrapose! hx;
  cases' a with a ; norm_cast at *;
  have := erdos_942.h_frequently_ge ( a + 1 ) ; simp_all +decide [ Filter.frequently_atTop ] ;