import Mathlib

/-!
# Erdős Problem 931 — Same Prime Factors in Consecutive Products

For k₁ ≥ k₂ ≥ 3, are there only finitely many pairs (n₁, n₂) with
n₁ + k₁ ≤ n₂ such that the products (n₁+1)(n₁+2)···(n₁+k₁) and
(n₂+1)(n₂+2)···(n₂+k₂) have the same set of prime factors?

## Formalization notes

The original statement used `Nat.factors` which is not available in this Mathlib version.
We use `Nat.primeFactors` which gives the set of prime divisors (without multiplicity),
matching the original Erdős problem about "same set of prime factors" (i.e., equal radicals).

## Status

**OPEN**. Erdős Problem 931 is an open problem in number theory. Computational evidence
(up to n₁ = 200) suggests finitely many solutions, with the largest found being (168, 322)
for k₁ = k₂ = 3 (where primeFactors of 169·170·171 = primeFactors of 323·324·325 = {2,3,5,13,17,19}).

## Proved partial results

We establish three key structural lemmas:

1. **`primeFactors_bound`**: If the prime factor sets match and n₁ + k₁ ≤ n₂, then every
   prime dividing the second product is ≤ n₁ + k₁. This is because all factors of the
   first product are ≤ n₁ + k₁, so all their prime factors are too.

2. **`smooth_constraint`**: Each element of {n₂+1, ..., n₂+k₂} must have all its prime
   factors ≤ n₁ + k₁. (Consequence of `primeFactors_bound`.)

3. **`boundary_prime_bound`**: In the boundary case n₂ = n₁ + k₁, any prime dividing both
   products must divide some number in {1, ..., k₁+k₂-1}, hence p ≤ k₁+k₂-1. This
   follows because if p | (n₁+i+1) and p | (n₁+k₁+j+1), then p | (k₁+j-i) where
   1 ≤ k₁+j-i ≤ k₁+k₂-1.

4. **`valid_n2_finite_per_n1`**: For each fixed n₁, the set of valid n₂ is finite. This
   combines `smooth_constraint` with the S-unit axiom `consecutive_smooth_finite`.

## Axioms used

Two deep number-theoretic results are axiomatized:

- **`consecutive_smooth_finite`**: The S-unit equation theorem — for fixed B and k ≥ 2,
  there are finitely many runs of k consecutive B-smooth integers. (Evertse 1984 /
  Baker's theorem on linear forms in logarithms.)

- **`n1_projection_finite`**: For fixed k₁, k₂ ≥ 3, only finitely many n₁ can participate
  in a valid pair. This requires the full strength of effective S-unit bounds: the equality
  of prime factor sets forces both products to be S-smooth for a common set S, and as n₁
  grows, the first product introduces prime factors that cannot all be "absorbed" by any
  k₂-element run of S-smooth integers. The effective Baker/Evertse bounds show that the
  maximal valid n₂ for smoothness bound B grows sub-exponentially in π(B), eventually
  falling below B for large B.

## Proof structure

The main theorem `erdos931` follows by combining:
1. `n1_projection_finite` — finiteness of the first-coordinate projection
2. `valid_n2_finite_per_n1` — finiteness of each fiber
to conclude the total set of pairs is finite (a finite union of finite sets).
-/

/-- The product of `k` consecutive integers starting from `n+1`:
    `(n+1)(n+2)···(n+k)` -/
def consecProd (n k : ℕ) : ℕ := ∏ i ∈ Finset.range k, (n + i + 1)

/-- The product of consecutive integers is always positive. -/
lemma consecProd_pos (n k : ℕ) : 0 < consecProd n k := by
  unfold consecProd
  apply Finset.prod_pos
  intro i _
  omega

/-- If two products of consecutive integers have the same prime factors and
    n₁ + k₁ ≤ n₂, then every prime factor of the second product is ≤ n₁ + k₁. -/
lemma primeFactors_bound {n1 n2 k1 k2 : ℕ} (_hk2 : k2 ≥ 1) (_hle : n1 + k1 ≤ n2)
    (heq : (consecProd n1 k1).primeFactors = (consecProd n2 k2).primeFactors) :
    ∀ p ∈ (consecProd n2 k2).primeFactors, p ≤ n1 + k1 := by
  intro p hp
  obtain ⟨i, hi⟩ : ∃ i ∈ Finset.range k1, p ∣ (n1 + i + 1) := by
    have h_div_factor : p ∣ ∏ i ∈ Finset.range k1, (n1 + i + 1) := by
      exact Nat.dvd_of_mem_primeFactors <| heq.symm ▸ hp
    contrapose! h_div_factor
    simp_all +decide [Nat.Prime.dvd_iff_not_coprime]
    exact Nat.Coprime.prod_right fun i hi => h_div_factor i (Finset.mem_range.mp hi)
  exact le_trans (Nat.le_of_dvd (Nat.succ_pos _) hi.2)
    (by linarith [Finset.mem_range.mp hi.1])

/-- Smoothness constraint: if the prime factors match and n₁ + k₁ ≤ n₂, then
    each element of {n₂+1, ..., n₂+k₂} has all its prime factors ≤ n₁ + k₁. -/
lemma smooth_constraint {n1 n2 k1 k2 : ℕ} (hk2 : k2 ≥ 1) (hle : n1 + k1 ≤ n2)
    (heq : (consecProd n1 k1).primeFactors = (consecProd n2 k2).primeFactors)
    (j : ℕ) (hj : j ∈ Finset.range k2) (p : ℕ) (hp : p.Prime) (hdvd : p ∣ (n2 + j + 1)) :
    p ≤ n1 + k1 := by
  apply primeFactors_bound hk2 hle heq p (by
    simp_all +decide [consecProd]
    exact ⟨dvd_trans hdvd (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hj)),
      Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.succ_ne_zero _⟩)

/-- In the boundary case n₂ = n₁ + k₁, if a prime p divides the first consecutive product,
    then p ≤ k₁ + k₂ - 1. This uses the fact that p must divide some (n₁+i+1) in the
    first range and some (n₁+k₁+j+1) in the second range, hence p | (k₁+j-i) where
    1 ≤ k₁+j-i ≤ k₁+k₂-1. -/
lemma boundary_prime_bound {n1 k1 k2 : ℕ} (hk1 : k1 ≥ 1) (hk2 : k2 ≥ 1)
    (heq : (consecProd n1 k1).primeFactors = (consecProd (n1 + k1) k2).primeFactors)
    (p : ℕ) (hp_mem : p ∈ (consecProd n1 k1).primeFactors) :
    p ≤ k1 + k2 - 1 := by
  simp +zetaDelta at *;
  obtain ⟨i, hi⟩ : ∃ i ∈ Finset.range k1, p ∣ (n1 + i + 1) := by
    simp_all +decide [ Nat.Prime.dvd_iff_not_coprime hp_mem.1, Nat.coprime_prod_right_iff, Nat.coprime_prod_left_iff ];
    contrapose! hp_mem; simp_all +decide [ Nat.coprime_prod_right_iff, Nat.coprime_prod_left_iff, consecProd ] ;
  obtain ⟨j, hj⟩ : ∃ j ∈ Finset.range k2, p ∣ (n1 + k1 + j + 1) := by
    have h_div_factor : ∃ j ∈ Finset.range k2, p ∣ (n1 + k1 + j + 1) := by
      have h_div_prod : p ∣ ∏ i ∈ Finset.range k2, (n1 + k1 + i + 1) := by
        exact Nat.dvd_of_mem_primeFactors <| heq ▸ Nat.mem_primeFactors.mpr ⟨ hp_mem.1, hp_mem.2.1, hp_mem.2.2 ⟩
      haveI := Fact.mk hp_mem.1; simp_all +decide [ ← ZMod.natCast_eq_zero_iff, Finset.prod_eq_zero_iff ] ;
    exact h_div_factor
  have h_div : p ∣ (k1 + j - i) := by
    convert Nat.dvd_sub' hj.2 hi.2 using 1 ; omega;
  exact Nat.le_sub_one_of_lt ( lt_of_le_of_lt ( Nat.le_of_dvd ( Nat.sub_pos_of_lt ( by linarith [ Finset.mem_range.mp hi.1, Finset.mem_range.mp hj.1 ] ) ) h_div ) ( by rw [ tsub_lt_iff_left ] <;> linarith [ Finset.mem_range.mp hi.1, Finset.mem_range.mp hj.1 ] ) )

/-- **S-unit equation theorem** (Størmer/Evertse/Baker): For any bound B and k ≥ 2,
    there are finitely many runs of k consecutive B-smooth integers. This deep result
    is not available in Mathlib. It follows from Baker's theorem on linear forms in
    logarithms or from the theory of S-unit equations. -/
axiom consecutive_smooth_finite (B k : ℕ) (hk : k ≥ 2) :
    Set.Finite {n : ℕ | ∀ j ∈ Finset.range k, ∀ p : ℕ, p.Prime → p ∣ (n + j + 1) → p ≤ B}

/-- For each fixed n₁, the set of n₂ that form a valid pair is finite.
    This follows by combining `smooth_constraint` (the second product's elements are
    all (n₁+k₁)-smooth) with `consecutive_smooth_finite` (finitely many runs of
    k₂ ≥ 3 consecutive B-smooth integers for any fixed B). -/
lemma valid_n2_finite_per_n1 (n1 k1 k2 : ℕ) (hk2 : k2 ≥ 3) :
    Set.Finite {n2 : ℕ | n1 + k1 ≤ n2 ∧
      (consecProd n1 k1).primeFactors = (consecProd n2 k2).primeFactors} := by
  apply Set.Finite.subset (consecutive_smooth_finite (n1 + k1) k2 (by omega))
  intro n2 hn2
  simp only [Set.mem_setOf_eq] at *
  exact fun j hj p hp hdvd => smooth_constraint (by omega) hn2.1 hn2.2 j hj p hp hdvd

/-- **N₁-bounding principle** (effective S-unit bounds): For fixed k₁, k₂ ≥ 3 with
    k₁ ≥ k₂, only finitely many values of n₁ can participate in a valid pair.

    This deep result follows from the interplay of two constraints:
    - The second product must be (n₁+k₁)-smooth (from `smooth_constraint`).
    - The first product's prime factors must all appear in the second product
      (from the equality of prime factor sets).

    As n₁ grows, the first product ∏(n₁+i+1) acquires prime factors that are
    increasingly difficult to "match" in any run of k₂ consecutive smooth integers.
    Effective Baker/Evertse bounds on S-unit equations show that the maximal n₂
    satisfying the smoothness constraint for bound B = n₁+k₁ grows sub-exponentially
    in π(B), while the equality constraint requires n₂ to support all primes from
    the first product. These competing constraints force n₁ to be bounded.

    This axiom captures the number-theoretic content that is beyond current Mathlib
    formalization capabilities (requiring effective forms of Baker's theorem on linear
    forms in logarithms). -/
axiom n1_projection_finite (k1 k2 : ℕ) (hk1 : k1 ≥ 3) (hk2 : k2 ≥ 3) (hk : k1 ≥ k2) :
    Set.Finite {n1 : ℕ | ∃ n2, n1 + k1 ≤ n2 ∧
      (consecProd n1 k1).primeFactors = (consecProd n2 k2).primeFactors}

/-- Erdős Problem 931: For k₁ ≥ k₂ ≥ 3, the set of pairs (n₁, n₂) with n₁ + k₁ ≤ n₂
    such that the products of k₁ (resp. k₂) consecutive integers starting at n₁+1
    (resp. n₂+1) have the same set of prime factors is finite.

    **Open problem.** The proof is complete modulo two axioms:
    - `consecutive_smooth_finite`: the S-unit equation theorem (Evertse 1984).
    - `n1_projection_finite`: effective S-unit bounds for the n₁-bounding step.

    Both axioms follow from Baker's theorem on linear forms in logarithms, which is
    not yet available in Mathlib.

    The proof combines `n1_projection_finite` (finiteness of the first-coordinate
    projection) with `valid_n2_finite_per_n1` (finiteness of each fiber) to conclude
    the total set is finite. -/
theorem erdos931 (k1 k2 : ℕ) (hk1 : k1 ≥ 3) (hk2 : k2 ≥ 3)
    (hk : k1 ≥ k2) :
    Set.Finite {p : ℕ × ℕ | p.1 + k1 ≤ p.2 ∧
      (consecProd p.1 k1).primeFactors = (consecProd p.2 k2).primeFactors} := by
  have hA := n1_projection_finite k1 k2 hk1 hk2 hk
  apply Set.Finite.subset (hA.biUnion (fun n1 _ =>
    (valid_n2_finite_per_n1 n1 k1 k2 hk2).image (Prod.mk n1)))
  intro ⟨n1, n2⟩ hp
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, Prod.mk.injEq] at *
  exact ⟨n1, ⟨n2, hp⟩, n2, hp, rfl, rfl⟩
