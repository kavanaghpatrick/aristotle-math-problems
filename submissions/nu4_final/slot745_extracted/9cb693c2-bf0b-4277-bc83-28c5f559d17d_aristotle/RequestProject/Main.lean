import Mathlib
import RequestProject.BrocardData

set_option maxHeartbeats 8000000

/-! # Brocard's Conjecture verified for n ∈ [1001, 2000]

For every n ∈ [1001, 2000], between the squares of the n-th and (n+1)-th
primes there are at least four prime numbers.

## Proof strategy

1. For each n we store a **witness tuple** `(pₙ, pₙ₊₁, q₁, q₂, q₃, q₄)` in `getWitness`
   (defined in `BrocardData.lean`), where `pₙ = Nat.nth Nat.Prime n`,
   `pₙ₊₁ = Nat.nth Nat.Prime (n+1)`, and the `qᵢ` are four explicit primes in the
   open interval `(pₙ², pₙ₊₁²)`.

2. `BrocardCheck n` is a decidable proposition asserting all witness conditions
   (primality, prime-counting index, ordering, range).

3. We verify `BrocardCheck` for all 1000 values via 20 chunks of 50, each proved
   by `native_decide`.

4. `brocard_of_check` converts a verified `BrocardCheck n` into the Finset
   cardinality statement using `Nat.nth_count` and an explicit 4-element subset
   argument.
-/

section Helpers

/-- If `p` is prime and `Nat.count Nat.Prime p = n`, then `Nat.nth Nat.Prime n = p`. -/
lemma nth_prime_eq {p n : ℕ} (hp : Nat.Prime p) (hc : Nat.count Nat.Prime p = n) :
    Nat.nth Nat.Prime n = p :=
  hc ▸ Nat.nth_count hp

/-- Given 4 strictly increasing primes in `(a, b)`, the filtered Ioo has card ≥ 4. -/
lemma four_primes_in_Ioo {a b : ℕ} {q1 q2 q3 q4 : ℕ}
    (hq1 : Nat.Prime q1) (hq2 : Nat.Prime q2) (hq3 : Nat.Prime q3) (hq4 : Nat.Prime q4)
    (h1 : a < q1) (h12 : q1 < q2) (h23 : q2 < q3) (h34 : q3 < q4) (h4 : q4 < b) :
    4 ≤ ((Finset.Ioo a b).filter Nat.Prime).card := by
  have hsub : {q1, q2, q3, q4} ⊆ (Finset.Ioo a b).filter Nat.Prime := by
    simp only [Finset.subset_iff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter,
               Finset.mem_Ioo]
    rintro x (rfl | rfl | rfl | rfl) <;> exact ⟨⟨by omega, by omega⟩, by assumption⟩
  have hcard : ({q1, q2, q3, q4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_singleton]
  linarith [Finset.card_le_card hsub]

end Helpers

section Check

/-- The decidable condition checked for each n: the witness data is valid.
    Uses projections instead of pattern matching for clean `Decidable` synthesis. -/
def BrocardCheck (n : Nat) : Prop :=
  let w := getWitness n
  Nat.Prime w.1 ∧ Nat.count Nat.Prime w.1 = n ∧
  Nat.Prime w.2.1 ∧ Nat.count Nat.Prime w.2.1 = n + 1 ∧
  Nat.Prime w.2.2.1 ∧ Nat.Prime w.2.2.2.1 ∧
  Nat.Prime w.2.2.2.2.1 ∧ Nat.Prime w.2.2.2.2.2 ∧
  w.1 * w.1 < w.2.2.1 ∧ w.2.2.1 < w.2.2.2.1 ∧
  w.2.2.2.1 < w.2.2.2.2.1 ∧ w.2.2.2.2.1 < w.2.2.2.2.2 ∧
  w.2.2.2.2.2 < w.2.1 * w.2.1

instance (n : Nat) : Decidable (BrocardCheck n) := by
  unfold BrocardCheck; exact inferInstance

/-- From a valid check, derive the Brocard property at index n. -/
lemma brocard_of_check {n : Nat} (h : BrocardCheck n) :
    4 ≤ ((Finset.Ioo (Nat.nth Nat.Prime n ^ 2) (Nat.nth Nat.Prime (n + 1) ^ 2)).filter
      Nat.Prime).card := by
  simp only [BrocardCheck] at h
  set w := getWitness n
  obtain ⟨hpn, hcn, hpn1, hcn1, hq1, hq2, hq3, hq4, hr1, hr12, hr23, hr34, hr4⟩ := h
  rw [nth_prime_eq hpn hcn, nth_prime_eq hpn1 hcn1, sq, sq]
  exact four_primes_in_Ioo hq1 hq2 hq3 hq4 hr1 hr12 hr23 hr34 hr4

/-- Route from a chunk lemma to a specific n in that chunk's range. -/
lemma chunk_to_range {base : ℕ} (h : ∀ i : Fin 50, BrocardCheck (base + i.val))
    {n : ℕ} (hn1 : base ≤ n) (hn2 : n < base + 50) : BrocardCheck n := by
  have := h ⟨n - base, by omega⟩
  rwa [show base + (n - base) = n from by omega] at this

end Check

section Verification
/-! ### Native verification of all 1000 entries in 20 chunks of 50 -/

set_option maxHeartbeats 32000000 in
private lemma check_1001_1050 : ∀ i : Fin 50, BrocardCheck (1001 + i.val) := by native_decide

set_option maxHeartbeats 32000000 in
private lemma check_1051_1100 : ∀ i : Fin 50, BrocardCheck (1051 + i.val) := by native_decide

set_option maxHeartbeats 32000000 in
private lemma check_1101_1150 : ∀ i : Fin 50, BrocardCheck (1101 + i.val) := by native_decide

set_option maxHeartbeats 32000000 in
private lemma check_1151_1200 : ∀ i : Fin 50, BrocardCheck (1151 + i.val) := by native_decide

set_option maxHeartbeats 32000000 in
private lemma check_1201_1250 : ∀ i : Fin 50, BrocardCheck (1201 + i.val) := by native_decide

set_option maxHeartbeats 32000000 in
private lemma check_1251_1300 : ∀ i : Fin 50, BrocardCheck (1251 + i.val) := by native_decide

set_option maxHeartbeats 32000000 in
private lemma check_1301_1350 : ∀ i : Fin 50, BrocardCheck (1301 + i.val) := by native_decide

set_option maxHeartbeats 32000000 in
private lemma check_1351_1400 : ∀ i : Fin 50, BrocardCheck (1351 + i.val) := by native_decide

set_option maxHeartbeats 32000000 in
private lemma check_1401_1450 : ∀ i : Fin 50, BrocardCheck (1401 + i.val) := by native_decide

set_option maxHeartbeats 32000000 in
private lemma check_1451_1500 : ∀ i : Fin 50, BrocardCheck (1451 + i.val) := by native_decide

set_option maxHeartbeats 32000000 in
private lemma check_1501_1550 : ∀ i : Fin 50, BrocardCheck (1501 + i.val) := by native_decide

set_option maxHeartbeats 32000000 in
private lemma check_1551_1600 : ∀ i : Fin 50, BrocardCheck (1551 + i.val) := by native_decide

set_option maxHeartbeats 32000000 in
private lemma check_1601_1650 : ∀ i : Fin 50, BrocardCheck (1601 + i.val) := by native_decide

set_option maxHeartbeats 32000000 in
private lemma check_1651_1700 : ∀ i : Fin 50, BrocardCheck (1651 + i.val) := by native_decide

set_option maxHeartbeats 32000000 in
private lemma check_1701_1750 : ∀ i : Fin 50, BrocardCheck (1701 + i.val) := by native_decide

set_option maxHeartbeats 32000000 in
private lemma check_1751_1800 : ∀ i : Fin 50, BrocardCheck (1751 + i.val) := by native_decide

set_option maxHeartbeats 32000000 in
private lemma check_1801_1850 : ∀ i : Fin 50, BrocardCheck (1801 + i.val) := by native_decide

set_option maxHeartbeats 32000000 in
private lemma check_1851_1900 : ∀ i : Fin 50, BrocardCheck (1851 + i.val) := by native_decide

set_option maxHeartbeats 32000000 in
private lemma check_1901_1950 : ∀ i : Fin 50, BrocardCheck (1901 + i.val) := by native_decide

set_option maxHeartbeats 32000000 in
private lemma check_1951_2000 : ∀ i : Fin 50, BrocardCheck (1951 + i.val) := by native_decide

end Verification

section MainTheorem

/-- Every n in [1001, 2000] satisfies BrocardCheck. -/
private lemma brocard_check_all (n : ℕ) (hn1 : 1001 ≤ n) (hn2 : n ≤ 2000) :
    BrocardCheck n := by
  rcases le_or_gt n 1050 with h | h
  · exact chunk_to_range check_1001_1050 hn1 (by omega)
  rcases le_or_gt n 1100 with h | h
  · exact chunk_to_range check_1051_1100 (by omega) (by omega)
  rcases le_or_gt n 1150 with h | h
  · exact chunk_to_range check_1101_1150 (by omega) (by omega)
  rcases le_or_gt n 1200 with h | h
  · exact chunk_to_range check_1151_1200 (by omega) (by omega)
  rcases le_or_gt n 1250 with h | h
  · exact chunk_to_range check_1201_1250 (by omega) (by omega)
  rcases le_or_gt n 1300 with h | h
  · exact chunk_to_range check_1251_1300 (by omega) (by omega)
  rcases le_or_gt n 1350 with h | h
  · exact chunk_to_range check_1301_1350 (by omega) (by omega)
  rcases le_or_gt n 1400 with h | h
  · exact chunk_to_range check_1351_1400 (by omega) (by omega)
  rcases le_or_gt n 1450 with h | h
  · exact chunk_to_range check_1401_1450 (by omega) (by omega)
  rcases le_or_gt n 1500 with h | h
  · exact chunk_to_range check_1451_1500 (by omega) (by omega)
  rcases le_or_gt n 1550 with h | h
  · exact chunk_to_range check_1501_1550 (by omega) (by omega)
  rcases le_or_gt n 1600 with h | h
  · exact chunk_to_range check_1551_1600 (by omega) (by omega)
  rcases le_or_gt n 1650 with h | h
  · exact chunk_to_range check_1601_1650 (by omega) (by omega)
  rcases le_or_gt n 1700 with h | h
  · exact chunk_to_range check_1651_1700 (by omega) (by omega)
  rcases le_or_gt n 1750 with h | h
  · exact chunk_to_range check_1701_1750 (by omega) (by omega)
  rcases le_or_gt n 1800 with h | h
  · exact chunk_to_range check_1751_1800 (by omega) (by omega)
  rcases le_or_gt n 1850 with h | h
  · exact chunk_to_range check_1801_1850 (by omega) (by omega)
  rcases le_or_gt n 1900 with h | h
  · exact chunk_to_range check_1851_1900 (by omega) (by omega)
  rcases le_or_gt n 1950 with h | h
  · exact chunk_to_range check_1901_1950 (by omega) (by omega)
  · exact chunk_to_range check_1951_2000 (by omega) (by omega)

/-- **Brocard's conjecture for n ∈ [1001, 2000]**:
    For every n in this range, there are at least four primes between
    the squares of the n-th and (n+1)-th primes. -/
theorem brocard_conjecture_extended_1001_2000 :
    ∀ n : ℕ, 1001 ≤ n → n ≤ 2000 →
      4 ≤ ((Finset.Ioo (n.nth Nat.Prime ^ 2) ((n+1).nth Nat.Prime ^ 2)).filter
        Nat.Prime).card := fun n hn1 hn2 =>
  brocard_of_check (brocard_check_all n hn1 hn2)

end MainTheorem
