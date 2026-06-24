You can’t finish `no_carmichael_giuga : False` from these hypotheses without solving the open core of Agoh–Giuga.  
So the right “max progress” is to push the `sorry` down to the genuine frontier.

In [AgohGiuga.lean](/Users/patrickkavanagh/math/results_v07/d7b59133/d7b59133-886a-40d1-976d-c7d25e207592_aristotle/RequestProject/AgohGiuga.lean), this compiled block gives substantial formal progress and leaves only the truly open remainder:

```lean
import Mathlib

open Finset

lemma no_giuga_two_factors (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q)
    (hgiuga_p : p ∣ (q - 1)) (hgiuga_q : q ∣ (p - 1)) : False := by
  linarith [ Nat.le_of_dvd ( Nat.sub_pos_of_lt hp.one_lt ) hgiuga_q, Nat.sub_add_cancel hp.pos, Nat.sub_add_cancel hq.pos ]

lemma no_two_prime_factors_carmichael_giuga (n : ℕ) (hn : n > 1) (hcomp : ¬ Nat.Prime n)
    (hsqfree : Squarefree n)
    (hkorselt : ∀ p : ℕ, Nat.Prime p → p ∣ n → (p - 1) ∣ (n - 1))
    (hgiuga : ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∣ (n / p - 1)) :
    n.primeFactors.card ≠ 2 := by
  intro hcard2
  obtain ⟨p, q, hpq, hpf⟩ := Finset.card_eq_two.mp hcard2
  have hp_mem : p ∈ n.primeFactors := by simpa [hpf]
  have hq_mem : q ∈ n.primeFactors := by simpa [hpf]
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_mem
  have hq_prime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq_mem
  have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp_mem
  have hq_dvd : q ∣ n := Nat.dvd_of_mem_primeFactors hq_mem
  have hmul : p * q = n := by
    calc
      p * q = ∏ r ∈ ({p, q} : Finset ℕ), r := by simp [hpq]
      _ = ∏ r ∈ n.primeFactors, r := by simpa [hpf]
      _ = n := Nat.prod_primeFactors_of_squarefree hsqfree
  have hdiv_p : n / p = q := by
    calc
      n / p = (p * q) / p := by simpa [hmul]
      _ = q := Nat.mul_div_right q hp_prime.pos
  have hdiv_q : n / q = p := by
    calc
      n / q = (p * q) / q := by simpa [hmul]
      _ = p := Nat.mul_div_left p hq_prime.pos
  have hgiuga_p : p ∣ (q - 1) := by simpa [hdiv_p] using hgiuga p hp_prime hp_dvd
  have hgiuga_q : q ∣ (p - 1) := by simpa [hdiv_q] using hgiuga q hq_prime hq_dvd
  rcases lt_or_gt_of_ne hpq with hp_lt_q | hq_lt_p
  · exact no_giuga_two_factors p q hp_prime hq_prime hp_lt_q hgiuga_p hgiuga_q
  · exact no_giuga_two_factors q p hq_prime hp_prime hq_lt_p hgiuga_q hgiuga_p

lemma odd_of_carmichael_giuga (n : ℕ) (hn : n > 1) (hcomp : ¬ Nat.Prime n)
    (hsqfree : Squarefree n)
    (hkorselt : ∀ p : ℕ, Nat.Prime p → p ∣ n → (p - 1) ∣ (n - 1))
    (hgiuga : ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∣ (n / p - 1)) : Odd n := by
  have hcard_ne_zero : n.primeFactors.card ≠ 0 := by
    exact Finset.card_ne_zero.mpr ((Nat.nonempty_primeFactors).2 hn)
  have hcard_ne_one : n.primeFactors.card ≠ 1 := by
    intro h1
    have hisPrimePow : IsPrimePow n := (isPrimePow_iff_card_primeFactors_eq_one).2 h1
    have hprime : Nat.Prime n := (Nat.squarefree_and_prime_pow_iff_prime).1 ⟨hsqfree, hisPrimePow⟩
    exact hcomp hprime
  have hcard_ne_two : n.primeFactors.card ≠ 2 := by
    exact no_two_prime_factors_carmichael_giuga n hn hcomp hsqfree hkorselt hgiuga
  have hcard_ge2 : 2 ≤ n.primeFactors.card := by omega
  have hcard_gt1 : 1 < n.primeFactors.card := by omega
  have hneven : ¬ Even n := by
    intro hEven
    have h2_dvd_n : 2 ∣ n := (even_iff_two_dvd.mp hEven)
    have hn0 : n ≠ 0 := by omega
    have h2_mem : 2 ∈ n.primeFactors := by
      exact (Nat.mem_primeFactors).2 ⟨Nat.prime_two, h2_dvd_n, hn0⟩
    obtain ⟨q, hq_mem, hq_ne2⟩ := Finset.exists_ne_of_one_lt_card hcard_gt1 2
    have hq_prime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq_mem
    have hq_dvd : q ∣ n := Nat.dvd_of_mem_primeFactors hq_mem
    have hqminus1_dvd : q - 1 ∣ n - 1 := hkorselt q hq_prime hq_dvd
    have hqminus1_even : Even (q - 1) := hq_prime.even_sub_one hq_ne2
    have h2_dvd_qminus1 : 2 ∣ q - 1 := even_iff_two_dvd.mp hqminus1_even
    have h2_dvd_nminus1 : 2 ∣ n - 1 := dvd_trans h2_dvd_qminus1 hqminus1_dvd
    have h2_dvd_one : 2 ∣ 1 := by
      have hsub : n - (n - 1) = 1 := by omega
      have htmp : 2 ∣ n - (n - 1) := Nat.dvd_sub h2_dvd_n h2_dvd_nminus1
      simpa [hsub] using htmp
    exact Nat.prime_two.not_dvd_one h2_dvd_one
  exact (Nat.not_even_iff_odd).1 hneven

lemma local_prime_dvd_sum_sub_one (n : ℕ) (hn : n > 1)
    (hgiuga : ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∣ (n / p - 1))
    (p : ℕ) (hp_mem : p ∈ n.primeFactors) :
    p ∣ (∑ q ∈ n.primeFactors, n / q) - 1 := by
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_mem
  have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp_mem
  have hrest_dvd : p ∣ ∑ q ∈ n.primeFactors.erase p, n / q := by
    refine Finset.dvd_sum (fun q hq => ?_)
    have hq_mem : q ∈ n.primeFactors := Finset.mem_of_mem_erase hq
    have hq_prime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq_mem
    have hq_dvd : q ∣ n := Nat.dvd_of_mem_primeFactors hq_mem
    have hq_ne : q ≠ p := Finset.ne_of_mem_erase hq
    have hcop : p.Coprime q := (Nat.coprime_primes hp_prime hq_prime).2 (Ne.symm hq_ne)
    have hmul : q * (n / q) = n := by simpa [Nat.mul_comm] using (Nat.div_mul_cancel hq_dvd)
    exact hcop.dvd_of_dvd_mul_left (by simpa [hmul] using hp_dvd)
  have hdiv_np_sub : p ∣ n / p - 1 := hgiuga p hp_prime hp_dvd
  have hdiv_sum : p ∣ (∑ q ∈ n.primeFactors.erase p, n / q) + (n / p - 1) :=
    Nat.dvd_add hrest_dvd hdiv_np_sub
  have hdiv_pos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hp_dvd) hp_prime.pos
  have hsum_decomp : ((∑ q ∈ n.primeFactors.erase p, n / q) + n / p) = ∑ q ∈ n.primeFactors, n / q := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Finset.sum_erase_add n.primeFactors (fun q => n / q) hp_mem
  have hsub_assoc : ((∑ q ∈ n.primeFactors.erase p, n / q) + n / p) - 1 =
      (∑ q ∈ n.primeFactors.erase p, n / q) + (n / p - 1) := by
    exact Nat.add_sub_assoc (Nat.succ_le_of_lt hdiv_pos) _
  have htarget : (∑ q ∈ n.primeFactors, n / q) - 1 =
      (∑ q ∈ n.primeFactors.erase p, n / q) + (n / p - 1) := by
    rw [← hsum_decomp, hsub_assoc]
  rw [htarget]
  exact hdiv_sum

lemma prod_dvd_of_prime_dvd_each (s : Finset ℕ) (b : ℕ)
    (hprime : ∀ p ∈ s, Nat.Prime p)
    (hdiv : ∀ p ∈ s, p ∣ b) :
    ∏ p ∈ s, p ∣ b := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have ha_prime : Nat.Prime a := hprime a (by simp [ha])
      have hprime_s : ∀ p ∈ s, Nat.Prime p := by
        intro p hp; exact hprime p (by simp [hp])
      have hdiv_a : a ∣ b := hdiv a (by simp [ha])
      have hdiv_s : ∀ p ∈ s, p ∣ b := by
        intro p hp; exact hdiv p (by simp [hp])
      have ih' : ∏ p ∈ s, p ∣ b := ih hprime_s hdiv_s
      have hcop : a.Coprime (∏ p ∈ s, p) := by
        refine Nat.Coprime.prod_right (fun p hp => ?_)
        have hp_prime : Nat.Prime p := hprime_s p hp
        have hp_ne : p ≠ a := by
          intro hpa
          apply ha
          simpa [hpa] using hp
        exact (Nat.coprime_primes ha_prime hp_prime).2 hp_ne.symm
      have hmul_dvd : a * (∏ p ∈ s, p) ∣ b := hcop.mul_dvd_of_dvd_of_dvd hdiv_a ih'
      simpa [Finset.prod_insert ha] using hmul_dvd

lemma giuga_sum_integer_identity (n : ℕ) (hn : n > 1)
    (hsqfree : Squarefree n)
    (hgiuga : ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∣ (n / p - 1)) :
    ∃ k : ℕ, (∑ q ∈ n.primeFactors, n / q) = k * n + 1 := by
  set S : ℕ := ∑ q ∈ n.primeFactors, n / q
  have hdiv_each : ∀ p ∈ n.primeFactors, p ∣ S - 1 := by
    intro p hp
    simpa [S] using local_prime_dvd_sum_sub_one n hn hgiuga p hp
  have hprod_div : ∏ p ∈ n.primeFactors, p ∣ S - 1 :=
    prod_dvd_of_prime_dvd_each n.primeFactors (S - 1)
      (fun p hp => Nat.prime_of_mem_primeFactors hp) hdiv_each
  have hn_div : n ∣ S - 1 := by
    simpa [Nat.prod_primeFactors_of_squarefree hsqfree] using hprod_div
  obtain ⟨k, hk⟩ := hn_div
  have hS_pos : 0 < S := by
    obtain ⟨p, hp⟩ := (Nat.nonempty_primeFactors).2 hn
    have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hterm_pos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hp_dvd) hp_prime.pos
    have hsum_decomp : (∑ q ∈ n.primeFactors.erase p, n / q) + n / p = S := by
      simpa [S, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        Finset.sum_erase_add n.primeFactors (fun q => n / q) hp
    have hterm_le : n / p ≤ S := by
      rw [← hsum_decomp]
      exact Nat.le_add_left _ _
    exact lt_of_lt_of_le hterm_pos hterm_le
  have hS_ge1 : 1 ≤ S := Nat.succ_le_of_lt hS_pos
  refine ⟨k, ?_⟩
  have hEq : S = n * k + 1 := (Nat.sub_eq_iff_eq_add hS_ge1).1 hk
  simpa [S, Nat.mul_comm] using hEq

lemma no_carmichael_giuga (n : ℕ) (hn : n > 1) (hcomp : ¬ Nat.Prime n)
    (hsqfree : Squarefree n)
    (hkorselt : ∀ p : ℕ, Nat.Prime p → p ∣ n → (p - 1) ∣ (n - 1))
    (hgiuga : ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∣ (n / p - 1)) :
    False := by
  have hodd : Odd n := odd_of_carmichael_giuga n hn hcomp hsqfree hkorselt hgiuga
  have hcard_ne_two : n.primeFactors.card ≠ 2 :=
    no_two_prime_factors_carmichael_giuga n hn hcomp hsqfree hkorselt hgiuga
  have hsum_int : ∃ k : ℕ, (∑ q ∈ n.primeFactors, n / q) = k * n + 1 :=
    giuga_sum_integer_identity n hn hsqfree hgiuga
  -- Remaining open part: exclude odd squarefree Carmichael+Giuga numbers in full generality.
  sorry
```

Mathematically, this gives:
1. `n` is odd.
2. Two-prime-factor case is impossible in this context.
3. The key Giuga integrality bridge is formalized: `∑_{p|n} n/p = kn + 1`, equivalently `∑ 1/p - 1/n ∈ ℤ`.

That is the maximal honest progress without resolving the open conjecture itself.