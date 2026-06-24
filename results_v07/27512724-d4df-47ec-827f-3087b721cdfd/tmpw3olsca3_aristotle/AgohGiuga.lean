import Mathlib

/-!
# Agoh-Giuga Conjecture

The Agoh-Giuga conjecture (Giuga 1950, Agoh 1995) states that no composite
number n satisfies ∑_{a=1}^{n-1} a^{n-1} ≡ -1 (mod n).

**Status**: This is an OPEN conjecture. Any counterexample must have ≥ 4771
prime factors and exceed 10^{19907} (Borwein-Maitland-Skerritt, 2013).

## Approach

We establish the known equivalence: if n is composite and satisfies the sum
condition, then n must simultaneously be a Carmichael number and a Giuga number.
The final step — showing no composite number is both Carmichael and Giuga — is
the hard open part.
-/

open Finset

/-- The power sum S(n) = ∑_{a=0}^{n-1} a^{n-1} -/
noncomputable def powerSum (n : ℕ) : ℕ := ∑ a ∈ Finset.range n, a ^ (n - 1)

/-- A number n is a Giuga number if for every prime p dividing n,
    p divides (n/p - 1). -/
def IsGiuga (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∣ (n / p - 1)

/-- Key lemma: if n > 1 is composite and n ∣ (powerSum n + 1), then n is squarefree. -/
lemma giuga_squarefree (n : ℕ) (hn : n > 1) (hcomp : ¬ Nat.Prime n)
    (hdvd : n ∣ (powerSum n + 1)) : Squarefree n := by
  refine' Nat.squarefree_iff_prime_squarefree.mpr _;
  intro p pp dp;
  have hp_div : p ∣ (powerSum n + 1) := by
    exact dvd_trans ( dvd_of_mul_left_dvd dp ) hdvd;
  have hsum_mod_p : (∑ a ∈ Finset.range n, a ^ (n - 1)) ≡ (∑ a ∈ Finset.range p, a ^ (n - 1)) * (n / p) [MOD p] := by
    have hsum_mod_p : ∀ k : ℕ, (∑ a ∈ Finset.range (k * p), a ^ (n - 1)) ≡ (∑ a ∈ Finset.range p, a ^ (n - 1)) * k [MOD p] := by
      intro k; induction k <;> simp_all +decide [ Nat.succ_mul, ← ZMod.natCast_eq_natCast_iff, Finset.sum_range_add ] ; ring;
    convert hsum_mod_p ( n / p ) using 1 ; rw [ Nat.div_mul_cancel ( dvd_of_mul_left_dvd dp ) ];
  have hp_div_np : p ∣ (n / p) := by
    exact Nat.dvd_div_of_mul_dvd dp;
  simp_all +decide [ Nat.ModEq, Nat.dvd_iff_mod_eq_zero ];
  simp_all +decide [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd ];
  unfold powerSum at *; simp_all +decide ;

/-- Key lemma: if n > 1 and n ∣ (powerSum n + 1), then for every prime p | n,
    we have (p-1) | (n-1) (Korselt/Carmichael condition). -/
lemma giuga_korselt (n : ℕ) (hn : n > 1)
    (hdvd : n ∣ (powerSum n + 1)) (p : ℕ) (hp : Nat.Prime p) (hpn : p ∣ n) :
    (p - 1) ∣ (n - 1) := by
  by_contra h_contra
  obtain ⟨p, hp_prime, hp_div, hp_not_div⟩ : ∃ p, Nat.Prime p ∧ p ∣ n ∧ ¬(p - 1) ∣ (n - 1) := by
    use p;
  have h_sum_mod_p : (∑ a ∈ Finset.range n, a ^ (n - 1)) % p = (∑ a ∈ Finset.range p, a ^ (n - 1)) * (n / p) % p := by
    have h_split_sum : ∑ a ∈ Finset.range (p * (n / p)), a ^ (n - 1) = ∑ k ∈ Finset.range (n / p), ∑ a ∈ Finset.range p, (a + p * k) ^ (n - 1) := by
      induction' n / p with k hk;
      · norm_num;
      · rw [ Nat.mul_succ, Finset.sum_range_add, hk ];
        simp +arith +decide [ add_comm, Finset.sum_range_succ ];
    rw [ Nat.mul_div_cancel' hp_div ] at h_split_sum; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff', mul_comm ] ;
  have h_sum_zero_mod_p : (∑ a ∈ Finset.range p, a ^ (n - 1)) % p = 0 := by
    haveI := Fact.mk hp_prime; simp +decide [ ← ZMod.val_natCast, Nat.add_mod, Nat.pow_mod, Finset.sum_nat_mod ] ;
    obtain ⟨g, hg⟩ : ∃ g : ZMod p, orderOf g = p - 1 := by
      obtain ⟨ g, hg ⟩ := IsCyclic.exists_generator ( α := ( ZMod p )ˣ );
      exact ⟨ g, by rw [ orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hg ] ; simp +decide [ Nat.totient_prime hp_prime ] ⟩;
    have h_sum_ga : ∑ a ∈ Finset.range p, (g * a) ^ (n - 1) = ∑ a ∈ Finset.range p, a ^ (n - 1) := by
      have h_sum_ga : Finset.image (fun a : ZMod p => g * a) (Finset.univ : Finset (ZMod p)) = Finset.univ := by
        refine' Finset.eq_of_subset_of_card_le ( Finset.subset_univ _ ) _;
        rw [ Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ ( show g ≠ 0 from by rintro rfl; rw [ eq_comm ] at hg; rcases p with ( _ | _ | p ) <;> simp_all +decide ) hxy ];
      have h_sum_ga : ∑ a ∈ Finset.univ, (g * a) ^ (n - 1) = ∑ a ∈ Finset.univ, a ^ (n - 1) := by
        conv_rhs => rw [ ← h_sum_ga, Finset.sum_image ( Finset.card_image_iff.mp <| by aesop ) ] ;
      simp_all +decide [ Finset.sum_range, ZMod.natCast_eq_zero_iff ];
      rcases p with ( _ | _ | p ) <;> simp_all +decide [ Fin.sum_univ_succ, ZMod ];
    have h_g_ne_one : g ^ (n - 1) ≠ 1 := by
      exact fun h => hp_not_div <| hg.symm ▸ orderOf_dvd_iff_pow_eq_one.mpr h;
    simp_all +decide [ mul_pow, Finset.mul_sum _ _ _ ];
    rw [ ← Finset.mul_sum _ _ _ ] at h_sum_ga ; exact mul_left_cancel₀ ( sub_ne_zero_of_ne h_g_ne_one ) <| by linear_combination' h_sum_ga;
  obtain ⟨ k, hk ⟩ := hdvd; replace hk := congr_arg ( · % p ) hk; simp_all +decide [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd ] ;
  unfold powerSum at hk; aesop;

/-- Key lemma: if n > 1 and n ∣ (powerSum n + 1), then for every prime p | n,
    we have p | (n/p - 1) (Giuga condition). -/
lemma giuga_condition (n : ℕ) (hn : n > 1)
    (hdvd : n ∣ (powerSum n + 1)) (p : ℕ) (hp : Nat.Prime p) (hpn : p ∣ n) :
    p ∣ (n / p - 1) := by
  have hkorselt : (p - 1) ∣ (n - 1) := giuga_korselt n hn hdvd p hp hpn
  have hsum_mod_p : (∑ a ∈ Finset.range n, a ^ (n - 1)) ≡ (∑ a ∈ Finset.range p, a ^ (n - 1)) * (n / p) [MOD p] := by
    have hsum_split : ∑ a ∈ Finset.range (p * (n / p)), a ^ (n - 1) ≡ (∑ a ∈ Finset.range p, a ^ (n - 1)) * (n / p) [MOD p] := by
      induction' n / p with k hk;
      · rfl;
      · simp_all +decide [ Nat.mul_succ, ← ZMod.natCast_eq_natCast_iff, Finset.sum_range_add ];
    rwa [ Nat.mul_div_cancel' hpn ] at hsum_split;
  have hsum_mod_p_prime : (∑ a ∈ Finset.range p, a ^ (n - 1)) ≡ p - 1 [MOD p] := by
    have h_fermat : ∀ a ∈ Finset.Ico 1 p, a ^ (n - 1) ≡ 1 [MOD p] := by
      intro a ha; have := Nat.totient_prime hp; rw [ ← Nat.mul_div_cancel' hkorselt ] ; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff, pow_mul ] ;
      haveI := Fact.mk hp; rw [ ZMod.pow_card_sub_one_eq_one ( by rw [ Ne.eq_def, ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ha.1 ha.2 ) ] ; norm_num;
    simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
    rw [ ← Finset.sum_range_add_sum_Ico _ hp.pos ];
    rw [ Finset.sum_congr rfl fun x hx => h_fermat x ( Finset.mem_Ico.mp hx |>.1 ) ( Finset.mem_Ico.mp hx |>.2 ) ] ; norm_num [ hp.pos ];
    rw [ zero_pow ( Nat.sub_ne_zero_of_lt hn ) ];
  have hsum_mod_p_final : (∑ a ∈ Finset.range n, a ^ (n - 1)) ≡ - (n / p) [ZMOD p] := by
    simp_all +decide [ ← Int.natCast_modEq_iff ];
    simp_all +decide [ ← ZMod.intCast_eq_intCast_iff, hp.pos ];
  have hdiv_p : (p : ℤ) ∣ (∑ a ∈ Finset.range n, a ^ (n - 1)) + 1 :=
    Int.natCast_dvd_natCast.mpr (dvd_trans hpn hdvd)
  rw [ ← Int.natCast_dvd_natCast ] ; cases le_total ( n / p ) 1 <;> simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_eq_intCast_iff ] ;
  linear_combination' -hdiv_p

/-
PROBLEM
Two-prime-factor case: no product of two distinct primes can satisfy the
    Giuga conditions. If p < q are primes, then p | (q-1) and q | (p-1)
    is impossible since q > p implies q cannot divide p-1 < q.

PROVIDED SOLUTION
Since q | (p - 1) and q is prime with q > p ≥ 2, we have q ≤ p - 1 < p < q, contradiction.
-/
lemma no_giuga_two_factors (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q)
    (hgiuga_p : p ∣ (q - 1)) (hgiuga_q : q ∣ (p - 1)) : False := by
  linarith [ Nat.le_of_dvd ( Nat.sub_pos_of_lt hp.one_lt ) hgiuga_q, Nat.sub_add_cancel hp.pos, Nat.sub_add_cancel hq.pos ]

/-- No composite number is simultaneously Carmichael and Giuga.
    THIS IS THE OPEN PART OF THE CONJECTURE.

    Known results (Borwein-Maitland-Skerritt 2013): any such number must have
    ≥ 4771 prime factors and exceed 10^{19907}. No proof that none exists is known. -/
lemma no_carmichael_giuga (n : ℕ) (hn : n > 1) (hcomp : ¬ Nat.Prime n)
    (hsqfree : Squarefree n)
    (hkorselt : ∀ p : ℕ, Nat.Prime p → p ∣ n → (p - 1) ∣ (n - 1))
    (hgiuga : ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∣ (n / p - 1)) :
    False := by
  sorry

theorem agoh_giuga (n : ℕ) (hn : n > 1) (hcomp : ¬ Nat.Prime n) :
    ¬ (n ∣ (∑ a ∈ Finset.range n, a ^ (n - 1) + 1)) := by
  intro hdvd
  have hdvd' : n ∣ (powerSum n + 1) := hdvd
  exact no_carmichael_giuga n hn hcomp
    (giuga_squarefree n hn hcomp hdvd')
    (giuga_korselt n hn hdvd')
    (giuga_condition n hn hdvd')

/-!
## Five Prime Factors Theorem

We prove that any composite squarefree number satisfying both the Carmichael
(Korselt) and Giuga conditions must have at least 5 prime factors.

The proof uses:
1. All prime factors must be odd (≥ 3) from the Korselt condition
2. The 2-factor case is already ruled out by `no_giuga_two_factors`
3. A CRT argument showing `n ∣ (∑ n/p - 1)`
4. Reciprocal sum bounds: `∑ 1/pᵢ < 1` for ≤ 4 distinct primes ≥ 3
-/

section FiveFactors

/-
PROBLEM
For 3 distinct naturals ≥ 3: sum of pairwise products < triple product.
    Equivalently, 1/a + 1/b + 1/c < 1 for distinct a, b, c ≥ 3.

PROVIDED SOLUTION
WLOG assume a ≤ b ≤ c (the LHS and RHS are symmetric). Since they're distinct: a < b < c, so a+1 ≤ b and b+1 ≤ c. With a ≥ 3: a-1 ≥ 2. The key chain: b*c*(a-1) ≥ 2*b*c. And a*(b+c) < b*(b+c) = b²+b*c ≤ b*c + b*c = 2*b*c (since b < c implies b² < b*c). So b*c*(a-1) ≥ 2*b*c > a*(b+c) = a*b + a*c. Hence a*b*c - b*c > a*b + a*c, i.e., a*b*c > a*b + a*c + b*c. Use rcases le_or_lt a b / rcases le_or_lt b c etc. to establish the ordering, then nlinarith with appropriate product hints.
-/
lemma three_cofactors_lt {a b c : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    b * c + a * c + a * b < a * b * c := by
  rcases a with ( _ | _ | _ | a ) <;> rcases b with ( _ | _ | _ | b ) <;> rcases c with ( _ | _ | _ | c ) <;> norm_num at *;
  cases lt_or_gt_of_ne hab <;> cases lt_or_gt_of_ne hac <;> cases lt_or_gt_of_ne hbc <;> nlinarith [ mul_pos ( Nat.succ_pos a ) ( Nat.succ_pos b ), mul_pos ( Nat.succ_pos a ) ( Nat.succ_pos c ), mul_pos ( Nat.succ_pos b ) ( Nat.succ_pos c ) ]

/-
PROBLEM
For 4 distinct naturals ≥ 3: sum of triple products < quadruple product.
    Equivalently, 1/a + 1/b + 1/c + 1/d < 1 for distinct a, b, c, d ≥ 3.

PROVIDED SOLUTION
WLOG assume a ≤ b ≤ c ≤ d (by symmetry of both sides). Since distinct: a < b < c < d. Use three_cofactors_lt on (a,b,c) to get D₃ := a*b*c - (b*c + a*c + a*b) > 0. Then show D₃ > a*b by proving a*b*c - b*c - a*c - 2*a*b > 0 (equivalently a*b*(c-2) > c*(a+b)). For a ≥ 3, b ≥ 4, c ≥ 5: this equals c*((a-1)*(b-1)-1) - 2*a*b. At minimum a=3,b=4,c=5: 5*7-24 = 11 > 0. Then a*b*c*d - (b*c*d + a*c*d + a*b*d + a*b*c) = d*D₃ - a*b*c. Since D₃ ≥ a*b+1 and d ≥ c+1, d*D₃ ≥ (c+1)*(a*b+1) = a*b*c + c + a*b + 1 > a*b*c. Use rcases le_or_lt to establish the ordering, then nlinarith with product hints.
-/
lemma four_cofactors_lt {a b c d : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) (hd : 3 ≤ d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    b * c * d + a * c * d + a * b * d + a * b * c < a * b * c * d := by
  -- Assume without loss of generality that $a < b < c < d$.
  suffices h_wlog : ∀ {a b c d : ℕ}, 3 ≤ a → a < b → b < c → c < d → a * b * c * d > b * c * d + a * c * d + a * b * d + a * b * c by
    -- By considering all possible orderings of $a, b, c, d$, we can apply the lemma `h_wlog` to each case.
    by_cases h_cases : a < b ∧ b < c ∧ c < d ∨ a < b ∧ b < d ∧ d < c ∨ a < c ∧ c < b ∧ b < d ∨ a < c ∧ c < d ∧ d < b ∨ a < d ∧ d < b ∧ b < c ∨ a < d ∧ d < c ∧ c < b ∨ b < a ∧ a < c ∧ c < d ∨ b < a ∧ a < d ∧ d < c ∨ b < c ∧ c < a ∧ a < d ∨ b < c ∧ c < d ∧ d < a ∨ b < d ∧ d < a ∧ a < c ∨ b < d ∧ d < c ∧ c < a ∨ c < a ∧ a < b ∧ b < d ∨ c < a ∧ a < d ∧ d < b ∨ c < b ∧ b < a ∧ a < d ∨ c < b ∧ b < d ∧ d < a ∨ c < d ∧ d < a ∧ a < b ∨ c < d ∧ d < b ∧ b < a ∨ d < a ∧ a < b ∧ b < c ∨ d < a ∧ a < c ∧ c < b ∨ d < b ∧ b < a ∧ a < c ∨ d < b ∧ b < c ∧ c < a ∨ d < c ∧ c < a ∧ a < b ∨ d < c ∧ c < b ∧ b < a;
    · grind;
    · cases lt_or_gt_of_ne hab <;> cases lt_or_gt_of_ne hac <;> cases lt_or_gt_of_ne had <;> cases lt_or_gt_of_ne hbc <;> cases lt_or_gt_of_ne hbd <;> cases lt_or_gt_of_ne hcd <;> simp +decide [ * ] at h_cases ⊢;
  intro a b c d ha hb hc hd; nlinarith [ mul_le_mul_left' ha b, mul_le_mul_left' ha c, mul_le_mul_left' ha d, mul_le_mul_left' hb c, mul_le_mul_left' hb d, mul_le_mul_left' hc d ] ;

/-
PROBLEM
All prime factors of a Korselt+squarefree+composite number are ≥ 3.
    If 2 | n then n is even, so n-1 is odd; but any other prime q | n has
    (q-1) | (n-1) with q-1 even, contradicting odd n-1.

PROVIDED SOLUTION
p is prime and p ∈ primeFactors, so p ≥ 2. Suppose p = 2. Then 2 | n, so n is even, hence n-1 is odd. Since n is squarefree and composite, n has another prime factor q > 2 (q is odd, so q ≥ 3). By Korselt: (q-1) | (n-1). But q ≥ 3 means q-1 ≥ 2 is even. An even number dividing an odd number is impossible. Contradiction. So p ≠ 2, hence p ≥ 3. Use Nat.mem_primeFactors to extract that p is prime and p | n.
-/
lemma giuga_prime_ge_three {n : ℕ} (hn : n > 1) (hcomp : ¬ Nat.Prime n) (hsqfree : Squarefree n)
    (hkorselt : ∀ p, Nat.Prime p → p ∣ n → (p - 1) ∣ (n - 1))
    {p : ℕ} (hp : p ∈ n.primeFactors) : 3 ≤ p := by
  contrapose! hkorselt; interval_cases p <;> simp_all +decide ;
  -- Since n is even and composite, it must have another prime factor q.
  obtain ⟨q, hq⟩ : ∃ q, Nat.Prime q ∧ q ∣ n ∧ q ≠ 2 := by
    by_contra h_contra; push_neg at h_contra;
    -- If $n$ is even and composite, then $n = 2^k$ for some $k \geq 2$.
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 ^ k := by
      rw [ ← Nat.prod_primeFactorsList hn.ne_bot ] ; rw [ List.prod_eq_pow_single 2 ] ; aesop;
      exact fun x hx hx' => False.elim <| hx <| h_contra x ( Nat.prime_of_mem_primeFactorsList hx' ) <| Nat.dvd_of_mem_primeFactorsList hx';
    rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.squarefree_pow_iff ];
  exact ⟨ q, hq.1, hq.2.1, by exact fun h => absurd ( dvd_trans ( even_iff_two_dvd.mp ( hq.1.even_sub_one hq.2.2 ) ) h ) ( by rw [ ← even_iff_two_dvd ] ; simpa [ Nat.even_sub hn.le ] using hp.1.even ) ⟩

/-
PROBLEM
A squarefree composite Giuga number has ≥ 3 prime factors,
    since the 2-factor case is ruled out by `no_giuga_two_factors`.

PROVIDED SOLUTION
Since n is squarefree and composite (and n > 1), n has at least 2 distinct prime factors, so card ≥ 2. If card = 2, use Finset.card_eq_two to get primeFactors = {p, q} with p ≠ q. Both are prime and divide n. Since n is squarefree with exactly 2 prime factors, n = p * q. From Giuga: p | (n/p - 1) = (q - 1) and q | (n/q - 1) = (p - 1). WLOG p < q (or use lt_or_gt_of_ne). Apply no_giuga_two_factors to get False. So card ≥ 3.
-/
lemma giuga_card_ge_three {n : ℕ} (hn : n > 1) (hcomp : ¬ Nat.Prime n) (hsqfree : Squarefree n)
    (hgiuga : ∀ p, Nat.Prime p → p ∣ n → p ∣ (n / p - 1)) :
    3 ≤ n.primeFactors.card := by
  contrapose! hgiuga;
  interval_cases _ : Finset.card n.primeFactors <;> simp_all +decide [ Nat.primeFactors_mul ];
  · aesop;
  · obtain ⟨ p, hp ⟩ := Finset.card_eq_one.mp ‹_›;
    -- If $n$ has exactly one prime factor $p$, then $n = p^k$ for some $k$.
    obtain ⟨k, hk⟩ : ∃ k, n = p^k := by
      exact ⟨ n.factorization p, by nth_rw 1 [ ← Nat.factorization_prod_pow_eq_self ( by positivity : n ≠ 0 ) ] ; rw [ Finsupp.prod ] ; aesop ⟩;
    rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.squarefree_pow_iff ];
    · rw [ Finset.eq_singleton_iff_unique_mem ] at hp ; aesop;
    · rw [ Nat.squarefree_pow_iff ] at hsqfree <;> aesop;
  · -- Let's obtain the two prime factors of n.
    obtain ⟨p, q, hp, hq, hprod⟩ : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ n = p * q := by
      have := Finset.card_eq_two.mp ‹_›;
      obtain ⟨ p, q, hpq, h ⟩ := this; exact ⟨ p, q, Nat.prime_of_mem_primeFactors ( h.symm ▸ Finset.mem_insert_self _ _ ), Nat.prime_of_mem_primeFactors ( h.symm ▸ Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ), hpq, by nth_rw 1 [ ← Nat.prod_primeFactors_of_squarefree hsqfree ] ; rw [ h, Finset.prod_pair hpq ] ⟩ ;
    cases lt_or_gt_of_ne hprod.1 <;> simp_all +decide [ Nat.mul_div_cancel_left _ hp.pos, Nat.mul_div_cancel_left _ hq.pos ];
    · use q;
      rcases p with ( _ | _ | p ) <;> rcases q with ( _ | _ | q ) <;> simp_all +arith +decide [ Nat.mul_div_cancel_left _ ( Nat.succ_pos _ ) ];
      exact Nat.not_dvd_of_pos_of_lt ( Nat.succ_pos _ ) ( by linarith );
    · exact ⟨ p, hp, dvd_mul_right _ _, by rw [ Nat.mul_div_cancel_left _ hp.pos ] ; exact Nat.not_dvd_of_pos_of_lt ( Nat.sub_pos_of_lt ( by nlinarith [ hp.two_le, hq.two_le ] ) ) ( by rw [ tsub_lt_iff_left ] <;> nlinarith [ hp.two_le, hq.two_le ] ) ⟩

/-
PROBLEM
For distinct prime factors p ≠ q of squarefree n, p divides n/q.
    Since n/q = ∏_{r ∈ primeFactors \ {q}} r and p ∈ that set.

PROVIDED SOLUTION
By Nat.prod_primeFactors_sdiff_of_squarefree with t = {q}, we get ∏ r ∈ (primeFactors \ {q}), r = n / q. Since p ∈ primeFactors and p ≠ q, p ∈ primeFactors \ {q}. By Finset.dvd_prod_of_mem, p ∣ ∏ r ∈ (primeFactors \ {q}), r = n / q.
-/
lemma prime_dvd_cofactor {n : ℕ} (hsqfree : Squarefree n)
    {p q : ℕ} (hp : p ∈ n.primeFactors) (hq : q ∈ n.primeFactors) (hpq : p ≠ q) :
    p ∣ n / q := by
  simp +zetaDelta at *;
  refine' Nat.Coprime.dvd_of_dvd_mul_left _ _;
  exacts [ q, hp.1.coprime_iff_not_dvd.mpr fun h => hpq <| by have := Nat.prime_dvd_prime_iff_eq hp.1 hq.1; tauto, Nat.dvd_trans hp.2.1 <| by rw [ Nat.mul_div_cancel' hq.2.1 ] ]

/-
PROBLEM
Each prime factor p divides (∑ n/q) - 1.
    Proof: S - 1 = (n/p - 1) + ∑_{q ≠ p} n/q. Giuga gives p | (n/p - 1),
    and p | n/q for q ≠ p (by `prime_dvd_cofactor`).

PROVIDED SOLUTION
We need to show p | (∑_{q ∈ PF} n/q) - 1. Use Finset.add_sum_erase to split: ∑_{q ∈ PF} n/q = n/p + ∑_{q ∈ PF.erase p} n/q. So (∑ n/q) - 1 = (n/p - 1) + ∑_{q ∈ PF.erase p} n/q (in ℕ, valid since n/p ≥ 1 because p | n and n > 1). The Giuga condition gives p | (n/p - 1). For each q ∈ PF.erase p: q ∈ PF and q ≠ p, so by prime_dvd_cofactor, p | (n/q). By Finset.dvd_sum, p | ∑_{q ∈ PF.erase p} n/q. Then dvd_add gives p | (S - 1). Key: use Nat.add_sub_cancel or Nat.sub_add_cancel to handle the ℕ subtraction.
-/
lemma giuga_sum_mod_prime {n : ℕ} (hn : n > 1) (hsqfree : Squarefree n)
    (hgiuga : ∀ p, Nat.Prime p → p ∣ n → p ∣ (n / p - 1))
    {p : ℕ} (hp : p ∈ n.primeFactors) :
    p ∣ (∑ q ∈ n.primeFactors, n / q) - 1 := by
  -- Using the Giuga condition and prime_dvd_cofactor, we can split the sum into two parts: one where q = p and one where q ≠ p.
  have h_split : (∑ q ∈ n.primeFactors, n / q) - 1 = (n / p - 1) + ∑ q ∈ n.primeFactors \ {p}, n / q := by
    rw [ Finset.sum_eq_add_sum_diff_singleton hp, add_comm ];
    rw [ add_comm, Nat.sub_eq_of_eq_add ] ; linarith [ Nat.sub_add_cancel <| show 1 ≤ n / p from Nat.div_pos ( Nat.le_of_dvd hn.le <| Nat.dvd_of_mem_primeFactors hp ) <| Nat.pos_of_mem_primeFactors hp ] ;
  exact h_split.symm ▸ dvd_add ( hgiuga p ( Nat.prime_of_mem_primeFactors hp ) ( Nat.dvd_of_mem_primeFactors hp ) ) ( Finset.dvd_sum fun q hq => prime_dvd_cofactor hsqfree ( by aesop ) ( by aesop ) ( by aesop ) )

/-
PROBLEM
CRT: n divides (∑ n/p) - 1 for squarefree Giuga numbers.
    By `giuga_sum_mod_prime`, each prime factor divides S - 1.
    By `Finset.prod_primes_dvd`, ∏ primeFactors divides S - 1.
    By `prod_primeFactors_of_squarefree`, ∏ = n.

PROVIDED SOLUTION
Every prime factor p divides (S - 1) by giuga_sum_mod_prime. All elements of primeFactors are prime (by Nat.mem_primeFactors). By Finset.prod_primes_dvd applied to (S - 1), the Finset n.primeFactors, the proof that all elements are prime (fun a ha => (Nat.mem_primeFactors.mp ha).1.prime), and the proof that all divide S-1 (fun a ha => giuga_sum_mod_prime ...), we get ∏_{p ∈ PF} p | (S - 1). By Nat.prod_primeFactors_of_squarefree hsqfree, ∏ = n. So n | (S - 1).
-/
lemma giuga_n_dvd_sum_sub_one {n : ℕ} (hn : n > 1) (hsqfree : Squarefree n)
    (hgiuga : ∀ p, Nat.Prime p → p ∣ n → p ∣ (n / p - 1)) :
    n ∣ (∑ p ∈ n.primeFactors, n / p) - 1 := by
  rw [ ← Nat.prod_primeFactors_of_squarefree hsqfree ];
  apply Finset.prod_primes_dvd;
  · exact fun p hp => Nat.prime_iff.mp <| Nat.prime_of_mem_primeFactors hp;
  · rw [ Nat.prod_primeFactors_of_squarefree hsqfree ];
    intro p hp;
    convert giuga_sum_mod_prime hn hsqfree hgiuga hp using 1

/-
PROBLEM
∑ n/p < n when n has exactly 3 prime factors all ≥ 3.
    Extract primes via `card_eq_three`, use `prod_primeFactors_of_squarefree`
    to get n = xyz, then apply `three_cofactors_lt`.

PROVIDED SOLUTION
By Finset.card_eq_three.mp hcard, obtain x, y, z with hxy : x ≠ y, hxz : x ≠ z, hyz : y ≠ z, hpf : primeFactors = {x, y, z}. By hall, x ≥ 3, y ≥ 3, z ≥ 3. By Nat.prod_primeFactors_of_squarefree hsqfree, n = ∏ p ∈ PF, p. Rewrite with hpf: n = ∏ p ∈ {x,y,z}, p = x * y * z (use Finset.prod_pair and Finset.prod_singleton, or Finset.prod_insert with the membership conditions). Then rewrite ∑ p ∈ PF, n/p with hpf: ∑ p ∈ {x,y,z}, n/p. Compute each term: n/x = y*z, n/y = x*z, n/z = x*y (using Nat.mul_div_cancel_left or similar with the product structure). So the sum = y*z + x*z + x*y. Apply three_cofactors_lt with ha := hall x, hb := hall y, hc := hall z. This gives y*z + x*z + x*y < x*y*z = n.
-/
lemma giuga_sum_lt_card_three {n : ℕ} (hn : n > 1) (hsqfree : Squarefree n)
    (hall : ∀ p ∈ n.primeFactors, 3 ≤ p) (hcard : n.primeFactors.card = 3) :
    ∑ p ∈ n.primeFactors, n / p < n := by
  obtain ⟨ p, q, r, hp, hq, hr, h ⟩ := Finset.card_eq_three.mp hcard ; simp_all +decide [ Finset.sum_pair, Finset.sum_singleton ];
  have h_prod : n = p * q * r := by
    have := Nat.prod_primeFactors_of_squarefree hsqfree; simp_all +decide [ Finset.prod_pair, mul_assoc ] ;
  rcases p with ( _ | _ | p ) <;> rcases q with ( _ | _ | q ) <;> rcases r with ( _ | _ | r ) <;> simp_all +decide [ Nat.mul_assoc, Nat.mul_div_assoc ];
  rcases p with ( _ | _ | p ) <;> rcases q with ( _ | _ | q ) <;> rcases r with ( _ | _ | r ) <;> simp_all! +arith +decide;
  · nlinarith only [ hn ];
  · nlinarith only [ mul_pos ( Nat.succ_pos p ) ( Nat.succ_pos r ) ];
  · grind;
  · nlinarith only [ mul_pos ( Nat.succ_pos p ) ( Nat.succ_pos q ), mul_pos ( Nat.succ_pos p ) ( Nat.succ_pos r ), mul_pos ( Nat.succ_pos q ) ( Nat.succ_pos r ) ]

/-
PROBLEM
∑ n/p < n when n has exactly 4 prime factors all ≥ 3.
    Extract primes via `card_eq_four`, use `prod_primeFactors_of_squarefree`
    to get n = xyzw, then apply `four_cofactors_lt`.

PROVIDED SOLUTION
By Finset.card_eq_four.mp hcard, obtain x, y, z, w with all distinctness conditions and hpf : primeFactors = {x, y, z, w}. By hall, all ≥ 3. By Nat.prod_primeFactors_of_squarefree, n = ∏ p ∈ {x,y,z,w}, p = x*y*z*w. The sum ∑ p ∈ {x,y,z,w}, n/p = n/x + n/y + n/z + n/w = y*z*w + x*z*w + x*y*w + x*y*z. Apply four_cofactors_lt with all ≥ 3 and distinct. This gives the sum < x*y*z*w = n.
-/
lemma giuga_sum_lt_card_four {n : ℕ} (hn : n > 1) (hsqfree : Squarefree n)
    (hall : ∀ p ∈ n.primeFactors, 3 ≤ p) (hcard : n.primeFactors.card = 4) :
    ∑ p ∈ n.primeFactors, n / p < n := by
  revert hcard;
  intro hcard
  obtain ⟨x, y, z, w, hxyzw⟩ : ∃ x y z w : ℕ, x ∈ n.primeFactors ∧ y ∈ n.primeFactors ∧ z ∈ n.primeFactors ∧ w ∈ n.primeFactors ∧ x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w ∧ n = x * y * z * w := by
    obtain ⟨x, y, z, w, hxyzw⟩ : ∃ x y z w : ℕ, n.primeFactors = {x, y, z, w} ∧ x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w := by
      rcases Finset.card_eq_succ.mp hcard with ⟨ x, hx ⟩;
      obtain ⟨ t, hxt, hinsert, hcard ⟩ := hx; rcases Finset.card_eq_three.mp hcard with ⟨ y, z, w, hy, hz, hw ⟩ ; use x, y, z, w; aesop;
    have := Nat.prod_primeFactors_of_squarefree hsqfree; simp_all +decide [ mul_assoc ] ;
  have h_sum : ∑ p ∈ n.primeFactors, n / p = y * z * w + x * z * w + x * y * w + x * y * z := by
    have h_sum : n.primeFactors = {x, y, z, w} := by
      rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ hxyzw.1, Finset.insert_subset_iff.mpr ⟨ hxyzw.2.1, Finset.insert_subset_iff.mpr ⟨ hxyzw.2.2.1, Finset.singleton_subset_iff.mpr hxyzw.2.2.2.1 ⟩ ⟩ ⟩ ) ] ; aesop;
    rw [ h_sum, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert ] <;> simp +decide [ * ] ; ring;
    simp +decide [ Nat.mul_assoc, Nat.mul_div_assoc, Nat.ne_of_gt ( Nat.pos_of_mem_primeFactors hxyzw.1 ), Nat.ne_of_gt ( Nat.pos_of_mem_primeFactors hxyzw.2.1 ), Nat.ne_of_gt ( Nat.pos_of_mem_primeFactors hxyzw.2.2.1 ), Nat.ne_of_gt ( Nat.pos_of_mem_primeFactors hxyzw.2.2.2.1 ) ] ; ring;
    rw [ show y * z * w * x / z = y * w * x by rw [ Nat.div_eq_of_eq_mul_left ] <;> linarith [ hall z hxyzw.2.2.1 ], show y * z * w * x / w = y * z * x by rw [ Nat.div_eq_of_eq_mul_left ] <;> linarith [ hall w hxyzw.2.2.2.1 ] ] ; ring;
  have := four_cofactors_lt ( hall x hxyzw.1 ) ( hall y hxyzw.2.1 ) ( hall z hxyzw.2.2.1 ) ( hall w hxyzw.2.2.2.1 ) ; aesop;

/-
PROBLEM
∑ n/p ≥ 2 for composite squarefree n with n > 1.

PROVIDED SOLUTION
Since n > 1 and composite and squarefree, n has at least 2 prime factors. Pick any p ∈ primeFactors. Then n/p ≥ 2 because n has another prime factor q ≠ p, so q | (n/p), and q ≥ 2, hence n/p ≥ q ≥ 2. Since ∑ n/q ≥ n/p ≥ 2. Use Finset.single_le_sum or Finset.le_sum_of_subset to bound the sum from below by one term. The key facts: n.primeFactors.Nonempty (from n > 1, n ≠ 0), and for any p in primeFactors, n / p ≥ 2.
-/
lemma giuga_sum_ge_two {n : ℕ} (hn : n > 1) (hcomp : ¬ Nat.Prime n) (hsqfree : Squarefree n) :
    2 ≤ ∑ p ∈ n.primeFactors, n / p := by
  obtain ⟨ p, hp ⟩ := Nat.exists_prime_and_dvd hn.ne';
  refine' le_trans _ ( Finset.single_le_sum ( fun x _ => Nat.zero_le ( n / x ) ) ( Nat.mem_primeFactors.mpr ⟨ hp.1, hp.2, _ ⟩ ) );
  · obtain ⟨ q, rfl ⟩ := hp.2;
    rcases p with ( _ | _ | p ) <;> rcases q with ( _ | _ | q ) <;> norm_num at *;
    contradiction;
  · linarith

/-- **Main theorem**: Any Carmichael+Giuga number has at least 5 prime factors.
    Proof by contradiction: if card ≤ 4, then card ∈ {3,4} (by `giuga_card_ge_three`).
    The CRT gives n | (S - 1), the reciprocal bound gives S < n, and S ≥ 2.
    But n | (S - 1) with 0 < S - 1 < n is impossible. -/
theorem agoh_giuga_five_factors (n : ℕ) (hn : n > 1)
    (hcomp : ¬ Nat.Prime n) (hsqfree : Squarefree n)
    (hkorselt : ∀ p, Nat.Prime p → p ∣ n → (p - 1) ∣ (n - 1))
    (hgiuga : ∀ p, Nat.Prime p → p ∣ n → p ∣ (n / p - 1)) :
    4 < n.primeFactors.card := by
  by_contra h
  push_neg at h
  have hcard3 := giuga_card_ge_three hn hcomp hsqfree hgiuga
  have hall : ∀ p ∈ n.primeFactors, 3 ≤ p :=
    fun p hp => giuga_prime_ge_three hn hcomp hsqfree hkorselt hp
  have hS_lt : ∑ p ∈ n.primeFactors, n / p < n := by
    rcases eq_or_lt_of_le hcard3 with h3 | h3
    · exact giuga_sum_lt_card_three hn hsqfree hall h3.symm
    · have h4 : n.primeFactors.card = 4 := by omega
      exact giuga_sum_lt_card_four hn hsqfree hall h4
  have hS_dvd := giuga_n_dvd_sum_sub_one hn hsqfree hgiuga
  have hS_ge := giuga_sum_ge_two hn hcomp hsqfree
  exact absurd (Nat.le_of_dvd (by omega) hS_dvd) (by omega)

end FiveFactors

/-!
## Six Prime Factors Theorem

We now show any Carmichael+Giuga number must have ≥ 6 prime factors.
The key: for 5 distinct odd primes (all ≥ 3), the reciprocal sum
1/p₁ + 1/p₂ + 1/p₃ + 1/p₄ + 1/p₅ ≤ 1/3 + 1/5 + 1/7 + 1/9 + 1/11 < 1,
so ∑ n/pᵢ < n, contradicting n | (∑ n/pᵢ - 1) with ∑ n/pᵢ ≥ 2.
-/

section SixFactors

/-
PROBLEM
For 5 values with a≥3, b≥5, c≥7, d≥9, e≥11, the sum of cofactors < product.

PROVIDED SOLUTION
We need b*c*d*e + a*c*d*e + a*b*d*e + a*b*c*e + a*b*c*d < a*b*c*d*e with a≥3, b≥5, c≥7, d≥9, e≥11. Dividing by abcde: 1/a + 1/b + 1/c + 1/d + 1/e ≤ 1/3+1/5+1/7+1/9+1/11 < 1. In ℕ arithmetic: rewrite as a*b*c*d*e - (b*c*d*e + a*c*d*e + a*b*d*e + a*b*c*e + a*b*c*d) > 0. Factor: this equals abcde(1 - 1/a - 1/b - 1/c - 1/d - 1/e). Use nlinarith with product bounds. Try: substitute a=a'+3, b=b'+5, c=c'+7, d=d'+9, e=e'+11 and expand, or just use nlinarith with hints like mul_le_mul and the lower bounds on products of pairs.
-/
lemma five_cofactors_lt {a b c d e : ℕ}
    (ha : 3 ≤ a) (hb : 5 ≤ b) (hc : 7 ≤ c) (hd : 9 ≤ d) (he : 11 ≤ e) :
    b*c*d*e + a*c*d*e + a*b*d*e + a*b*c*e + a*b*c*d < a*b*c*d*e := by
  -- Let's simplify the inequality.
  have h_simp : 1 / (a : ℝ) + 1 / (b : ℝ) + 1 / (c : ℝ) + 1 / (d : ℝ) + 1 / (e : ℝ) < 1 := by
    exact lt_of_le_of_lt ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( one_div_le_one_div_of_le ( by positivity ) ( Nat.cast_le.mpr ha ) ) ( one_div_le_one_div_of_le ( by positivity ) ( Nat.cast_le.mpr hb ) ) ) ( one_div_le_one_div_of_le ( by positivity ) ( Nat.cast_le.mpr hc ) ) ) ( one_div_le_one_div_of_le ( by positivity ) ( Nat.cast_le.mpr hd ) ) ) ( one_div_le_one_div_of_le ( by positivity ) ( Nat.cast_le.mpr he ) ) ) ( by norm_num );
  field_simp at h_simp;
  norm_cast at h_simp; linarith;

/-
PROBLEM
Five distinct odd naturals ≥ 3, when sorted a < b < c < d < e,
    satisfy a ≥ 3, b ≥ 5, c ≥ 7, d ≥ 9, e ≥ 11 since consecutive
    odd numbers differ by ≥ 2.

PROVIDED SOLUTION
Since a is odd with a ≥ 3, b is odd with b > a, we have b ≥ a + 2 ≥ 5 (odd numbers differ by at least 2). Similarly c ≥ b + 2 ≥ 7, d ≥ c + 2 ≥ 9, e ≥ d + 2 ≥ 11. To formalize: obtain ⟨ka, rfl⟩ from hao (Odd a means ∃ k, a = 2*k+1), similarly for b, c, d, e. Then omega handles all the bounds.
-/
lemma distinct_odd_sorted_bounds {a b c d e : ℕ}
    (ha3 : 3 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (hao : Odd a) (hbo : Odd b) (hco : Odd c) (hdo : Odd d) (heo : Odd e) :
    5 ≤ b ∧ 7 ≤ c ∧ 9 ≤ d ∧ 11 ≤ e := by
  obtain ⟨ k, rfl ⟩ := hao; obtain ⟨ l, rfl ⟩ := hbo; obtain ⟨ m, rfl ⟩ := hco; obtain ⟨ n, rfl ⟩ := hdo; obtain ⟨ o, rfl ⟩ := heo; omega;

/-- For 5 distinct odd values ≥ 3 in sorted order, the cofactor sum < product. -/
lemma five_odd_cofactors_lt_sorted {a b c d e : ℕ}
    (ha3 : 3 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (hao : Odd a) (hbo : Odd b) (hco : Odd c) (hdo : Odd d) (heo : Odd e) :
    b*c*d*e + a*c*d*e + a*b*d*e + a*b*c*e + a*b*c*d < a*b*c*d*e := by
  have ⟨hb5, hc7, hd9, he11⟩ := distinct_odd_sorted_bounds ha3 hab hbc hcd hde hao hbo hco hdo heo
  exact five_cofactors_lt ha3 hb5 hc7 hd9 he11

/-
PROBLEM
Sum of cofactors < product for any 5 distinct odd values ≥ 3,
    regardless of order (both sides are symmetric).

PROVIDED SOLUTION
Both LHS (b*c*d*e + a*c*d*e + a*b*d*e + a*b*c*e + a*b*c*d) and RHS (a*b*c*d*e) are symmetric in a,b,c,d,e. So WLOG assume a < b < c < d < e (use suffices with the sorted version). For the sorted case, apply five_odd_cofactors_lt_sorted.

For the WLOG: use `suffices` to reduce to sorted case. The sorted case follows from five_odd_cofactors_lt_sorted. To go from unsorted to sorted, note that both sides are symmetric functions (elementary symmetric polynomials e_4 and e_5), so any permutation of (a,b,c,d,e) preserves both sides. Given 5 pairwise distinct values, we can sort them. Use Finset.sort or manual ordering: consider the 5 values as elements of {a,b,c,d,e}, pick the minimum, second minimum, etc.

Actually, a cleaner approach: work with the cast to ℝ. In ℝ, the inequality is equivalent to 1/a + 1/b + 1/c + 1/d + 1/e < 1. Since all are odd and ≥ 3, each is ≥ 3 and distinct, the sum ∑ 1/x is maximized by the 5 smallest distinct odd values ≥ 3, which are 3,5,7,9,11. So ∑ 1/x ≤ 1/3+1/5+1/7+1/9+1/11 < 1.

To formalize: cast to ℝ. Each term 1/(x:ℝ) ≤ 1/3 if x ≥ 3, but that gives ≤ 5/3 which is too weak. Instead: use that the Finset {a,b,c,d,e} has card 5, all odd, all ≥ 3, distinct. The sum ∑ 1/x over this set is ≤ sum over {3,5,7,9,11}. But this comparison is hard directly.

Better approach: use Finset.sort on the 5 values to get a sorted list, extract elements, use distinct_odd_sorted_bounds, then five_cofactors_lt.

Actually simplest: just cast to ℝ and show 1/a + 1/b + 1/c + 1/d + 1/e < 1 using the fact that each term is ≤ 1 over the corresponding element of {3,5,7,9,11}. To bound: sort the five values. Since they are pairwise distinct odd and ≥ 3, the sorted values a₁ < a₂ < a₃ < a₄ < a₅ satisfy a₁ ≥ 3, a₂ ≥ 5, a₃ ≥ 7, a₄ ≥ 9, a₅ ≥ 11 (by distinct_odd_sorted_bounds). So 1/aᵢ ≤ 1/3, 1/5, 1/7, 1/9, 1/11 respectively, and the sum ≤ 1/3+1/5+1/7+1/9+1/11 < 1. Then the ℕ inequality follows from the ℝ one by field_simp and norm_cast.

Concretely: use the same approach as five_cofactors_lt. Cast to ℝ, use one_div_le_one_div_of_le for each term paired with the right bound. To get the bounds, need to sort. Use List.Sorted and Finset.sort, or just manual case analysis.

Alternatively: much simpler. Just use the ℝ approach directly without sorting. We have 5 distinct odd values ≥ 3. Cast to ℝ: need ∑ 1/x < 1. We know all x ≥ 3, so each 1/x ≤ 1/3. But 5/3 > 1 so this doesn't help. We need the distinctness.

Use: given 5 pairwise distinct odd values ≥ 3, let them be a₁ ≤ a₂ ≤ a₃ ≤ a₄ ≤ a₅ (strict since distinct). Apply distinct_odd_sorted_bounds (after sorting). Then five_cofactors_lt.

For the sorting step: given a,b,c,d,e pairwise distinct, there exists a permutation putting them in sorted order. Since both sides of the inequality are symmetric, the inequality for the sorted version implies it for any order. Formally, we need: there exist a',b',c',d',e' with a' < b' < c' < d' < e' and {a',b',c',d',e'} = {a,b,c,d,e}, and then b'*c'*d'*e' + ... = b*c*d*e + ... (by symmetry).

This symmetry argument is a bit tedious. An alternative: use a Finset-based approach. Define S = {a,b,c,d,e} and argue about ∑_{x ∈ S} (∏ S) / x and ∏ S.

Hmm, let me just try having the subagent use the ℝ approach: cast to ℝ, use that the Finset of values sorted gives bounds, compute in ℝ.
-/
lemma five_odd_cofactors_lt {a b c d e : ℕ}
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) (hd : 3 ≤ d) (he : 3 ≤ e)
    (hao : Odd a) (hbo : Odd b) (hco : Odd c) (hdo : Odd d) (heo : Odd e)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    b*c*d*e + a*c*d*e + a*b*d*e + a*b*c*e + a*b*c*d < a*b*c*d*e := by
  obtain ⟨ k₁, rfl ⟩ := hao; obtain ⟨ k₂, rfl ⟩ := hbo; obtain ⟨ k₃, rfl ⟩ := hco; obtain ⟨ k₄, rfl ⟩ := hdo; obtain ⟨ k₅, rfl ⟩ := heo; ring_nf;
  rcases k₁ with ( _ | _ | k₁ ) <;> rcases k₂ with ( _ | _ | k₂ ) <;> try simp +arith +decide only [ * ] at * <;> omega;
  · rcases k₃ with ( _ | _ | k₃ ) <;> rcases k₄ with ( _ | _ | k₄ ) <;> rcases k₅ with ( _ | _ | k₅ ) <;> try simp +arith +decide only [ * ] at * <;> omega;
    grind +ring;
  · rcases k₃ with ( _ | _ | k₃ ) <;> rcases k₄ with ( _ | _ | k₄ ) <;> rcases k₅ with ( _ | _ | k₅ ) <;> try simp +arith +decide only [ * ] at * <;> omega;
    grind;
  · rcases k₃ with ( _ | _ | k₃ ) <;> rcases k₄ with ( _ | _ | k₄ ) <;> rcases k₅ with ( _ | _ | k₅ ) <;> try simp +arith +decide only [ * ] at * <;> omega;
    · grind;
    · grind;
    · grind +ring;
    · grind +ring

/-
PROVIDED SOLUTION
Since n.primeFactors.card = 5, use Finset.card_eq_succ and Finset.card_eq_four to extract 5 distinct primes a, b, c, d, e with n.primeFactors = {a, b, c, d, e}. All are prime (from primeFactors), all ≥ 3 (from hall), all odd (primes ≥ 3 are odd). By Nat.prod_primeFactors_of_squarefree, n = a*b*c*d*e. The sum ∑ p ∈ PF, n/p = n/a + n/b + n/c + n/d + n/e = b*c*d*e + a*c*d*e + a*b*d*e + a*b*c*e + a*b*c*d. Apply five_odd_cofactors_lt (the symmetric version) with all ≥ 3, all odd (Nat.Prime.odd_of_ne_two since all ≥ 3 hence ≠ 2), all pairwise distinct.

Follow the exact same pattern as giuga_sum_lt_card_four but with 5 elements. Use set_option maxHeartbeats 400000 at the beginning.

Step 1: Extract 5 elements. Use Finset.card_eq_succ repeatedly to get a, b, c, d, e with n.primeFactors = {a, b, c, d, e} and pairwise distinct. Use Finset.card_eq_four for the last 4 elements.

Step 2: Get n = a*b*c*d*e from Nat.prod_primeFactors_of_squarefree.

Step 3: Compute the sum. Rewrite primeFactors as {a,b,c,d,e}, use Finset.sum_insert repeatedly (checking non-membership with the distinctness hypotheses), compute each n/p term using Nat.mul_div_cancel.

Step 4: Apply five_odd_cofactors_lt. Need:
- All ≥ 3: from hall
- All odd: use Nat.Prime.odd_of_ne_two (Nat.prime_of_mem_primeFactors _) (by linarith [hall _ _]) for each
- Pairwise distinct: from the extraction

Step 5: Conclude with linarith or omega.

Important: keep the proof modular. Use `have hpf : n.primeFactors = {a,b,c,d,e}` early, then rewrite everything with hpf.
-/
lemma giuga_sum_lt_card_five {n : ℕ} (hn : n > 1) (hsqfree : Squarefree n)
    (hall : ∀ p ∈ n.primeFactors, 3 ≤ p) (hcard : n.primeFactors.card = 5) :
    ∑ p ∈ n.primeFactors, n / p < n := by
  obtain ⟨a, b, c, d, e, h_eq⟩ : ∃ a b c d e, n.primeFactors = {a, b, c, d, e} ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e := by
    simp_rw +decide [ Finset.card_eq_succ ] at hcard;
    rcases hcard with ⟨ a, t, hat, hinsert, b, u, hbu, huinsert, c, v, hcv, hvinsert, d, w, hdw, hwinsert, e, x, hex, hxinsert, hcard ⟩ ; use a, b, c, d, e; aesop;
  have h_prod : n = a * b * c * d * e := by
    have h_prod : n = (∏ p ∈ n.primeFactors, p) := by
      rw [ Nat.prod_primeFactors_of_squarefree hsqfree ];
    simp +decide [ h_eq, mul_assoc ] at h_prod ⊢ ; linarith
  have h_sum : ∑ p ∈ n.primeFactors, n / p = b * c * d * e + a * c * d * e + a * b * d * e + a * b * c * e + a * b * c * d := by
    simp +decide [ *, Finset.sum_pair, add_assoc ];
    rw [ ← h_prod, h_eq.1 ];
    simp +decide [ *, Finset.sum_pair, Finset.sum_singleton, Nat.mul_div_mul_left ];
    rw [ Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left ] <;> ring <;> contrapose! hall <;> aesop;
  have h_odd : Odd a ∧ Odd b ∧ Odd c ∧ Odd d ∧ Odd e := by
    have h_odd : ∀ p ∈ n.primeFactors, Odd p := by
      exact fun p hp => Nat.Prime.odd_of_ne_two ( Nat.prime_of_mem_primeFactors hp ) ( by linarith [ hall p hp ] );
    grind;
  have h_bounds : 3 ≤ a ∧ 3 ≤ b ∧ 3 ≤ c ∧ 3 ≤ d ∧ 3 ≤ e := by
    exact ⟨ hall a ( h_eq.1.symm ▸ by simp +decide ), hall b ( h_eq.1.symm ▸ by simp +decide ), hall c ( h_eq.1.symm ▸ by simp +decide ), hall d ( h_eq.1.symm ▸ by simp +decide ), hall e ( h_eq.1.symm ▸ by simp +decide ) ⟩;
  have := five_odd_cofactors_lt h_bounds.1 h_bounds.2.1 h_bounds.2.2.1 h_bounds.2.2.2.1 h_bounds.2.2.2.2 h_odd.1 h_odd.2.1 h_odd.2.2.1 h_odd.2.2.2.1 h_odd.2.2.2.2 h_eq.2.1 h_eq.2.2.1 h_eq.2.2.2.1 h_eq.2.2.2.2.1 h_eq.2.2.2.2.2.1 h_eq.2.2.2.2.2.2.1 h_eq.2.2.2.2.2.2.2.1 h_eq.2.2.2.2.2.2.2.2.1 h_eq.2.2.2.2.2.2.2.2.2.1 h_eq.2.2.2.2.2.2.2.2.2.2; linarith;

/-
PROVIDED SOLUTION
Same structure as agoh_giuga_five_factors (which is already proved above). By contradiction: assume card ≤ 5. By giuga_card_ge_three, card ≥ 3, so card ∈ {3,4,5}. Define hall : ∀ p ∈ n.primeFactors, 3 ≤ p := fun p hp => giuga_prime_ge_three hn hcomp hsqfree hkorselt hp. For each case use giuga_sum_lt_card_three/four/five to get ∑ n/p < n. By giuga_n_dvd_sum_sub_one, n | (∑ n/p - 1). By giuga_sum_ge_two, ∑ n/p ≥ 2. Then n | (S-1) with 1 ≤ S-1 < n is impossible. Use omega. Do NOT use no_carmichael_giuga.
-/
theorem agoh_giuga_six_factors (n : ℕ) (hn : n > 1)
    (hcomp : ¬ Nat.Prime n) (hsqfree : Squarefree n)
    (hkorselt : ∀ p, Nat.Prime p → p ∣ n → (p-1) ∣ (n-1))
    (hgiuga : ∀ p, Nat.Prime p → p ∣ n → p ∣ (n/p - 1)) :
    5 < n.primeFactors.card := by
  by_contra h
  push_neg at h
  have hcard3 := giuga_card_ge_three hn hcomp hsqfree hgiuga
  have hall : ∀ p ∈ n.primeFactors, 3 ≤ p :=
    fun p hp => giuga_prime_ge_three hn hcomp hsqfree hkorselt hp
  have hS_lt : ∑ p ∈ n.primeFactors, n / p < n := by
    have hle : n.primeFactors.card ≤ 5 := h
    have hge : 3 ≤ n.primeFactors.card := hcard3
    rcases Nat.eq_or_lt_of_le hge with h3 | h3
    · exact giuga_sum_lt_card_three hn hsqfree hall h3.symm
    · rcases Nat.eq_or_lt_of_le h3 with h4 | h4
      · exact giuga_sum_lt_card_four hn hsqfree hall h4.symm
      · exact giuga_sum_lt_card_five hn hsqfree hall (by omega)
  have hS_dvd := giuga_n_dvd_sum_sub_one hn hsqfree hgiuga
  have hS_ge := giuga_sum_ge_two hn hcomp hsqfree
  exact absurd (Nat.le_of_dvd (by omega) hS_dvd) (by omega)

end SixFactors