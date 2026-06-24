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
  have hall : ∀ p ∈ n.primeFactors, 3 ≤ p := by
    intro p hp; exact giuga_prime_ge_three hn hcomp hsqfree hkorselt hp
  have hS_lt : ∑ p ∈ n.primeFactors, n / p < n := by
    rcases eq_or_lt_of_le hcard3 with h3 | h3
    · exact giuga_sum_lt_card_three hn hsqfree hall h3.symm
    · have h4 : n.primeFactors.card = 4 := by omega
      exact giuga_sum_lt_card_four hn hsqfree hall h4
  have hS_dvd := giuga_n_dvd_sum_sub_one hn hsqfree hgiuga
  have hS_ge := giuga_sum_ge_two hn hcomp hsqfree
  exact absurd (Nat.le_of_dvd (by omega) hS_dvd) (by omega)

end FiveFactors