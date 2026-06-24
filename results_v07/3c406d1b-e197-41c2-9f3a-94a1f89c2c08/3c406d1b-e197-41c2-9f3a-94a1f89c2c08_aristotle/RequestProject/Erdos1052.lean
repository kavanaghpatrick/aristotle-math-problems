import Mathlib

/-- The unitary sigma function: sum of unitary divisors of n.
A divisor d of n is *unitary* if gcd(d, n/d) = 1. -/
def unitarySigma (n : ℕ) : ℕ :=
  ∑ d ∈ (Nat.divisors n).filter (fun d => Nat.Coprime d (n / d)), d

/-- The set of unitary divisors of n. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  (Nat.divisors n).filter (fun d => Nat.Coprime d (n / d))

lemma unitarySigma_eq (n : ℕ) : unitarySigma n = ∑ d ∈ unitaryDivisors n, d := rfl

/-
PROBLEM
For a prime power p^a with a ≥ 1, the unitary divisors are {1, p^a},
so unitarySigma(p^a) = 1 + p^a.

PROVIDED SOLUTION
Unfold unitarySigma. The divisors of p^a are {p^0, p^1, ..., p^a} (use Nat.divisors_prime_pow). For d = p^i, n/d = p^(a-i), and gcd(p^i, p^(a-i)) = p^(min(i,a-i)). The coprimality gcd = 1 holds iff min(i, a-i) = 0, i.e., i = 0 or i = a. So the filtered set is {1, p^a}. The sum is 1 + p^a.

Key steps: use Nat.divisors_prime_pow to rewrite divisors as a map over Finset.range(a+1). Then show the filter condition selects exactly i=0 and i=a. For i with 0 < i < a, show gcd(p^i, p^(a-i)) = p^(min(i,a-i)) ≥ p > 1, so not coprime.
-/
lemma unitarySigma_prime_pow {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : 0 < a) :
    unitarySigma (p ^ a) = 1 + p ^ a := by
      unfold unitarySigma;
      norm_num [ Nat.divisors_prime_pow hp ];
      simp +arith +decide [ Finset.sum_filter, Finset.sum_range_succ', Nat.pow_dvd_pow_iff ];
      rw [ Finset.sum_eq_single ( a - 1 ) ] <;> rcases a with ( _ | _ | a ) <;> simp_all +decide [ Nat.Coprime, Nat.gcd_comm, Nat.pow_succ' ];
      · rcases p with ( _ | _ | p ) <;> simp_all +decide [ Nat.div_eq_of_lt ];
      · rw [ Nat.div_self ( Nat.mul_pos hp.pos ( Nat.mul_pos hp.pos ( pow_pos hp.pos _ ) ) ) ] ; aesop;
      · intro b hb₁ hb₂ hb₃; rw [ Nat.mul_div_mul_left _ _ hp.pos ] at hb₃; rcases p with ( _ | _ | p ) <;> simp_all +decide [ Nat.Coprime ] ;
        rw [ Nat.mul_div_assoc, Nat.gcd_eq_left ] at hb₃ <;> norm_num at *;
        exact pow_dvd_pow _ ( Nat.le_of_lt_succ ( lt_of_le_of_ne ( Nat.le_of_lt_succ hb₁ ) hb₂ ) )

/-
PROBLEM
Multiplicativity: for coprime m, k > 0,
unitarySigma(m * k) = unitarySigma(m) * unitarySigma(k).

PROVIDED SOLUTION
The unitary divisors of m*k biject with pairs (d₁, d₂) of unitary divisors of m and k respectively, via d ↦ (gcd(d,m), gcd(d,k)) with inverse (d₁,d₂) ↦ d₁*d₂. This works because gcd(m,k)=1 means every divisor d of m*k uniquely decomposes as d = d₁*d₂ with d₁|m, d₂|k, gcd(d₁,d₂)=1. Then d is a unitary divisor of m*k iff gcd(d, m*k/d) = 1 iff gcd(d₁*d₂, (m/d₁)*(k/d₂)) = 1 iff gcd(d₁, m/d₁) = 1 and gcd(d₂, k/d₂) = 1 (using coprimality). So ∑ d ∈ unitaryDivisors(m*k), d = ∑ (d₁,d₂) ∈ unitaryDivisors(m) ×ˢ unitaryDivisors(k), d₁*d₂ = (∑ d₁ ∈ unitaryDivisors(m), d₁) * (∑ d₂ ∈ unitaryDivisors(k), d₂).

Use Finset.sum_product' or Finset.sum_biUnion, and Nat.Coprime.divisors_mul for the divisor decomposition.
-/
lemma unitarySigma_mul_coprime {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hc : Nat.Coprime m k) :
    unitarySigma (m * k) = unitarySigma m * unitarySigma k := by
      unfold unitarySigma;
      -- Let's rewrite the divisors of $mk$ in terms of the divisors of $m$ and $k$.
      have h_divisors : (m * k).divisors = Finset.image (fun (d : ℕ × ℕ) => d.1 * d.2) (m.divisors ×ˢ k.divisors) := by
        exact Nat.divisors_mul _ _;
      -- By definition of coprimality, we can split the sum into a product of sums over divisors of $m$ and divisors of $k$.
      have h_split : ∑ d ∈ (m * k).divisors, (if Nat.Coprime d (m * k / d) then d else 0) = ∑ d₁ ∈ m.divisors, ∑ d₂ ∈ k.divisors, (if Nat.Coprime (d₁ * d₂) (m * k / (d₁ * d₂)) then d₁ * d₂ else 0) := by
        rw [ h_divisors, Finset.sum_image ];
        · erw [ Finset.sum_product ];
        · -- Since $m$ and $k$ are coprime, their divisors are also coprime. Therefore, if $d1 * d2 = d1' * d2'$, then $d1$ must equal $d1'$ and $d2$ must equal $d2'$.
          have h_coprime_divisors : ∀ d1 d2 d1' d2', d1 ∣ m → d2 ∣ k → d1' ∣ m → d2' ∣ k → d1 * d2 = d1' * d2' → d1 = d1' ∧ d2 = d2' := by
            intros d1 d2 d1' d2' hd1 hd2 hd1' hd2' h_eq
            have h_div : d1 ∣ d1' ∧ d1' ∣ d1 := by
              exact ⟨ Nat.Coprime.dvd_of_dvd_mul_right ( Nat.Coprime.coprime_dvd_left hd1 <| Nat.Coprime.coprime_dvd_right hd2' hc ) <| h_eq.symm ▸ dvd_mul_right _ _, Nat.Coprime.dvd_of_dvd_mul_right ( Nat.Coprime.coprime_dvd_left hd1' <| Nat.Coprime.coprime_dvd_right hd2 hc ) <| h_eq.symm ▸ dvd_mul_right _ _ ⟩;
            have := Nat.dvd_antisymm h_div.1 h_div.2; aesop;
          exact fun x hx y hy hxy => Prod.ext ( h_coprime_divisors _ _ _ _ ( Nat.dvd_of_mem_divisors ( Finset.mem_product.mp hx |>.1 ) ) ( Nat.dvd_of_mem_divisors ( Finset.mem_product.mp hx |>.2 ) ) ( Nat.dvd_of_mem_divisors ( Finset.mem_product.mp hy |>.1 ) ) ( Nat.dvd_of_mem_divisors ( Finset.mem_product.mp hy |>.2 ) ) hxy |>.1 ) ( h_coprime_divisors _ _ _ _ ( Nat.dvd_of_mem_divisors ( Finset.mem_product.mp hx |>.1 ) ) ( Nat.dvd_of_mem_divisors ( Finset.mem_product.mp hx |>.2 ) ) ( Nat.dvd_of_mem_divisors ( Finset.mem_product.mp hy |>.1 ) ) ( Nat.dvd_of_mem_divisors ( Finset.mem_product.mp hy |>.2 ) ) hxy |>.2 );
      -- Since $m$ and $k$ are coprime, we can simplify the condition for unitary divisors.
      have h_unitary : ∀ d₁ ∈ m.divisors, ∀ d₂ ∈ k.divisors, Nat.Coprime (d₁ * d₂) (m * k / (d₁ * d₂)) ↔ Nat.Coprime d₁ (m / d₁) ∧ Nat.Coprime d₂ (k / d₂) := by
        intro d₁ hd₁ d₂ hd₂
        have h_coprime : Nat.Coprime (d₁ * d₂) (m * k / (d₁ * d₂)) ↔ Nat.Coprime d₁ (m * k / (d₁ * d₂)) ∧ Nat.Coprime d₂ (m * k / (d₁ * d₂)) := by
          rw [ Nat.coprime_mul_iff_left ];
        simp_all +decide [ Nat.mul_div_mul_comm, Nat.Coprime ];
        simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right, Nat.Coprime, Nat.gcd_comm ];
        exact ⟨ fun h => ⟨ h.1.1, h.2.2 ⟩, fun h => ⟨ ⟨ h.1, Nat.Coprime.coprime_dvd_right ( Nat.div_dvd_of_dvd hd₂.1 ) ( Nat.Coprime.coprime_dvd_left ( hd₁.1 ) hc ) ⟩, Nat.Coprime.coprime_dvd_right ( Nat.div_dvd_of_dvd hd₁.1 ) ( Nat.Coprime.coprime_dvd_left ( hd₂.1 ) ( Nat.Coprime.symm hc ) ), h.2 ⟩ ⟩;
      simp_all +decide [ Finset.sum_ite ];
      simp +decide only [Finset.sum_filter, Finset.sum_mul _ _ _];
      exact Finset.sum_congr rfl fun i hi => by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun j hj => by aesop;

/-
PROVIDED SOLUTION
Unfold unitarySigma. Nat.divisors 1 = {1}, and Nat.Coprime 1 (1/1) = Nat.Coprime 1 1 = True, so the filter keeps {1}, and the sum is 1. Use simp/decide.
-/
lemma unitarySigma_one : unitarySigma 1 = 1 := by
  native_decide +revert

/-
PROBLEM
Erdős Problem 1052: No odd unitary perfect number exists.

PROVIDED SOLUTION
Use strong induction on n. For odd n > 1:

Case 1: n is a prime power. There exist p prime and a ≥ 1 with n = p^a. Since n is odd, p is odd. By `unitarySigma_prime_pow`, σ*(p^a) = 1 + p^a. The equation 1 + p^a = 2*p^a implies p^a = 1, contradicting a ≥ 1 and p ≥ 2.

Case 2: n is not a prime power. Then n has at least 2 distinct prime factors. We can write n = m * k where m, k > 1, gcd(m,k) = 1 (e.g., take the smallest prime factor p, let m = p^(v_p(n)), k = n/m). Use `Nat.exists_Coprime_factor_of_not_isPrimePow` or manually extract two coprime factors > 1. By `unitarySigma_mul_coprime`, σ*(n) = σ*(m) * σ*(k). Both m and k are odd (as divisors of odd n) and > 1. The key observation: σ*(m) is even and σ*(k) is even. Each is even because 1 and m are both unitary divisors of m (since gcd(1, m) = 1 and gcd(m, 1) = 1), and 1 + m is even (both odd, sum is even), and the remaining unitary divisors also pair up under d ↦ m/d. More precisely, for odd m > 1, we can extract a prime factor p of m, write m = p^a * m' with a ≥ 1 and gcd(p^a, m') = 1. If m' = 1, σ*(m) = 1 + p^a which is even (p odd). If m' > 1, by multiplicativity σ*(m) = σ*(p^a) * σ*(m') = (1+p^a) * σ*(m'), and (1+p^a) is even, so σ*(m) is even.

So σ*(n) = σ*(m) * σ*(k) where both are even, meaning 4 | σ*(n). But 2*n ≡ 2 (mod 4) since n is odd (n ≡ 1 or 3 mod 4, so 2n ≡ 2 or 6 ≡ 2 mod 4). This gives 4 | 2n which is false. Contradiction.

Key Mathlib facts to use: Nat.exists_prime_and_dvd (to extract prime factors), Nat.IsPrimePow for case analysis, Nat.minFac for extracting smallest prime factor, pow_pos, Nat.Coprime properties. For the mod 4 argument, use Nat.even_mul to show 2*2 | σ*(m)*σ*(k), and Nat.odd_mul/Odd to show ¬(4 | 2*n).
-/
theorem erdos1052 (n : ℕ) (hn : n > 1) (hodd : Odd n)
    (hperf : unitarySigma n = 2 * n) : False := by
      -- Let's consider the two cases: $n$ is a prime power or $n$ is not a prime power.
      by_cases h_prime_power : ∃ p a, Nat.Prime p ∧ a > 0 ∧ n = p^a;
      · obtain ⟨ p, a, hp, ha, rfl ⟩ := h_prime_power; simp_all +decide [ Nat.divisors_prime_pow ] ;
        rw [ unitarySigma_prime_pow hp ha ] at hperf ; linarith [ pow_lt_pow_right₀ hp.one_lt ha ] ;
      · -- Since $n$ is not a prime power, it has at least two distinct prime factors. We can write $n$ as a product of two coprime factors greater than 1.
        obtain ⟨m, k, hm, hk, hmk⟩ : ∃ m k, 1 < m ∧ 1 < k ∧ m * k = n ∧ Nat.Coprime m k := by
          obtain ⟨ p, hp₁, hp₂ ⟩ := Nat.exists_prime_and_dvd hn.ne';
          -- Since $p$ is a prime factor of $n$, we can write $n$ as $p^a * m$ where $a \geq 1$ and $m$ is not divisible by $p$.
          obtain ⟨a, m, ha, hm⟩ : ∃ a m, a > 0 ∧ n = p^a * m ∧ ¬p ∣ m := by
            exact ⟨ Nat.factorization n p, n / p ^ Nat.factorization n p, Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by aesop ) ), by rw [ Nat.mul_div_cancel' ( Nat.ordProj_dvd _ _ ) ], Nat.not_dvd_ordCompl ( by aesop ) ( by aesop ) ⟩;
          use p^a, m;
          exact ⟨ one_lt_pow₀ hp₁.one_lt ha.ne', Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by aesop_cat, by aesop_cat ⟩, hm.1.symm, Nat.Coprime.pow_left _ <| hp₁.coprime_iff_not_dvd.mpr hm.2 ⟩;
        -- By the multiplicativity of the unitary sigma function, we have $\sigma^*(n) = \sigma^*(m) \cdot \sigma^*(k)$.
        have h_sigma_mul : unitarySigma n = unitarySigma m * unitarySigma k := by
          convert unitarySigma_mul_coprime ( pos_of_gt hm ) ( pos_of_gt hk ) hmk.2 using 1 ; aesop;
        -- Since $m$ and $k$ are both odd and greater than 1, $\sigma^*(m)$ and $\sigma^*(k)$ are both even.
        have h_even_m : Even (unitarySigma m) := by
          -- Since $m$ is odd and greater than 1, we can write $m$ as a product of its prime factors.
          obtain ⟨p, a, hp, ha, hm_eq⟩ : ∃ p a, Nat.Prime p ∧ a > 0 ∧ m = p^a * (m / p^a) ∧ Nat.Coprime (p^a) (m / p^a) := by
            use Nat.minFac m, Nat.factorization m (Nat.minFac m);
            exact ⟨ Nat.minFac_prime hm.ne', Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( Nat.mem_primeFactors.mpr ⟨ Nat.minFac_prime hm.ne', Nat.minFac_dvd m, by aesop ⟩ ) ), Eq.symm ( Nat.mul_div_cancel' ( Nat.ordProj_dvd _ _ ) ), Nat.Coprime.pow_left _ ( Nat.Prime.coprime_iff_not_dvd ( Nat.minFac_prime hm.ne' ) |>.2 ( Nat.not_dvd_ordCompl ( Nat.minFac_prime hm.ne' ) ( by aesop ) ) ) ⟩;
          -- By the multiplicativity of the unitary sigma function, we have $\sigma^*(m) = \sigma^*(p^a) \cdot \sigma^*(m / p^a)$.
          have h_sigma_mul_m : unitarySigma m = unitarySigma (p^a) * unitarySigma (m / p^a) := by
            convert unitarySigma_mul_coprime _ _ hm_eq.2 using 1;
            · rw [ ← hm_eq.1 ];
            · exact pow_pos hp.pos _;
            · exact Nat.pos_of_ne_zero ( by rintro h; simp_all +singlePass );
          -- Since $p$ is odd and $a > 0$, $\sigma^*(p^a) = 1 + p^a$ is even.
          have h_sigma_pa_even : Even (unitarySigma (p^a)) := by
            rw [ unitarySigma_prime_pow hp ha ];
            grind;
          exact h_sigma_mul_m.symm ▸ h_sigma_pa_even.mul_right _
        have h_even_k : Even (unitarySigma k) := by
          -- Since $k$ is odd and greater than 1, we can write $k = p^a \cdot k'$ where $p$ is a prime factor of $k$ and $a \geq 1$.
          obtain ⟨p, a, hp, ha, hk', hk'_coprime⟩ : ∃ p a, Nat.Prime p ∧ a > 0 ∧ k = p^a * (k / p^a) ∧ Nat.Coprime (p^a) (k / p^a) := by
            obtain ⟨ p, hp ⟩ := Nat.exists_prime_and_dvd hk.ne';
            exact ⟨ p, Nat.factorization k p, hp.1, Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by aesop ) ), by rw [ Nat.mul_div_cancel' ( Nat.ordProj_dvd _ _ ) ], by exact Nat.Coprime.pow_left _ ( hp.1.coprime_iff_not_dvd.mpr <| Nat.not_dvd_ordCompl ( by aesop ) <| by aesop ) ⟩;
          -- By the multiplicativity of the unitary sigma function, we have $\sigma^*(k) = \sigma^*(p^a) \cdot \sigma^*(k / p^a)$.
          have h_sigma_mul_k : unitarySigma k = unitarySigma (p^a) * unitarySigma (k / p^a) := by
            rw [ hk', unitarySigma_mul_coprime ];
            · rw [ Nat.mul_div_cancel_left _ ( pow_pos hp.pos _ ) ];
            · exact pow_pos hp.pos _;
            · grind;
            · exact hk'_coprime;
          -- By the properties of the unitary sigma function, we know that $\sigma^*(p^a) = 1 + p^a$.
          have h_sigma_prime_pow : unitarySigma (p^a) = 1 + p^a := by
            exact unitarySigma_prime_pow hp ha;
          grind;
        -- Therefore, $\sigma^*(n)$ is divisible by 4.
        have h_div4 : 4 ∣ unitarySigma n := by
          exact h_sigma_mul.symm ▸ mul_dvd_mul h_even_m.two_dvd h_even_k.two_dvd;
        exact absurd ( Nat.dvd_trans ( by decide : 2 ∣ 4 ) h_div4 ) ( by obtain ⟨ c, rfl ⟩ := hodd; omega )