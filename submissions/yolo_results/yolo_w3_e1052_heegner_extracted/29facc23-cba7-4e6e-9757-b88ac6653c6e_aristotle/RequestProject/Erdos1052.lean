/-
# Erdős Problem 1052 — Wall k=3 Stratum: Primitive Divisors of Lehmer Sequences

## Mathematical Background

A **Lehmer pair** (α, β) consists of algebraic integers satisfying:
- α + β = √R for some positive integer R
- αβ = Q for some nonzero integer Q
- gcd(R, Q) = 1
- α/β is not a root of unity

The **Lehmer sequence** {Ũ_n} is defined by:
- Ũ_n = (αⁿ - βⁿ)/(α - β)   when n is odd
- Ũ_n = (αⁿ - βⁿ)/(α² - β²)  when n is even

These satisfy the integer recurrence:
- Ũ_0 = 0, Ũ_1 = 1
- Ũ_n = R · Ũ_{n-1} - Q · Ũ_{n-2}  when n ≥ 2 is odd
- Ũ_n = Ũ_{n-1} - Q · Ũ_{n-2}      when n ≥ 2 is even

A prime q is a **primitive divisor** of Ũ_n if q ∣ Ũ_n but q ∤ Ũ_m for all 0 < m < n.

## Main Result

**Theorem (Bilu-Hanrot-Voutier 2001):** For every Lehmer pair and every n > 30,
Ũ_n has a primitive prime divisor.

The Wall k=3 stratum is the special case where 3 ∣ n.

## Proof Status

This theorem was proved by Bilu, Hanrot, and Voutier in:
  "Existence of primitive divisors of Lucas and Lehmer numbers"
  J. reine angew. Math. (Crelle) 539 (2001), 75-122.

Their proof uses Baker's method (linear forms in logarithms of algebraic numbers)
combined with extensive computational verification for small cases.

**No Lean formalization exists.** The required machinery includes:
- Baker's theory of linear forms in logarithms
- Effective bounds on solutions to Thue-Mahler equations
- Computational verification for finitely many exceptional cases
- Theory of cyclotomic polynomials and their divisibility properties

None of this is currently available in Mathlib.

## Notes on the suggested Heegner-point approach

The informal proof outline suggested attacking this via Frey-Hellegouarch curves,
Heegner points, the Gross-Zagier formula, and Kolyvagin's Euler system. While
these are powerful tools in arithmetic geometry, the "bridge" step connecting
primitive-divisor-freeness to bounded Heegner heights (Step 6 in the outline)
is genuinely conjectural — no published work applies Heegner-point descent to
Lehmer primitive-divisor problems. The standard proof via Baker's method is
more direct but equally difficult to formalize.
-/

import Mathlib

open scoped BigOperators

set_option maxHeartbeats 800000

/-! ## Definitions -/

/-- The Lehmer sequence associated to integer parameters R and Q.

If α, β are the roots of x² - √R · x + Q = 0 (so α + β = √R, αβ = Q),
then `LehmerSeq R Q n` equals:
- (αⁿ - βⁿ)/(α - β)   when n is odd
- (αⁿ - βⁿ)/(α² - β²)  when n is even

This is computed via the integer recurrence:
- n odd  (n ≥ 3): Ũ_n = R · Ũ_{n-1} - Q · Ũ_{n-2}
- n even (n ≥ 2): Ũ_n = Ũ_{n-1} - Q · Ũ_{n-2}
-/
def LehmerSeq (R Q : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) =>
    if (n + 2) % 2 = 0
    then LehmerSeq R Q (n + 1) - Q * LehmerSeq R Q n
    else R * LehmerSeq R Q (n + 1) - Q * LehmerSeq R Q n

/-- The complex-valued Lehmer term, defined by the closed-form expression. -/
noncomputable def lehmerTermComplex (α β : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0
  else if n % 2 = 1 then (α ^ n - β ^ n) / (α - β)
  else (α ^ n - β ^ n) / (α ^ 2 - β ^ 2)

/-- Predicate: z is a root of unity (there exists k > 0 with z^k = 1). -/
def IsRootOfUnity (z : ℂ) : Prop := ∃ k : ℕ, 0 < k ∧ z ^ k = 1

/-- A Lehmer pair is specified by coprime nonzero integers R > 0 and Q
with positive discriminant R - 4Q, such that no Lehmer term vanishes
(equivalently, α/β is not a root of unity). -/
structure IsLehmerPair (R Q : ℤ) : Prop where
  R_pos : 0 < R
  Q_ne_zero : Q ≠ 0
  coprime : Int.gcd R Q = 1
  disc_pos : 4 * Q < R
  /-- α/β is not a root of unity, equivalently all Lehmer terms are nonzero. -/
  no_vanishing : ∀ k : ℕ, 0 < k → LehmerSeq R Q k ≠ 0

/-- A prime q is a **primitive divisor** of the n-th Lehmer term if q divides
the n-th term but does not divide any earlier term. -/
def IsPrimitiveDivisor (R Q : ℤ) (n : ℕ) (q : ℕ) : Prop :=
  q.Prime ∧ (↑q : ℤ) ∣ LehmerSeq R Q n ∧
    ∀ m : ℕ, 0 < m → m < n → ¬ ((↑q : ℤ) ∣ LehmerSeq R Q m)

/-! ## Basic properties of the Lehmer sequence -/

@[simp] lemma LehmerSeq_zero (R Q : ℤ) : LehmerSeq R Q 0 = 0 := rfl
@[simp] lemma LehmerSeq_one (R Q : ℤ) : LehmerSeq R Q 1 = 1 := rfl

lemma LehmerSeq_two (R Q : ℤ) : LehmerSeq R Q 2 = 1 := by
  simp [LehmerSeq]

lemma LehmerSeq_three (R Q : ℤ) : LehmerSeq R Q 3 = R - Q := by
  simp [LehmerSeq]

lemma LehmerSeq_four (R Q : ℤ) : LehmerSeq R Q 4 = R - 2 * Q := by
  simp [LehmerSeq]; ring

/-
Recurrence for LehmerSeq at even indices (n + 2 even, i.e. n even).
-/
lemma LehmerSeq_even_succ_succ (R Q : ℤ) (n : ℕ) (hn : n % 2 = 0) :
    LehmerSeq R Q (n + 2) = LehmerSeq R Q (n + 1) - Q * LehmerSeq R Q n := by
  exact if_pos ( by omega )

/-
Recurrence for LehmerSeq at odd indices (n + 2 odd, i.e. n odd).
-/
lemma LehmerSeq_odd_succ_succ (R Q : ℤ) (n : ℕ) (hn : n % 2 = 1) :
    LehmerSeq R Q (n + 2) = R * LehmerSeq R Q (n + 1) - Q * LehmerSeq R Q n := by
  exact if_neg ( by omega )

/-! ## Correspondence between integer recurrence and complex closed form -/

/-- Key algebraic identity: the recurrence for αⁿ - βⁿ. -/
lemma pow_sub_pow_recurrence (α β : ℂ) (n : ℕ) :
    α ^ (n + 2) - β ^ (n + 2) =
      (α + β) * (α ^ (n + 1) - β ^ (n + 1)) - α * β * (α ^ n - β ^ n) := by
  ring

/-
When (α+β)² = R > 0, we have α + β ≠ 0.
-/
lemma sum_ne_zero_of_sq_pos (α β : ℂ) (R : ℤ) (hsum : (α + β) ^ 2 = ↑R)
    (hR : (0 : ℤ) < R) : α + β ≠ 0 := by
  exact fun h => by rw [ h ] at hsum; norm_cast at hsum; aesop;

/-
When α ≠ β and α + β ≠ 0, we have α² - β² ≠ 0.
-/
lemma sq_sub_sq_ne_zero (α β : ℂ) (hne : α ≠ β) (hsum_ne : α + β ≠ 0) :
    α ^ 2 - β ^ 2 ≠ 0 := by
  exact fun h => hne <| mul_left_cancel₀ hsum_ne <| by linear_combination h;

/-
The complex Lehmer term satisfies the even recurrence.
-/
lemma lehmerTermComplex_even_recurrence (α β : ℂ) (R Q : ℤ) (n : ℕ)
    (_hsum : (α + β) ^ 2 = ↑R) (hprod : α * β = ↑Q)
    (hne : α ≠ β) (hsum_ne : α + β ≠ 0) (hn : n % 2 = 0) (hn0 : n ≠ 0) :
    lehmerTermComplex α β (n + 2) =
      lehmerTermComplex α β (n + 1) - ↑Q * lehmerTermComplex α β n := by
  simp [lehmerTermComplex, hn, hn0];
  rw [ if_pos ( by omega ) ] ; ring;
  grind

/-
The complex Lehmer term satisfies the odd recurrence.
-/
lemma lehmerTermComplex_odd_recurrence (α β : ℂ) (R Q : ℤ) (n : ℕ)
    (hsum : (α + β) ^ 2 = ↑R) (hprod : α * β = ↑Q)
    (hne : α ≠ β) (hsum_ne : α + β ≠ 0) (hn : n % 2 = 1) :
    lehmerTermComplex α β (n + 2) =
      ↑R * lehmerTermComplex α β (n + 1) - ↑Q * lehmerTermComplex α β n := by
  unfold lehmerTermComplex;
  grind +extAll

/-
The integer Lehmer sequence agrees with the complex closed-form expression.
This requires (α + β)² = R with R > 0, and αβ = Q (with α ≠ β).
The R > 0 hypothesis ensures α + β ≠ 0, which is needed for the even-indexed
terms (which divide by α² - β² = (α-β)(α+β)).
-/
theorem LehmerSeq_eq_lehmerTermComplex (R Q : ℤ) (α β : ℂ)
    (hsum : (α + β) ^ 2 = ↑R) (hprod : α * β = ↑Q) (hne : α ≠ β)
    (hR : (0 : ℤ) < R) (n : ℕ) :
    (LehmerSeq R Q n : ℂ) = lehmerTermComplex α β n := by
  have hsum_ne : α + β ≠ 0 := by
    exact sum_ne_zero_of_sq_pos α β R hsum hR
  have hsq_sub_sq_ne_zero : α ^ 2 - β ^ 2 ≠ 0 := by
    grind;
  induction' n using Nat.strongRecOn with n ih;
  rcases n with ( _ | _ | n ) <;> simp_all +decide [ LehmerSeq ];
  · rfl;
  · unfold lehmerTermComplex; norm_num [ sub_ne_zero_of_ne hne ] ;
  · split_ifs;
    · by_cases hn : n = 0;
      · simp_all +decide [ lehmerTermComplex ];
        exact sub_ne_zero_of_ne hne;
      · exact Eq.symm ( lehmerTermComplex_even_recurrence α β R Q n hsum hprod hne hsum_ne ‹_› hn );
    · rw [ ← hsum, ← hprod, lehmerTermComplex_odd_recurrence ] <;> aesop

/-! ## Main Theorem -/

/-- **Erdős Problem 1052 / Wall k=3 — Primitive Divisor Theorem for Lehmer Sequences**

For every Lehmer pair (R, Q) and every n > 30 with 3 ∣ n, the n-th Lehmer
term U_n has a primitive prime divisor.

This is a special case of the Bilu-Hanrot-Voutier theorem (2001), which
establishes the result for ALL n > 30 (not just multiples of 3).

Reference: Y. Bilu, G. Hanrot, P.M. Voutier, "Existence of primitive
divisors of Lucas and Lehmer numbers", J. reine angew. Math. 539 (2001), 75-122.
-/
theorem erdos_1052_wall_k3_int (R Q : ℤ) (h : IsLehmerPair R Q)
    (n : ℕ) (hn : 30 < n) (h3 : 3 ∣ n) :
    ∃ q : ℕ, IsPrimitiveDivisor R Q n q := by
  sorry

/-! ## Alternative statement matching the complex formulation

The following reformulates the theorem using the complex Lehmer term
and complex parameters α, β, closer to the user's requested signature.
-/

/-- Helper: extract an integer from a complex number known to be integral. -/
noncomputable def intOfComplex (z : ℂ) (hz : z ∈ Set.range (Int.cast : ℤ → ℂ)) : ℤ :=
  Classical.choose hz

lemma intOfComplex_spec (z : ℂ) (hz : z ∈ Set.range (Int.cast : ℤ → ℂ)) :
    (↑(intOfComplex z hz) : ℂ) = z :=
  Classical.choose_spec hz

/-- The Lehmer term as an integer, defined for complex α, β with (α+β)² ∈ ℤ and αβ ∈ ℤ.
Uses the integer recurrence via LehmerSeq with R = (α+β)² and Q = αβ. -/
noncomputable def lehmer_term (α β : ℂ)
    (hR : (α + β) ^ 2 ∈ Set.range (Int.cast : ℤ → ℂ))
    (hQ : α * β ∈ Set.range (Int.cast : ℤ → ℂ))
    (n : ℕ) : ℤ :=
  LehmerSeq (intOfComplex _ hR) (intOfComplex _ hQ) n

/-- **Erdős 1052 / Wall k=3** — Complex formulation.

For algebraic integers α, β with (α+β)² = R ∈ ℤ, αβ = Q ∈ ℤ,
gcd(R,Q) = 1, α/β not a root of unity, and n > 30 with 3 ∣ n,
the n-th Lehmer term has a primitive prime divisor.

Note: The original problem statement uses α + β = √R (so (α+β)² = R ∈ ℤ),
not α + β ∈ ℤ. The latter would give a Lucas pair, not a Lehmer pair.
-/
theorem erdos_1052_wall_k3
    (α β : ℂ)
    (hR : (α + β) ^ 2 ∈ Set.range (Int.cast : ℤ → ℂ))
    (hQ : α * β ∈ Set.range (Int.cast : ℤ → ℂ))
    (hcoprime : Int.gcd (intOfComplex _ hR) (intOfComplex _ hQ) = 1)
    (hRpos : 0 < intOfComplex _ hR)
    (hQne : intOfComplex _ hQ ≠ 0)
    (hdisc : 4 * intOfComplex _ hQ < intOfComplex _ hR)
    (hrat : ¬ IsRootOfUnity (α / β))
    (n : ℕ) (hn : 30 < n) (h3 : 3 ∣ n) :
    ∃ q : ℕ, q.Prime ∧ (↑q : ℤ) ∣ lehmer_term α β hR hQ n ∧
      ∀ m, 0 < m → m < n → ¬ ((↑q : ℤ) ∣ lehmer_term α β hR hQ m) := by
  sorry

/-! ## The full Bilu-Hanrot-Voutier theorem (without the 3 ∣ n restriction)

For completeness, we also state the full BHV result. The Wall k=3 case
(erdos_1052_wall_k3) follows as a corollary.
-/

/-- **Bilu-Hanrot-Voutier Theorem (2001):** For every Lehmer pair and every n > 30,
U_n has a primitive prime divisor. -/
theorem bilu_hanrot_voutier (R Q : ℤ) (h : IsLehmerPair R Q)
    (n : ℕ) (hn : 30 < n) :
    ∃ q : ℕ, IsPrimitiveDivisor R Q n q := by
  sorry

/-- The Wall k=3 case follows immediately from BHV. -/
theorem erdos_1052_wall_k3_of_bhv (R Q : ℤ) (h : IsLehmerPair R Q)
    (n : ℕ) (hn : 30 < n) (_h3 : 3 ∣ n) :
    ∃ q : ℕ, IsPrimitiveDivisor R Q n q :=
  bilu_hanrot_voutier R Q h n hn