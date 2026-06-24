import Mathlib

/-!
# Singmaster's Conjecture

## Statement
There is an absolute constant `N` such that no integer greater than 1
appears more than `N` times in Pascal's triangle.

## Status: OPEN

This is a well-known open problem in combinatorics, first posed by
David Singmaster in 1971.

## Known results

- **Trivial symmetry:** `C(n,k) = C(n,n-k)`, so every binomial coefficient
  appears at least twice (except those in the middle of even rows).

- **The number 3003** = C(14,5) = C(14,9) = C(15,5) = C(15,10)
  = C(3003,1) = C(3003,3002) = C(78,2) = C(78,76) appears **8 times**.
  It is conjectured that N = 8.

- **Infinitely many numbers appear 6 times:**
  Using Fibonacci numbers, `C(F_{2k}, F_{2k}-2)` for even-indexed
  Fibonacci numbers gives such examples.

- **Best known upper bound:** The number of representations of `t` as a
  binomial coefficient is `O(log t / (log log t)²)` (improvements due to
  Kane, 2007, building on work of Erdős). This is **not** a constant bound.

## Why this cannot currently be formalized

The core difficulty is bounding the number of distinct `k` values for which
the equation `C(n,k) = t` has a solution:

1. For each fixed `k ≥ 1`, `n ↦ C(n,k)` is strictly increasing for `n ≥ k`,
   so there is **at most one** `n` per `k`.

2. If `C(n,k) = t` with `k ≤ n/2`, then `n ≥ 2k` and
   `C(n,k) ≥ C(2k,k) ≥ 2^k`, so `k ≤ log₂(t)`.

3. This gives at most `2 · log₂(t) + 2` representations — an `O(log t)`
   bound, which grows with `t` and is **not** a constant.

4. Proving that the number of valid `k` values is bounded by a universal
   constant requires ruling out the possibility that for large `t`, many
   of the `O(log t)` candidate `k` values simultaneously yield solutions.
   This is precisely what remains unproven.

No proof of a constant bound is known in the mathematical literature.
-/

/-- **Singmaster's Conjecture (OPEN):** There exists an absolute constant `N`
such that every integer `t > 1` appears at most `N` times as a binomial
coefficient `C(n,k)` with `0 ≤ k ≤ n ≤ t`. -/
theorem singmaster :
    ∃ N : ℕ, ∀ t : ℕ, t > 1 →
    (Finset.filter (fun p : ℕ × ℕ => Nat.choose p.1 p.2 = t)
      (Finset.range (t+1) ×ˢ Finset.range (t+1))).card ≤ N := by
  sorry

/-!
## Provable partial results

Below we state and prove some related results that ARE provable:
the `O(log t)` bound, monotonicity of binomial coefficients, etc.
-/

/-
PROBLEM
For fixed `k ≥ 1`, `Nat.choose · k` is strictly increasing on `[k, ∞)`.

PROVIDED SOLUTION
Use Nat.choose_succ_right_eq or the fact that C(n+1,k) = C(n,k) + C(n,k-1) > C(n,k) for k ≥ 1. Alternatively, use Nat.choose_lt_choose or similar Mathlib lemmas about monotonicity of binomial coefficients.
-/
theorem choose_strictMono_left (k : ℕ) (hk : k ≥ 1) :
    StrictMono fun n => Nat.choose (n + k) k := by
  refine' strictMono_nat_of_lt_succ fun n => _;
  induction' n with n ih <;> simp_all +arith +decide [ Nat.choose ];
  · linarith;
  · rcases k with ( _ | _ | k ) <;> simp_all +arith +decide [ Nat.choose ]

/-
PROBLEM
Every entry `C(n,k)` with `1 ≤ k ≤ n-1` satisfies `C(n,k) ≥ n`.

PROVIDED SOLUTION
Induction on n. Base case n=2: k=1, C(2,1)=2=n. Inductive step: C(n+1,k) = C(n,k) + C(n,k-1) ≥ n + 0 = n, or use that C(n,k) ≥ n when 1 ≤ k ≤ n-1 because C(n,1)=n is the minimum among all C(n,k) for 1 ≤ k ≤ n-1 (by unimodality of binomial coefficients).
-/
theorem choose_ge_of_interior (n k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1) (hn : n ≥ 2) :
    Nat.choose n k ≥ n := by
  induction hn <;> rcases k with ( _ | _ | k ) <;> simp_all +arith +decide [ Nat.choose_succ_succ, add_comm ];
  rcases hk2 <;> simp_all +arith +decide [ Nat.choose ];
  · grind;
  · linarith [ Nat.choose_pos ( by linarith : k ≤ ‹_› ) ]

/-
PROBLEM
All solutions to `C(n,k) = t > 1` satisfy `n ≤ t` and `k ≤ t`.

PROVIDED SOLUTION
Use choose_ge_of_interior: if C(n,k) = t > 1, then k ≥ 1 and k ≤ n-1 (since C(n,0)=1 and C(n,k)=0 for k>n). Then C(n,k) ≥ n by choose_ge_of_interior (for n ≥ 2; if n ≤ 1 then C(n,k) ≤ 1 < t), so n ≤ t. Also k ≤ n-1 ≤ t-1 ≤ t.
-/
theorem choose_eq_bound {n k t : ℕ} (ht : t > 1) (h : Nat.choose n k = t) :
    n ≤ t ∧ k ≤ t := by
  -- Since $t$ is positive, $k$ cannot be $0$.
  have hk_pos : 1 ≤ k := by
    contrapose! ht; aesop;
  -- Since $t$ is positive, $k$ cannot be $n$.
  have hk_lt_n : k < n := by
    exact lt_of_le_of_ne ( Nat.le_of_not_lt fun h => by linarith [ Nat.choose_eq_zero_of_lt h ] ) ( by aesop_cat );
  -- By choose_ge_of_interior, since $1 \le k \le n - 1$, we have $n \le t$.
  have hn_le_t : n ≤ t := by
    have := choose_ge_of_interior n k hk_pos ( Nat.le_sub_one_of_lt hk_lt_n ) ( by linarith ) ; aesop;
  exact ⟨ hn_le_t, le_trans hk_lt_n.le hn_le_t ⟩