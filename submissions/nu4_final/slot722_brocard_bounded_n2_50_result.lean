import Mathlib

set_option maxHeartbeats 8000000

private lemma nth_prime_val {m n : ℕ} (hp : Nat.Prime m) (hc : Nat.count Nat.Prime m = n) :
    Nat.nth Nat.Prime n = m := by
  rw [← hc, Nat.nth_count hp]

theorem brocard_conjecture_bounded :
    ∀ n : ℕ, 2 ≤ n → n ≤ 50 →
      4 ≤ ((Finset.Ioo (n.nth Nat.Prime ^ 2) ((n+1).nth Nat.Prime ^ 2)).filter Nat.Prime).card := by
  intro n hn1 hn2
  have h2  : Nat.nth Nat.Prime 2  = 5   := nth_prime_val (by norm_num) (by native_decide)
  have h3  : Nat.nth Nat.Prime 3  = 7   := nth_prime_val (by norm_num) (by native_decide)
  have h4  : Nat.nth Nat.Prime 4  = 11  := nth_prime_val (by norm_num) (by native_decide)
  have h5  : Nat.nth Nat.Prime 5  = 13  := nth_prime_val (by norm_num) (by native_decide)
  have h6  : Nat.nth Nat.Prime 6  = 17  := nth_prime_val (by norm_num) (by native_decide)
  have h7  : Nat.nth Nat.Prime 7  = 19  := nth_prime_val (by norm_num) (by native_decide)
  have h8  : Nat.nth Nat.Prime 8  = 23  := nth_prime_val (by norm_num) (by native_decide)
  have h9  : Nat.nth Nat.Prime 9  = 29  := nth_prime_val (by norm_num) (by native_decide)
  have h10 : Nat.nth Nat.Prime 10 = 31  := nth_prime_val (by norm_num) (by native_decide)
  have h11 : Nat.nth Nat.Prime 11 = 37  := nth_prime_val (by norm_num) (by native_decide)
  have h12 : Nat.nth Nat.Prime 12 = 41  := nth_prime_val (by norm_num) (by native_decide)
  have h13 : Nat.nth Nat.Prime 13 = 43  := nth_prime_val (by norm_num) (by native_decide)
  have h14 : Nat.nth Nat.Prime 14 = 47  := nth_prime_val (by norm_num) (by native_decide)
  have h15 : Nat.nth Nat.Prime 15 = 53  := nth_prime_val (by norm_num) (by native_decide)
  have h16 : Nat.nth Nat.Prime 16 = 59  := nth_prime_val (by norm_num) (by native_decide)
  have h17 : Nat.nth Nat.Prime 17 = 61  := nth_prime_val (by norm_num) (by native_decide)
  have h18 : Nat.nth Nat.Prime 18 = 67  := nth_prime_val (by norm_num) (by native_decide)
  have h19 : Nat.nth Nat.Prime 19 = 71  := nth_prime_val (by norm_num) (by native_decide)
  have h20 : Nat.nth Nat.Prime 20 = 73  := nth_prime_val (by norm_num) (by native_decide)
  have h21 : Nat.nth Nat.Prime 21 = 79  := nth_prime_val (by norm_num) (by native_decide)
  have h22 : Nat.nth Nat.Prime 22 = 83  := nth_prime_val (by norm_num) (by native_decide)
  have h23 : Nat.nth Nat.Prime 23 = 89  := nth_prime_val (by norm_num) (by native_decide)
  have h24 : Nat.nth Nat.Prime 24 = 97  := nth_prime_val (by norm_num) (by native_decide)
  have h25 : Nat.nth Nat.Prime 25 = 101 := nth_prime_val (by norm_num) (by native_decide)
  have h26 : Nat.nth Nat.Prime 26 = 103 := nth_prime_val (by norm_num) (by native_decide)
  have h27 : Nat.nth Nat.Prime 27 = 107 := nth_prime_val (by norm_num) (by native_decide)
  have h28 : Nat.nth Nat.Prime 28 = 109 := nth_prime_val (by norm_num) (by native_decide)
  have h29 : Nat.nth Nat.Prime 29 = 113 := nth_prime_val (by norm_num) (by native_decide)
  have h30 : Nat.nth Nat.Prime 30 = 127 := nth_prime_val (by norm_num) (by native_decide)
  have h31 : Nat.nth Nat.Prime 31 = 131 := nth_prime_val (by norm_num) (by native_decide)
  have h32 : Nat.nth Nat.Prime 32 = 137 := nth_prime_val (by norm_num) (by native_decide)
  have h33 : Nat.nth Nat.Prime 33 = 139 := nth_prime_val (by norm_num) (by native_decide)
  have h34 : Nat.nth Nat.Prime 34 = 149 := nth_prime_val (by norm_num) (by native_decide)
  have h35 : Nat.nth Nat.Prime 35 = 151 := nth_prime_val (by norm_num) (by native_decide)
  have h36 : Nat.nth Nat.Prime 36 = 157 := nth_prime_val (by norm_num) (by native_decide)
  have h37 : Nat.nth Nat.Prime 37 = 163 := nth_prime_val (by norm_num) (by native_decide)
  have h38 : Nat.nth Nat.Prime 38 = 167 := nth_prime_val (by norm_num) (by native_decide)
  have h39 : Nat.nth Nat.Prime 39 = 173 := nth_prime_val (by norm_num) (by native_decide)
  have h40 : Nat.nth Nat.Prime 40 = 179 := nth_prime_val (by norm_num) (by native_decide)
  have h41 : Nat.nth Nat.Prime 41 = 181 := nth_prime_val (by norm_num) (by native_decide)
  have h42 : Nat.nth Nat.Prime 42 = 191 := nth_prime_val (by norm_num) (by native_decide)
  have h43 : Nat.nth Nat.Prime 43 = 193 := nth_prime_val (by norm_num) (by native_decide)
  have h44 : Nat.nth Nat.Prime 44 = 197 := nth_prime_val (by norm_num) (by native_decide)
  have h45 : Nat.nth Nat.Prime 45 = 199 := nth_prime_val (by norm_num) (by native_decide)
  have h46 : Nat.nth Nat.Prime 46 = 211 := nth_prime_val (by norm_num) (by native_decide)
  have h47 : Nat.nth Nat.Prime 47 = 223 := nth_prime_val (by norm_num) (by native_decide)
  have h48 : Nat.nth Nat.Prime 48 = 227 := nth_prime_val (by norm_num) (by native_decide)
  have h49 : Nat.nth Nat.Prime 49 = 229 := nth_prime_val (by norm_num) (by native_decide)
  have h50 : Nat.nth Nat.Prime 50 = 233 := nth_prime_val (by norm_num) (by native_decide)
  have h51 : Nat.nth Nat.Prime 51 = 239 := nth_prime_val (by norm_num) (by native_decide)
  interval_cases n <;> simp only [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33,
    h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51] <;>
    native_decide
