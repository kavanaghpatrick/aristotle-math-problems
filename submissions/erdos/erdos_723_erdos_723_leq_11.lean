/-
Erdős Problem #723: erdos_723.leq_11
Source: Google DeepMind Formal Conjectures
Generated: 2026-01-04T16:15:34.654492

Submit via: aristotle --file /Users/patrickkavanagh/math/submissions/erdos/erdos_723_erdos_723_leq_11.lean
-/

/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-!
# Erdős Problem 723

Also known as the prime power conjecture.

*Reference:* [erdosproblems.com/723](https://www.erdosproblems.com/723)
-/

open Configuration

namespace Erdos723

/--
If there is a finite projective plane of order $n$ then must $n$ be a prime power?
-/
@[category research open, AMS 5]
theorem erdos_723 :
    (∀ {P L : Type} (_: Membership P L) (_ : Fintype P) (_ : Fintype L),
      ∀ pp : ProjectivePlane P L, IsPrimePow pp.order) ↔ answer(sorry) := by
  sorry

/--
These always exist if $n$ is a prime power.
-/
@[category research solved, AMS 5]
theorem erdos_723.prime_pow_is_projplane_order :
    ∀ n, IsPrimePow n → ∃ (P L : Type) (_ : Membership P L) (_ : Fintype P) (_ : Fintype L)
      (pp : ProjectivePlane P L), pp.order = n := by
  sorry

/--
This conjecture has been proved for $n \leq 11$.
-/
@[category research solved, AMS 5]
/-
PROOF SKETCH for erdos_723.leq_11:
1. [TODO: Describe the mathematical approach]
2. [TODO: Key lemmas or techniques needed]
3. [TODO: Why this leads to the result]
-/

theorem erdos_723.leq_11 {P L : Type} [Membership P L] [Fintype P] [Fintype L] :
    ∀ pp : ProjectivePlane P L, pp.order ≤ 11 → IsPrimePow pp.order := by
  sorry

/--
It is open whether there exists a projective plane of order 12.
-/
@[category research open, AMS 5]
theorem erdos_723.eq_12 :
    (∃ (P L : Type) (_ : Membership P L) (_ : Fintype P) (_ : Fintype L) (pp : ProjectivePlane P L),
      pp.order = 12) ↔ answer(sorry) := by
  sorry

/--
Bruck and Ryser have proved that if $n \equiv 1 (\mod 4)$ or $n \equiv 2 (\mod 4)$ then $n$ must be
the sum of two squares.
-/
@[category research solved, AMS 5]
theorem bruck_ryser {P L : Type} [Membership P L] [Fintype P] [Fintype L]
    (n : ℕ) (pp : ProjectivePlane P L) (hpp : pp.order = n) :
    (n ≡ 1 [MOD 4] ∨ n ≡ 2 [MOD 4]) → ∃ a b, n = a ^ 2 + b ^ 2 := by
  sorry

end Erdos723
