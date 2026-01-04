/-
Erdős Problem #972: erdos_972
Tier: 5 - Research Open + High Tractability
Status: open | Prize: no | Tractability: 95
Generated: 2026-01-04T16:20:16.819022
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
# Erdős Problem 972

*Reference:* [erdosproblems.com/972](https://www.erdosproblems.com/972)
-/

namespace Erdos972

/--
The set of primes `p` such that `Nat.floor (α * p)` is also prime.
-/
def primeSet (α : ℝ) : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ Nat.Prime ⌊ (α * p) ⌋₊}

/--
**Erdős problem 972.**
Let $\alpha > 1$ be irrational. Are there infinitely many primes $p$
such that $\lfloor p\alpha \rfloor$ is also prime?
-/
@[category research open, AMS 11]
/-
PROOF SKETCH for erdos_972:
Status: open

1. [Mathematical approach]
2. [Key lemmas or techniques]
3. [Why this leads to the result]
-/

theorem erdos_972 : (∀ α > 1, Irrational α → (primeSet α).Infinite) ↔ answer(sorry) := by
  sorry

end Erdos972
