/-
Erdős Problem #826: erdos_826
Tier: 5 - Research Open + High Tractability
Status: open | Prize: no | Tractability: 95
Generated: 2026-01-04T16:20:16.818076
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
# Erdős Problem 826

*Reference:* [erdosproblems.com/826](https://www.erdosproblems.com/826)
-/

open scoped ArithmeticFunction

namespace Erdos826

/--
Are there infinitely many $n$ such that, for all $k\geq 1$
$$
  \tau(n + k) \ll k?
$$
-/
@[category research open, AMS 11]
/-
PROOF SKETCH for erdos_826:
Status: open

1. [Mathematical approach]
2. [Key lemmas or techniques]
3. [Why this leads to the result]
-/

theorem erdos_826 : (∃ C > (0 : ℝ), { n | ∀ k ≥ 1, σ 0 (n + k) ≤ C * k }.Infinite) ↔
    answer(sorry) := by
  sorry

end Erdos826
