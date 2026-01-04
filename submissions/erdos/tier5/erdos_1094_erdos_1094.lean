/-
Erdős Problem #1094: erdos_1094
Tier: 5 - Research Open + High Tractability
Status: open | Prize: no | Tractability: 95
Generated: 2026-01-04T16:20:16.814847
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

import FormalConjectures.Util.ProblemImports


/-!
# Erdős Problem 1094

For all $n\ge 2k$ the least prime factor of $\binom{n}{k}$ is $\le\max(n/k,k)$, with only
finitely many exceptions.

*Reference:* [erdosproblems.com/1094](https://www.erdosproblems.com/1094)
-/

namespace Erdos1094

open scoped Nat

/--
**Erdős problem 1094**

There are only finitely many pairs `(n,k)` with `n ≥ 2*k` for which the
least prime factor of the binomial coefficient `Nat.choose n k` exceeds `max (n / k) k`.
-/
@[category research open, AMS 11]
/-
PROOF SKETCH for erdos_1094:
Status: open

1. [Mathematical approach]
2. [Key lemmas or techniques]
3. [Why this leads to the result]
-/

theorem erdos_1094 :
    {(n, k) : ℕ × ℕ | 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}.Finite := by
  sorry

end Erdos1094
