/-
Erdős Problem #370: erdos_370
Tier: 4 - Already Proved/Disproved (Formalization)
Status: proved (Lean) | Prize: no | Tractability: 95
Generated: 2026-01-04T16:20:16.803261
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
# Erdős Problem 370

*Reference:* [erdosproblems.com/370](https://www.erdosproblems.com/370)
-/

namespace Erdos370

/--
Are there infinitely many $n$ such that the largest prime factor of $n$ is $< n^{\frac{1}{2}}$ and
the largest prime factor of $n + 1$ is $< (n + 1)^{\frac{1}{2}}$.

Steinerberger has pointed out this problem has a trivial solution.
-/
@[category research solved, AMS 11]
/-
FORMALIZATION SKETCH for erdos_370:
Status: proved (Lean) - Proof exists, needs Lean formalization

1. [Reference the known proof]
2. [Key lemmas needed]
3. [Main proof technique]
-/

theorem erdos_370 :
    { n | Nat.maxPrimeFac n < √n ∧ Nat.maxPrimeFac (n + 1) < √(n + 1) }.Infinite ↔ answer(True) := by
  sorry

end Erdos370
