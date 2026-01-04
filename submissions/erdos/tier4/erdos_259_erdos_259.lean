/-
Erdős Problem #259: erdos_259
Tier: 4 - Already Proved/Disproved (Formalization)
Status: proved | Prize: no | Tractability: 100
Generated: 2026-01-04T16:20:16.801340
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
# Erdős Problem 259

*Reference:* [erdosproblems.com/259](https://www.erdosproblems.com/259)
-/

open scoped ArithmeticFunction

namespace Erdos259

/--
Is $\sum_{n} \mu(n)^2\frac{n}{2^n}$ irrational?

This is true, and was proved by Chen and Ruzsa.

[ChRu99] Chen, Yong-Gao and Ruzsa, Imre Z., On the irrationality of certain series. Period. Math. Hungar. (1999), 31--37.
-/
@[category research solved, AMS 11]
/-
FORMALIZATION SKETCH for erdos_259:
Status: proved - Proof exists, needs Lean formalization

1. [Reference the known proof]
2. [Key lemmas needed]
3. [Main proof technique]
-/

theorem erdos_259 : Irrational (∑' n : ℕ, (μ n) ^ 2 * n / (2 ^ n)) := by
  sorry

end Erdos259
