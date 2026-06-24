#!/usr/bin/env python3
"""Generate Lean proof for the 12x12 covering - v3."""

m = 625942982474437835576448580641867239959237377760067219877585649

selected = [
    (5, 1), (7, 1), (11, 1), (17, 10), (13, 3), (19, 18), (29, 14),
    (37, 2), (31, 27), (41, 38), (43, 9), (61, 35), (59, 58), (79, 29),
    (971, 32), (53, 18), (107, 2), (67, 4), (83, 48), (89, 54),
    (103, 34), (127, 61), (157, 24), (691, 324), (211, 149), (227, 29),
    (101, 27), (109, 8), (113, 49), (131, 61), (163, 32), (179, 78),
    (229, 28), (269, 105)
]

GRID = 12

cell_prime = {}
for k in range(GRID):
    for l in range(GRID):
        val = pow(2, k) * pow(3, l) * m + 1
        for p, vm in selected:
            if val % p == 0:
                cell_prime[(k,l)] = p
                break

primes_used = sorted(set(cell_prime.values()))

lines = []
lines.append("import Mathlib")
lines.append("")
lines.append("set_option maxHeartbeats 8000000")
lines.append("set_option maxRecDepth 4000")
lines.append("")

lines.append(f"private def M : ℕ := {m}")
lines.append("")

# Index-1 lemmas
for p in primes_used:
    lines.append(f"private lemma index1_{p} :")
    lines.append(f"    (((Finset.univ : Finset (Fin ({p} - 1) × Fin ({p} - 1))).image")
    lines.append(f"      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % {p})).card = {p} - 1) := by native_decide")
    lines.append("")

# Primality lemmas
for p in primes_used:
    lines.append(f"private lemma prime_{p} : Nat.Prime {p} := by decide")
lines.append("")

# Divisibility lemmas for each cell
for k in range(GRID):
    for l in range(GRID):
        p = cell_prime[(k,l)]
        lines.append(f"private lemma dvd_{k}_{l} : {p} ∣ 2 ^ {k} * 3 ^ {l} * M + 1 := by native_decide")

lines.append("")

# Main theorem
lines.append("theorem erdos203_grid_12x12_B1000_exists :")
lines.append("    ∃ m : ℕ, ∀ k l : ℕ, k < 12 → l < 12 →")
lines.append("      ∃ p ∈ Finset.range 1001, p.Prime ∧ 3 < p ∧")
lines.append("        (((Finset.univ : Finset (Fin (p-1) × Fin (p-1))).image")
lines.append("          (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % p)).card = p - 1) ∧")
lines.append("        p ∣ 2 ^ k * 3 ^ l * m + 1 := by")
lines.append("  refine ⟨M, fun k l hk hl => ?_⟩")
lines.append("  interval_cases k <;> interval_cases l")

for k in range(GRID):
    for l in range(GRID):
        p = cell_prime[(k,l)]
        lines.append(f"  · exact ⟨{p}, Finset.mem_range.mpr (by omega), prime_{p}, by omega, index1_{p}, dvd_{k}_{l}⟩")

with open("/workspace/request-project/RequestProject/Main.lean", "w") as f:
    f.write("\n".join(lines) + "\n")

print(f"Generated {len(lines)} lines")
