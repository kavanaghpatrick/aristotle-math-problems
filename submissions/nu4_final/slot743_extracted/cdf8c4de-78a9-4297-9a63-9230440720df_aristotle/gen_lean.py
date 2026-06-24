#!/usr/bin/env python3
"""Generate Lean proof for the 12x12 covering."""

m = 625942982474437835576448580641867239959237377760067219877585649

# (prime, vm) pairs from the search
selected = [
    (5, 1), (7, 1), (11, 1), (17, 10), (13, 3), (19, 18), (29, 14),
    (37, 2), (31, 27), (41, 38), (43, 9), (61, 35), (59, 58), (79, 29),
    (971, 32), (53, 18), (107, 2), (67, 4), (83, 48), (89, 54),
    (103, 34), (127, 61), (157, 24), (691, 324), (211, 149), (227, 29),
    (101, 27), (109, 8), (113, 49), (131, 61), (163, 32), (179, 78),
    (229, 28), (269, 105)
]

GRID = 12

# Build cell -> prime mapping
cell_prime = {}
for k in range(GRID):
    for l in range(GRID):
        val = pow(2, k) * pow(3, l) * m + 1
        for p, vm in selected:
            if val % p == 0:
                cell_prime[(k,l)] = p
                break

primes_used = sorted(set(cell_prime.values()))

# For each cell, compute the divisibility witness
cell_quot = {}
for k in range(GRID):
    for l in range(GRID):
        p = cell_prime[(k,l)]
        val = pow(2, k) * pow(3, l) * m + 1
        cell_quot[(k,l)] = val // p

# Generate Lean code
lines = []
lines.append("import Mathlib")
lines.append("")
lines.append("set_option maxHeartbeats 800000")
lines.append("set_option maxRecDepth 4000")
lines.append("")
lines.append(f"private def M : ℕ := {m}")
lines.append("")

# For each prime, prove index-1 as a separate native_decide lemma
for p in primes_used:
    lines.append(f"private lemma index1_{p} :")
    lines.append(f"    (((Finset.univ : Finset (Fin ({p}-1) × Fin ({p}-1))).image")
    lines.append(f"      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % {p})).card = {p} - 1) := by native_decide")
    lines.append("")

# For each prime, prove primality
for p in primes_used:
    lines.append(f"private lemma prime_{p} : Nat.Prime {p} := by decide")

lines.append("")

# Main theorem
lines.append("theorem erdos203_grid_12x12_B1000_exists :")
lines.append("    ∃ m : ℕ, ∀ k l : ℕ, k < 12 → l < 12 →")
lines.append("      ∃ p ∈ Finset.range 1001, p.Prime ∧ 3 < p ∧")
lines.append("        (((Finset.univ : Finset (Fin (p-1) × Fin (p-1))).image")
lines.append("          (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % p)).card = p - 1) ∧")
lines.append("        p ∣ 2 ^ k * 3 ^ l * m + 1 := by")
lines.append("  refine ⟨M, fun k l hk hl => ?_⟩")
lines.append("  interval_cases k <;> interval_cases l <;> exact")

# Generate 144 cases
cases = []
for k in range(GRID):
    for l in range(GRID):
        p = cell_prime[(k,l)]
        q = cell_quot[(k,l)]
        # ⟨p, mem_range, prime, gt3, index1, dvd⟩
        case = f"    ⟨{p}, by omega, prime_{p}, by omega, index1_{p}, ⟨{q}, by ring⟩⟩"
        cases.append(case)

# Join with " <;>\n"
# Actually, after interval_cases, each case is a separate goal.
# "interval_cases k <;> interval_cases l" creates 144 goals.
# "<;> exact" tries the same tactic on all goals, but each goal has different k,l values.
# We need to handle each goal separately.

# Better approach: use a single tactic that handles all cases
# Use a lookup function

# Actually, let's use a different approach: provide the proof term directly
# as a match expression or use `fin_cases` or `omega`.

# Hmm, let me reconsider. With "interval_cases k <;> interval_cases l",
# we get 144 goals. Then we need separate proofs for each.
# We can use "all_goals first | exact ... | exact ... | ..."
# Or we can use a big <;> block.

# Actually, the simplest approach: use a single `decide` or `native_decide`
# after providing the witness m. But we already discussed that might be slow.

# Let me try yet another approach: define a function that maps (k,l) to the
# prime and quotient, and prove it's correct.

# Actually, let me just try the explicit approach with a list of 144 exacts
# separated by semicolons.

# After "interval_cases k <;> interval_cases l", each subgoal has specific
# values of k and l substituted. We need exactly 144 terms.
# Using "<;> exact" won't work because each case needs a different term.

# So we need:
# interval_cases k <;> interval_cases l
# -- 144 goals
# · exact ⟨...⟩
# · exact ⟨...⟩
# ...

# Or use: all_goals ...  but that only works if all goals have the same proof.

# Or use a big match. Let me use a proof term approach instead.

# Actually, the cleanest way is to use `Fin.cases` or just provide a proof term.

# Let me restructure: instead of interval_cases, use a proof term with a big match.

lines_new = []
lines_new.append("import Mathlib")
lines_new.append("")
lines_new.append("set_option maxHeartbeats 4000000")
lines_new.append("set_option maxRecDepth 4000")
lines_new.append("")
lines_new.append(f"private def M : ℕ := {m}")
lines_new.append("")

# For each prime, prove index-1 as a separate native_decide lemma
for p in primes_used:
    lines_new.append(f"private lemma index1_{p} :")
    lines_new.append(f"    (((Finset.univ : Finset (Fin ({p}-1) × Fin ({p}-1))).image")
    lines_new.append(f"      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % {p})).card = {p} - 1) := by native_decide")
    lines_new.append("")

# For each prime, prove primality  
for p in primes_used:
    lines_new.append(f"private lemma prime_{p} : Nat.Prime {p} := by decide")

lines_new.append("")

# Main theorem using omega for divisibility
lines_new.append("theorem erdos203_grid_12x12_B1000_exists :")
lines_new.append("    ∃ m : ℕ, ∀ k l : ℕ, k < 12 → l < 12 →")
lines_new.append("      ∃ p ∈ Finset.range 1001, p.Prime ∧ 3 < p ∧")
lines_new.append("        (((Finset.univ : Finset (Fin (p-1) × Fin (p-1))).image")
lines_new.append("          (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % p)).card = p - 1) ∧")
lines_new.append("        p ∣ 2 ^ k * 3 ^ l * m + 1 := by")
lines_new.append(f"  exact ⟨M, fun k l hk hl => by")
lines_new.append(f"    interval_cases k <;> interval_cases l")

# For each (k,l), add a focused goal proof
for i, (k, l) in enumerate([(k,l) for k in range(GRID) for l in range(GRID)]):
    p = cell_prime[(k,l)]
    q = cell_quot[(k,l)]
    # Each subgoal after interval_cases has the specific values substituted
    prefix = "    all_goals (" if i == 0 else ""
    suffix = ")" if i == 143 else ""
    lines_new.append(f"    <;> exact ⟨{p}, by omega, prime_{p}, by omega, index1_{p}, ⟨{q}, by ring⟩⟩")
    if i == 0:
        # Remove the per-goal and do them all at once with <;>
        break

# Actually, the <;> combinator after interval_cases applies to ALL subgoals.
# But each subgoal needs a DIFFERENT proof (different p, q).
# So <;> exact won't work.

# Let me use a different tactic. After interval_cases, we have 144 goals.
# We can use `next => exact ...` for each, or use focused proofs with ·.

# The cleanest approach: use a big tactic block with `next` for each case.
# Or better: use `first` with all possibilities.

# With `first`, for each goal, it tries each option until one works.
# Since the goals are different, each option will only work on specific goals.
# This is inefficient (O(144^2)) but might work.

# Actually, the most practical approach: use `<;> first` with all the exact terms.

lines_v2 = []
lines_v2.append("import Mathlib")
lines_v2.append("")
lines_v2.append("set_option maxHeartbeats 8000000")
lines_v2.append("set_option maxRecDepth 4000")
lines_v2.append("")
lines_v2.append(f"private def M : ℕ := {m}")
lines_v2.append("")

for p in primes_used:
    lines_v2.append(f"private lemma index1_{p} :")
    lines_v2.append(f"    (((Finset.univ : Finset (Fin ({p}-1) × Fin ({p}-1))).image")
    lines_v2.append(f"      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % {p})).card = {p} - 1) := by native_decide")
    lines_v2.append("")

for p in primes_used:
    lines_v2.append(f"private lemma prime_{p} : Nat.Prime {p} := by decide")

lines_v2.append("")

lines_v2.append("theorem erdos203_grid_12x12_B1000_exists :")
lines_v2.append("    ∃ m : ℕ, ∀ k l : ℕ, k < 12 → l < 12 →")
lines_v2.append("      ∃ p ∈ Finset.range 1001, p.Prime ∧ 3 < p ∧")
lines_v2.append("        (((Finset.univ : Finset (Fin (p-1) × Fin (p-1))).image")
lines_v2.append("          (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % p)).card = p - 1) ∧")
lines_v2.append("        p ∣ 2 ^ k * 3 ^ l * m + 1 := by")
lines_v2.append("  refine ⟨M, fun k l hk hl => ?_⟩")
lines_v2.append("  interval_cases k <;> interval_cases l")

# After interval_cases, we have 144 separate goals
# Use focused proofs
for k in range(GRID):
    for l in range(GRID):
        p = cell_prime[(k,l)]
        q = cell_quot[(k,l)]
        lines_v2.append(f"  · exact ⟨{p}, by omega, prime_{p}, by omega, index1_{p}, {q}, by ring⟩")

with open("/workspace/request-project/RequestProject/Main.lean", "w") as f:
    f.write("\n".join(lines_v2) + "\n")

print(f"Generated {len(lines_v2)} lines")
print(f"File written.")

# Also check: will `by ring` work for the divisibility?
# We need: 2^k * 3^l * M + 1 = p * q
# where q = (2^k * 3^l * M + 1) / p
# ring should handle this since all values are concrete naturals.
# Actually, ring works for equalities in commutative (semi)rings.
# With concrete numbers, norm_num might be better.

# Let's verify one case:
k, l = 0, 0
p = cell_prime[(0,0)]
q = cell_quot[(0,0)]
val = pow(2,0) * pow(3,0) * m + 1
print(f"\nExample: k=0, l=0, p={p}, q={q}")
print(f"  2^0 * 3^0 * M + 1 = {val}")
print(f"  p * q = {p * q}")
print(f"  Equal: {val == p * q}")
