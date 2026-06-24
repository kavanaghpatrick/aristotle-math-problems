#!/usr/bin/env python3
"""
Compute the cell-to-prime mapping for the Lean proof.
"""

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

# Build mapping: (k,l) -> prime that covers it
cell_prime = {}
for k in range(GRID):
    for l in range(GRID):
        val = pow(2, k) * pow(3, l) * m + 1
        for p, vm in selected:
            if val % p == 0:
                cell_prime[(k,l)] = p
                break

# Print as a grid
print("Cell-to-prime mapping:")
for k in range(GRID):
    row = []
    for l in range(GRID):
        row.append(str(cell_prime.get((k,l), "?")))
    print(f"  k={k}: {', '.join(row)}")

# Verify all cells are covered
assert len(cell_prime) == 144, f"Only {len(cell_prime)} cells covered!"

# Print unique primes used
primes_used = sorted(set(cell_prime.values()))
print(f"\nPrimes actually used in mapping: {primes_used}")
print(f"Count: {len(primes_used)}")

# For Lean, we need to verify divisibility: p | 2^k * 3^l * m + 1
# Let's also compute the quotients to help verification
print("\nVerification data:")
for k in range(GRID):
    for l in range(GRID):
        p = cell_prime[(k,l)]
        val = pow(2, k) * pow(3, l) * m + 1
        q = val // p
        assert val == p * q
        # print(f"  ({k},{l}): p={p}, 2^{k}*3^{l}*m+1 = {p} * {q}")

print("All quotients verified!")

# Now verify the index-1 condition for each prime used
def subgroup_size_23(p):
    seen = set()
    seen.add(1)
    queue = [1]
    while queue:
        x = queue.pop()
        y = (x * 2) % p
        if y not in seen:
            seen.add(y)
            queue.append(y)
        y = (x * 3) % p
        if y not in seen:
            seen.add(y)
            queue.append(y)
    return len(seen)

print("\nIndex-1 verification:")
for p in primes_used:
    sz = subgroup_size_23(p)
    assert sz == p - 1, f"Prime {p} is NOT index-1! subgroup size = {sz}, p-1 = {p-1}"
    print(f"  p={p}: <2,3> has size {sz} = p-1 ✓")

print("\n=== Everything verified ===")
print(f"\nm = {m}")
