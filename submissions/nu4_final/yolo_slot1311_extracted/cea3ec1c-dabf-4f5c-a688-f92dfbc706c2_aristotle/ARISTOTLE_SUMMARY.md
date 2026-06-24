# Summary of changes for run cea3ec1c-dabf-4f5c-a688-f92dfbc706c2
## Erdős Problem 938 — Formalization

**Status: OPEN PROBLEM — main theorem left as `sorry`**

### What was done

The file `RequestProject/Main.lean` contains a clean formalization of Erdős Problem 938:

1. **Definitions:**
   - `Nat.Powerful`: A natural number n ≥ 1 where every prime factor appears with exponent ≥ 2
   - `Set.IsAPOfLength`: A set forms an arithmetic progression of given length

2. **Proved lemmas (3/3):**
   - `Nat.Powerful.one`: 1 is powerful (vacuously)
   - `Nat.Powerful.sq`: Every perfect square n² (n ≥ 1) is powerful
   - `Nat.Powerful.setOf_infinite`: The set of powerful numbers is infinite

3. **Main theorem (`erdos_938`):** Stated with the exact target signature, left as `sorry`

### Why the main theorem remains `sorry`

Erdős Problem 938 is a **genuine open problem** in number theory. No proof of finiteness for 3-APs among consecutive powerful numbers is known in the literature. The informal proof outline provided relies on the **Bombieri–Lang conjecture** for surfaces of general type, which is itself an unproven conjecture in arithmetic geometry. The only partial results in the literature are:

- **Chan (2022, arXiv:2210.00281)**: Shows under the abc conjecture that the common difference d satisfies d ≫ N^{1/2−ε}
- **Chan (2025, arXiv:2503.21485)**: Rules out certain very special configurations unconditionally

Only three 3-AP triples of consecutive powerful numbers are known computationally: (1728, 1764, 1800), (6912, 7056, 7200), and (729000, 729316, 729632). The file builds cleanly with only the expected `sorry` warning on the open problem.