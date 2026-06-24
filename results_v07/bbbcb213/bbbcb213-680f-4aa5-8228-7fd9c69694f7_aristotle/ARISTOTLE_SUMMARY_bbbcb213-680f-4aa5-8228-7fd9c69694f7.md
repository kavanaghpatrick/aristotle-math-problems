# Summary of changes
## Erdős Problem 398 — Brocard's Problem

**File:** `RequestProject/Erdos398.lean`

**Status:** This is a famous **open problem** in number theory (Brocard's conjecture, 1876). No proof is known, despite computational verification up to n = 10⁹.

### What was accomplished:

1. **`erdos_398_easy` (PROVED):** The easy direction — {4, 5, 7} are all Brocard numbers:
   - 4! + 1 = 25 = 5²
   - 5! + 1 = 121 = 11²  
   - 7! + 1 = 5041 = 71²

2. **`erdos_398_hard` (SORRY — open conjecture):** The hard direction — no other natural numbers n satisfy n! + 1 = m². This remains `sorry` as it is an unsolved problem in mathematics.

3. **`erdos_398` (structured proof):** The main theorem follows from the two directions via `Set.eq_of_subset_of_subset`. It inherits the `sorry` from `erdos_398_hard`.

The theorem proving subagent attempted the open conjecture using modular arithmetic approaches but, as expected for a problem that has resisted proof for nearly 150 years, could not close it.