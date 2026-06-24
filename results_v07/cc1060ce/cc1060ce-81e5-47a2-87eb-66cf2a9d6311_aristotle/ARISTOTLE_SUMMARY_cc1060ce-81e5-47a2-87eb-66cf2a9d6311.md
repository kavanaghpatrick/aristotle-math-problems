# Summary of changes
## Erdős Problem 936 — Status: OPEN

The theorem is stated in `RequestProject/Erdos936.lean` with a `sorry`, which is the expected outcome for this problem.

**Why the `sorry` remains:** Erdős Problem 936 — that there are only finitely many n ≥ 1 with 2^n + 1 powerful — is a **genuinely open problem** in number theory. No unconditional proof is known as of 2024. The finiteness statement follows conditionally from the ABC conjecture, but ABC itself remains unproven (the claimed proof by Mochizuki is not widely accepted).

**What was verified:**
- The formal statement compiles correctly against Mathlib.
- Computational verification confirms that among n ∈ [1, 79], only n = 3 yields a powerful value (2³ + 1 = 9 = 3²), consistent with the conjecture.
- The theorem proving subagent was unable to find a proof, as expected for an open problem.

The file includes detailed documentation of the problem's status, the known solution (n = 3), and references to the relevant literature.