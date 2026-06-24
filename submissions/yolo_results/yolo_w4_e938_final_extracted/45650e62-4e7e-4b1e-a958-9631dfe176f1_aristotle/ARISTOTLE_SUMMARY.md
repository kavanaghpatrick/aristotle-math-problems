# Summary of changes for run 45650e62-4e7e-4b1e-a958-9631dfe176f1
## Erdős Problem 938 — Formalization

**Status**: This is an **open problem** (as of 2026). The single remaining `sorry` in the file reflects genuinely unknown mathematics, not a gap in formalization effort.

### What was delivered (`RequestProject/Erdos938.lean`):

1. **Definition of powerful numbers** (`Nat.IsPowerful`): A natural number n ≥ 1 where every prime factor appears with multiplicity ≥ 2.

2. **Proven lemmas** (all sorry-free, verified with `#print axioms`):
   - `Nat.IsPowerful.one` — 1 is powerful
   - `Nat.IsPowerful.sq` — every perfect square ≥ 1 is powerful
   - `Nat.IsPowerful_infinite` — the set of powerful numbers is infinite
   - `powerfulNth_isPowerful` — the k-th powerful number is powerful
   - `powerfulNth_strictMono` — the enumeration is strictly monotone
   - **`erdos_938_conditional`** — the key conditional theorem: if *kernel-uniformity* and *bounded-kernel finiteness* both hold, then Erdős 938 follows. This captures the logical structure of the most promising conditional approach.

3. **Conditional framework**: Two hypotheses are cleanly defined:
   - `BoundedKernelFiniteness`: For any fixed kernel bound B, only finitely many consecutive powerful 3-APs have all squarefree kernels ≤ B. (Unconditionally true via Mordell–Siegel, but the proof requires number theory beyond current Mathlib.)
   - `KernelUniformity`: An absolute bound on squarefree kernels exists for all sufficiently large consecutive powerful 3-APs. (This is the *open core* — and may even be false.)

4. **Main theorem** (`erdos_938`): Stated with `sorry` — the open problem.

5. **Falsification note**: The file documents that van Doorn (2026) conjectures infinitely many consecutive powerful 3-APs via the Pell family x² − 343y² = 2, which would make the conjecture FALSE and the kernel-uniformity hypothesis false.

### Mathematical analysis

The conditional proof (`erdos_938_conditional`) works by a clean union argument: the set of AP-witnessing indices splits into those below a threshold K₀ (finite by strict monotonicity of `powerfulNth`) and those above (finite by combining kernel-uniformity with bounded-kernel finiteness). This structural decomposition is fully machine-verified.

The irreducible open content is concentrated in `KernelUniformity` — whether squarefree kernels in the Golomb decomposition n = a²b³ stay bounded for consecutive powerful 3-APs. No known technique resolves this, and computational evidence is ambiguous.