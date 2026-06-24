# Erdős 647 Sieve Campaign — PRE-REGISTRATION

**Author:** gelfond (Baker Assembly free hand) · **Date registered:** 2026-06-11 ·
**Status:** registered BEFORE any production run. Empty is a deliverable, not a disappointment.

This document fixes the outcome protocol before the sieve launches, so that neither outcome
(witness found / range exhausted empty) can be reinterpreted after the fact. Per the assembly-gap
screen (`analysis/assembly_gap_screen_jun10.md`, #1 erdos_647, feasibility 5.5/10), the honest prior
is **40–80% empty**. Both branches below are pre-committed.

---

## 1. The exact witness predicate (locked from 647.lean)

Source of truth: `formal-conjectures/FormalConjectures/ErdosProblems/647.lean`, theorem `erdos_647`:

```lean
∃ n > 24, ⨆ m : Fin n, m + σ 0 m ≤ n + 2
```

Decoded (`σ 0 m = τ(m)` = number of divisors; `⨆ m : Fin n` = sup over `m ∈ {0, 1, …, n−1}`):

> **n is a witness ⟺ n > 24 AND max_{0 ≤ m < n} ( m + τ(m) ) ≤ n + 2.**

Conventions, pinned and verified against OEIS A087280:
- The sup ranges over `m : Fin n`, i.e. **m ∈ [0, n)**, INCLUDING m = 0. In Mathlib `σ 0 0 = 0`,
  so `0 + τ(0) = 0` (never binding). `τ(1) = 1`.
- Boundary `≤ n + 2` is load-bearing (the m = n−2, n−4, n−6 candidates can hit it exactly).
- **Verified** (`verify_predicate.py`): brute force over n < 200 reproduces A087280's tail exactly
  — witnesses {5, 6, 8, 10, 12, 24} (the 1–4 are trivial small-n; 5,8,10,12,24 = McCranie's
  published exhaustive-to-10^10 sequence). The synthesized OEIS b-file confirms terms 5,8,10,12,24.

**The constellation / Sophie-Germain prime-form story is HEURISTIC PRIOR ONLY.** The seven forms
(n−1, (n−2)/2, …, (n−12)/12 prime) predict *where* witnesses are likely; they are NOT part of the
decision. The sieve decides the predicate above directly and unfiltered. Sieve soundness does not
depend on any constellation claim, on slot723/737, or on any HCN list (`hcn_tau_near_max` is a
**banned false lemma** — `false_lemmas` id 23 — and is used nowhere).

---

## 2. Exact search range

- **Discovery range: (10^10, 10^12].** The frontier is 10^10 (A087280, McCranie 2003, exhaustive);
  nothing new is learnable below it.
- **Validation range: [25, 10^10].** Re-run as FREE self-validation: the sieve must reproduce
  witnesses {5, 8, 10, 12, 24} and NO others in [25, 10^10]. **Any disagreement halts the campaign**
  (halt-and-audit tripwire) before the production range is trusted.
- **Re-registration note:** the screen's earlier pre-registered empty-stop was 10^11. This document
  RE-REGISTERS the stop at **10^12** (the screen explicitly flagged that the 10^12 extension needs
  re-registration; this is it).

---

## 3. The algorithm (reduction-free, self-checking)

Segmented τ-sieve over [25, 10^12], maintaining the running maximum of `m + τ(m)`:

```
running_max := 0
for m = 25 … 10^12 (in segments):
    compute τ(m)              # segmented divisor-count sieve, reduction-free
    if m + τ(m) > running_max: running_max := m + τ(m)
    # n = m+1 is a witness candidate; n is a witness iff running_max(over k<n) ≤ n+2:
    if running_max ≤ (m+1) + 2 and (m+1) > 24:  record candidate n = m+1
```

Because `running_max` is monotone nondecreasing and `n+2` grows by 1 per step, witnesses are exactly
the n where the running max has not yet overshot n+2. This is a single O(N log log N) pass; no
constellation filter, no reduction, trusts nothing but the divisor sieve.

**Check-window soundness (for the on-hit certificate only).** A violation `m+τ(m) > n+2` with `m<n`
needs `τ(m) > (n−m)+2`. Since `max τ(m)` for `m ≤ 10^12` is 6720 (HCN record, A066150 — used for
window SIZING only, re-verified live), only `m ∈ [n − 6718, n)` can violate. The campaign uses a
conservative window **W = 12000** (safe to ~1.5×10^13) with a **self-check tripwire**: if any segment
exhibits `τ(m) ≥ W−2`, the run HALTS (window too small) — so a too-short window can never manufacture
a false witness. (The running-max sieve itself needs no window; W is only the certificate's factor-
table width on a hit.)

---

## 4. OUTCOME PROTOCOL (pre-committed, both branches)

### Branch A — range exhausted EMPTY (the 40–80% expected outcome) — A DELIVERABLE

If the sieve completes (10^10, 10^12] with NO witness, the following are produced (no Aristotle spend):

1. **`failed_approaches` DB row**: problem_id `erdos_647`, approach `witness_sieve_to_1e12`,
   why-failed = "no witness n in (10^10, 10^12]; running max of m+τ(m) never returns to ≤ n+2 above
   the McCranie frontier; consistent with Erdős's 'extremely doubtful … infinitely many' and the
   variants.lim divergence conjecture." Includes the exact range, the validation result, and the
   completion timestamp.
2. **Dated memo** `analysis/e647_sieve/RESULT_<date>.md`: the negative result written up — range,
   method, validation against A087280, max `m+τ(m)−n` deficit observed per decade (this is data for
   Erdős's `variants.lim` conjecture that the deficit → ∞), runtime, reproducibility pointer.
3. **OEIS A087280 comment** (drafted, for human review before posting): "No further terms in
   (10^10, 10^12]; verified by independent segmented τ-sieve, <date>." Extends McCranie's recorded
   search range. **Not auto-posted** — external publication needs human sign-off.
4. **NO Aristotle submission. NO Sophie-Germain pivot.** The held June-1 debate hold on the
   Sophie-Germain residual (FALSE side) STANDS UNTOUCHED — the no-pivot tripwire. Empty closes the
   slot; it does not trigger a new attack.

### Branch B — a witness n is FOUND

1. **Exact re-verification BEFORE any claim** (two independent paths, both must agree):
   - Path 1: recompute `τ(m)` for all `m ∈ [n − 12000, n)` by direct trial factorization (independent
     of the segmented sieve) and confirm `max(m+τ(m)) ≤ n+2`; confirm no `m < n−12000` can violate
     (τ bound). Confirm `n > 24`.
   - Path 2: independent primality/factorization library (e.g. sympy `factorint` / `divisor_count`)
     on the same window, plus a spot re-derivation of the running max from a fresh sieve segment
     `[n − 2·10^6, n)`. Both paths must produce the identical witness verdict.
2. Only after both paths agree: record `compiled_advance`-track candidate, write the human-readable
   note, and route the Lean certificate through Codex locally first (factor table over the window +
   parametric global τ-bound, ceiling tracked not hardcoded; `native_decide` faces maximal scrutiny;
   NO HCN shortcut). Aristotle is the optional secondary notary only, lane=`informal`, on a hit only.
3. A single witness RESOLVES the problem (it is an existence statement). Report immediately to team-lead.

---

## 5. Logging & reproducibility

- All progress to **`analysis/e647_sieve/sieve.log`** (segment boundaries, running max, any candidate,
  any tripwire). Nice'd background CPU; does not contend with the GPU.
- Code in `analysis/e647_sieve/` (Rust production sieve + Python reference/validator). The Python
  reference `verify_predicate.py` is the ground truth the Rust sieve is diffed against.
- This pre-registration is immutable from launch; any change is a new dated revision appended below.

---

*Registered 2026-06-11 by gelfond, before the production run. Empty is a small, real, durable
contribution (a failed_approaches row + an OEIS range extension); a witness is a Lean-certifiable
resolution. The asymmetry — bounded downside with residual value, unbounded upside — is the trade.*
