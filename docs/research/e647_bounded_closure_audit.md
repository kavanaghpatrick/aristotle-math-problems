# Erdős 647 — Bounded-False Closure Audit

**Date:** 2026-05-30
**Subject:** slot723 + slot737 + R10 (UUID `9c30dee3`)
**Claim under audit:** "Erdős 647 inequality `∃ n > 24, max_{m<n}(m+τ(m)) ≤ n+2` is proven false on the entire range [25, 10^6]."

---

## 1. The problem (precisely)

Erdős 647 asks whether there exists `n > 24` with `max_{m<n}(m + τ(m)) ≤ n + 2`. An `n` with this property is called a **barrier** for `m + τ(m)` (Smarandache 2007 nomenclature; Erdős, *Mathematics Magazine* 52 (1979), Problem 4, p. 68; Guy, *Unsolved Problems in Number Theory*, B8). Erdős found it "extremely doubtful" any such `n` exists; the £25 prize is for a single example `n > 24`.

A `n` is a barrier iff `n ∈ A087280`.

## 2. Literature status — DEFINITIVE

**OEIS A087280** ("Solutions `n` of `max(m+d(m)) = n+2` for `m < n`"):

- Authored by Jud McCranie, 2003-08-28.
- Five known terms: **5, 8, 10, 12, 24**.
- Comment: **"It is not known if there are other terms. There are no more terms < 10^10."**
- Last revision 2018-12-01.

The `teorth/erdosproblems` canonical database lists problem 647 with `status: verifiable, last_update: 2025-08-31`, prize £25, formalized in `FormalConjectures/ErdosProblems/647.lean`. The "verifiable" tag confirms that no proof or disproof is known — only computational data.

McCranie's 2003 sieve search (`< 10^10`) is **10^4× stronger** than the [25, 10^6] window. Tenenbaum's 2013 survey (arXiv:1908.00488) revisits Erdős's 1979 problems but introduces no new techniques for this one. Smarandache 2007 (arXiv:0705.1381) discusses Erdős "barriers" only for `εω(n)`, not `τ`. Pollack–Pomerance work on `σ(n)`-fibers, the Erdős–Pomerance–Sárközy 1987 paper on `d(n)=d(n+1)`, Heath-Brown / Hildebrand on the Erdős–Mirsky conjecture, and recent Tao–Teräväinen correlation work all touch the divisor function but **do not address the `m+τ(m)` barrier problem at all**.

## 3. What slot723 + slot737 + R10 actually proves

- **slot723** (UUID `d3af7e55`): `witness_for_all` for `n ≥ 25` falls back to `sorry` precisely on the Sophie-Germain configuration (`n ≡ 0 (mod 6)`, `n−1` prime, `(n−2)/2` prime). The "negation of E647" theorem holds only modulo this sorry.
- **slot737** (UUID `d10f9308`): closes the sub-case where `n−1` prime, `q=(n−2)/2` prime, and **at least one of** `(q−1)/2` or `(2q−1)/3` is composite. Uses elementary `σ₀`-multiplicativity (`σ₀(4d) ≥ 7` for composite `d ≥ 749`; `σ₀(3c) ≥ 6` for composite `c ≥ 999`). No sorries, no axioms in the file. **Valid sub-case**.
- **R10 / slot741** (UUID `9fa69652`): handles the residual 35-case Cunningham chain `(n−1, q, (q−1)/2, (2q−1)/3)` all prime in `[3000, 10^6]` via a `native_decide` witness table (offsets 5 or 6).

Composed, these discharge slot723's `sorry` on `[25, 10^6]`. Mathematically this is a finite case-split: every barrier candidate `n ∈ [25, 10^6]` has an explicit witness `m < n` with `m + τ(m) > n + 2`.

## 4. Classification

**TRIVIAL / SUBSUMED.**

- The headline result ("no barriers above 24 on `[25, 10^6]`") is a strict weakening of McCranie's 2003 OEIS computation to `10^10`. A textbook sieve handles it in seconds.
- The "structural insight" — that the obstruction is the Sophie Germain / Cunningham residual — is not new: Erdős's 1979 footnote, Guy §B8, and the OEIS comment all note that the only candidates one needs to handle are configurations where `n−1` or `n−2` is forced to have few divisors (i.e. is prime or twice-prime). The 35-element enumeration is just the leaves of that tree restricted to `n ≤ 10^6`.
- The unbounded conjecture (`limsup max(τ(m)+m−n) = ∞`, formal-conjectures 647 variant `lim`) **remains entirely open**. Nothing here advances it. Schinzel's Hypothesis H still required for the related "seems certain" variant.

The Lean artifact is a partial formalization of well-known computational content. Even as a Lean contribution, slot723 retains a `sorry` until R10 is glued in, and R10 leans on `native_decide` over an enumerated set — i.e. a Lean-checked transcript of McCranie's sieve, restricted to a smaller range.

## 5. Realistic publication path

- **As a research paper**: none. The result is subsumed by 10^4 by an OEIS entry from 2003 with a one-line comment. There is no novel theorem, no new structural reduction, no progress on the unbounded conjecture.
- **As a Lean / Mathlib contribution**: marginal. A genuinely useful formalization would either (a) match or exceed McCranie's `10^10` bound inside Lean, or (b) provide a Lean-level proof of the `m+τ(m)` infrastructure (the `σ₀`-multiplicativity lemmas in slot737 are mildly reusable). Submission to `FormalConjectures/ErdosProblems/647.lean` as a partial-result variant theorem (e.g. `erdos_647_no_barrier_below_1e6 : ∀ n, 25 ≤ n → n ≤ 10^6 → ¬ (⨆ m : Fin n, m + σ 0 m) ≤ n + 2`) is the maximum honest framing — and would have to compete against the OEIS-known `10^10` upper end of verified emptiness.
- **DB classification**: `compiled_no_advance` is correct. Do **not** mark `target_resolved=1`. Do **not** issue a `contribution_statement` claiming closure of E647 — the open problem is the unbounded version, untouched.

## 6. Honest one-liner

We re-derived, in Lean, a strict subset of a 2003 OEIS computation that nobody has published as a paper because the open conjecture (`limsup = ∞`) is what matters and remains hopeless without Hypothesis H or Maynard-sieve advances.

---

**Sources**

- [Erdős Problem #647 on erdosproblems.com](https://www.erdosproblems.com/647) (status: `verifiable`, prize £25)
- [OEIS A087280](https://oeis.org/A087280) — McCranie 2003, no barriers in `(24, 10^10]`
- [Erdős, Some Unconventional Problems in Number Theory, Math. Mag. 52 (1979), Problem 4, p. 68](https://www.jstor.org/stable/2689842)
- [`teorth/erdosproblems/data/problems.yaml`](https://github.com/teorth/erdosproblems/blob/main/data/problems.yaml) — entry 647
- [`FormalConjectures/ErdosProblems/647.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/647.lean) (Google DeepMind)
- [Smarandache, *On Two of Erdős's Open Problems*, arXiv:0705.1381](https://arxiv.org/abs/0705.1381) — discusses "barrier" terminology (for `εω(n)`, not `τ`)
- [Tenenbaum, *Some of Erdős' Unconventional Problems… Thirty-four Years Later*, arXiv:1908.00488](https://arxiv.org/abs/1908.00488)
- Local artifacts:
  - `/Users/patrickkavanagh/math/submissions/nu4_final/slot723_extracted/.../Main.lean` (sorry on Sophie case)
  - `/Users/patrickkavanagh/math/submissions/nu4_final/slot737_extracted/.../Erdos647.lean` (sub-case closed)
  - `/Users/patrickkavanagh/math/submissions/nu4_final/slot741_extracted/.../Main.lean` (35-case `native_decide`)
  - `/Users/patrickkavanagh/math/analysis/erdos647_cunningham_witnesses.json` (35 explicit witnesses)
