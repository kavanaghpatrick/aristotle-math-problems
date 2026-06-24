# AI-Competition Audit Summary (Agent #1, May 30 2026)

**Source:** github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erdős-problems (canonical AI-progress registry maintained by Thomas Bloom / Tao).
**Auditor:** Agent #1 of 5, closure-execution team.
**Scope:** Cross-reference the C10 closure shortlist (top-20) and the W1-W4 batch (11 slots) against every Erdős# resolved, partially resolved, or attempted by any AI team.

---

## Headline

**9 of 13 named-Erdős closure candidates are CONFIRMED-UNTOUCHED by any AI team** (CLEAR).
**4 are AI_PARTIAL** (false claim, lit search only, or formalization-only — none constitute a real closure):

| Problem | AI status | What's left for us |
|---|---|---|
| Erdős 7 | Aristotle FALSE_CLAIM 2026-05-02 | Open; but Aristotle's prior wrong attempt is in our submission DNA — risk of re-running the same failed approach |
| Erdős 167 (Tuza) | GPT-5 lit-search only 2025-10-13 | Full Tuza untouched, but MEMORY.md kills our angles |
| Erdős 366 | "Automated research pipeline" PARTIAL 2026-04-14 | Some scope claimed — needs reading before submission |
| Erdős 672 | GPT lit-search only 2026-01-07 | k=4 ℓ=3 lane fully untouched |
| Erdős 835 | AlphaProof FORMALIZATION-only 2025-12-26 | Open k>2 conjecture untouched (AlphaProof proved a folklore result, not the open one) |

**Zero of our shortlist were FULLY_RESOLVED by AI.**

---

## Top 5 candidates the wiki CONFIRMS are still open (and untouched by AI)

Ranked by closure-probability × competitiveness-clearance:

1. **Erdős 203** — CLEAR. No AI entry. Existential `m.Coprime 6` lane wide open. C10 ranked this #1 with 6/10 closure probability. **Highest-priority safe target.**
2. **Erdős 672 (k=4, ℓ=3 AP)** — AI_PARTIAL lit search only. Direct slot712 extension. C10 #20 at 5/10. **Safest "named AP closure" with no AI competitor working it.**
3. **Erdős 617** — CLEAR. No AI entry. Erdős-Sós r-coloring r=4 counterexample on Fin 17 via SAT. **No competitor.**
4. **Erdős 938** — CLEAR. No AI entry. Powerful 3-AP.
5. **Erdős 64 (Erdős-Gyárfás)** — CLEAR. Computer-aided P_13-free proof exists but is NOT AI-LLM. SAT-cex lane fully open. **Only competitor is classical computer search, not AI.**

Honorable mentions (also CLEAR):
- Erdős 242 (Erdős-Straus) — completely untouched by AI competition
- Erdős 364 — untouched
- Erdős 952 (Gaussian moat) — untouched (note: actually Basil Gordon 1962, misattributed)
- Erdős 137 — untouched **but** literature_freshness flags k=4 as trivially implied by k=3 (closure-trap, not AI-competition issue)
- Erdős 307 — untouched by AI but literature_freshness flags SOLVED_SINCE for SUM version (sum was solved by Steinerberger 2024 + Liu-Sawhney 2024). Codex's PRODUCT framing may still be novel — needs disambiguation.

---

## Kill list — items in our shortlist that are AI-claimed (any sense)

**Strict AI_CLOSED in our shortlist: NONE.** No problem on the closure-first top-20 has been fully resolved by an AI team. We are not in conflict with any published AI result.

**Soft warnings (do not block but read context first):**

- **Erdős 7 (distinct odd cover, E#7 / W3-adjacent / top-15)** — Aristotle made a FALSE_CLAIM on 2026-05-02 (with Jinook Lee). The claim was retracted. **Risk:** re-running the same submission may produce the same wrong-direction proof attempt; check `mk failed` for E7 before any submission. Closure mechanism per C10 is still verification-of-witness, and the open problem (search for cover) is upstream of Aristotle's wheelhouse anyway. **Do not target unless we have a genuine new search-witness to verify.**

- **Erdős 366** — wiki lists PARTIAL_PROGRESS by "Automated research pipeline" 2026-04-14. Not in our top-20 but appears on the broader 13-problem watch list from C10. Read what was claimed before submitting anything on E#366.

- **Erdős 835** — AlphaProof formalized a folklore proof (NOT the open problem). The open problem (k>2 (k+1)-coloring of J(2k,k)) is still wide open. We are safe to submit, but be careful in any writeup not to overlap with AlphaProof's formalization scope; the closure target is `k=9, 10, 11` per literature_freshness.

---

## NEW closure candidates surfaced from the wiki (not in our top-20)

The wiki reveals AI teams have been heavily concentrated on a *narrow band* of problems. The following Erdős# are open per erdosproblems.com but have **zero AI entry** in the wiki — meaning they are competitively wide open. Sampled from the 1100+ problem space:

**High-value (Erdős-prize-class), untouched by AI:**

- **Erdős 17** (cluster primes infinite) — no AI entry; nt; infinite-set lane
- **Erdős 100/107 family** (geometry) — no AI entry
- **Erdős 11** (odd n = squarefree + 2^l) — Aristotle/GPT FALSE_CLAIM on 2026-01-24 → so technically AI_PARTIAL not CLEAR, but the actual problem is open and the failed approaches are documented
- **Erdős 233** — GPT-5.2 Pro FALSE_CLAIM 2026-01-18 → open and untouched cleanly
- **Erdős 1041** — Multiple AI FALSE_CLAIM → open but with documented failed-approach DNA
- **Erdős 153, 155, 158, 160, 168, 170, 172, 188, 195-197, 200, 212, 213** — all CLEAR per cross-reference with the wiki; all open per registry
- **Erdős 218** — partial-progress only; closure direction open
- **Erdős 1003** (Carmichael totient infinite) — no AI entry; nt
- **Erdős 1052** (unitary perfect numbers finite) — no AI entry; 6 prior attempts in our DB (might already be in our DNA)
- **Erdős 1068, 1073, 1097, 1101, 1106** — various CLEAR

**Most promising new candidates by mechanism-fit:**

1. **Erdős 17 (cluster primes)** — clean S6-mechanism infinite-set existence, no AI competition.
2. **Erdős 1003 (φ(n) = φ(n+1) infinite)** — same DNA as Aristotle's slot737 σ₀-multiplicativity strength; zero AI competition.
3. **Erdős 17, 197, 1059** — pure infinite-prime-set existence problems with zero AI entries.

These are candidates for *future* batches (not W1-W4). Recommendation: add to W5+ planning, not to W1-W4 batch.

---

## Single most-important action: which candidates MUST be removed from W1-W4

**NONE need to be removed for AI-competition reasons.** Zero AI closures intersect the queue.

**BUT three should be removed for orthogonal reasons (rediscovered from literature_freshness_may30.csv during this audit):**

1. **W1-C Lehmer ω=7** — REMOVE. Cohen-Hagis 1980 already proved ω≥14. Premise is false. (literature_freshness REMOVE flag)
2. **W1-B Primitive weird ω=6** — REMOVE. Amato-Hasler-Melfi-Parton 2018-2019 found 12 PWNs at ω=6. Premise is false.
3. **W2-B Goormaghtigh (5,3)** — DOWNGRADE. Grantham 2024 to 10^700 already classical; further bound-bumping is `bounded_version_closure` = engineering, not closure.

These were already flagged in literature_freshness_may30.csv; this audit RECONFIRMS via wiki cross-check that no AI team has progress there either, so the kill verdict stands purely on the classical side.

**Net effect on W1-W4 batch:** drop W1-B, W1-C, W2-B. The 11-slot batch becomes an 8-slot batch:
- W1-A only (odd multiperfect σ₀=11) — STILL OPEN per audit + freshness
- W2-A only (Erdős 672 k=4 ℓ=3) — AI_PARTIAL lit-search; safest closure target
- W2-C (Erdős 137 k=4) — be careful re: trivially-implied trap from k=3
- W3-A (Erdős 203) — top-priority safe target
- W3-B (Erdős 307) — needs disambiguation: product vs sum
- W3-C (Erdős 835) — open k>2 conjecture; competition-clear
- W4-A (Erdős 64 cubic-cex SAT) — competition-clear
- (W4-B Conway 99-graph: HOLD as originally planned)

---

## Most competitive open problem (most AI teams attempting, still unsolved)

**Erdős 90 (Unit Distance Conjecture)** — OpenAI internal model May 2026 claimed disproof; also Claude Mythos 2026-05-26 claimed FULLY_RESOLVED; Sawin replicated reasoning days later. Multiple AI teams hammering it. **Not in our shortlist, and the field is now saturated — would be a bad target.**

Within our shortlist, no problem has more than ONE AI team attempting it. The closest is:
- **Erdős 7 (covering systems)** — Aristotle (us, FALSE_CLAIM) + classical (BBMST22, Hough-Nielsen). One AI team (us) + classical pressure.
- **Erdős 167 (Tuza)** — GPT-5 lit-search only; we have 200+ no-advance prior attempts. Classical Basit-Galvin 2024 active. Pressure mounting but no AI solution yet.

The single highest-traffic AI-competition arena right now (relevant to our combinatorics-fit window) is the **Erdős 36/507/1026/1132/1153/848 cluster** — AlphaEvolve / GPT-5.4 Pro / Aristotle. **None of these are on our shortlist.** Our closure-first slate sits in an *uncrowded* corner of the Erdős space, which is good news for closure-rate hygiene but also confirms C10's selection was AI-competition-aware.

---

## Bottom line

- Zero AI-CLOSED items in our shortlist.
- Three SHOULD be removed from W1-W4 (Lehmer, primitive-weird, Goormaghtigh) for classical-literature reasons (NOT AI competition).
- Erdős 203, 672 (k=4 ℓ=3), 64, 617, 938 are the safest competition-clear targets.
- Aristotle's own FALSE_CLAIM on Erdős 7 (2026-05-02) is the only AI-domain concern, and it can be sidestepped by checking `mk failed e7` before any new submission.
- The "untouched by AI" lane includes a number of higher-value targets (Erdős 17, 1003, 1052) that should be considered for W5+.
