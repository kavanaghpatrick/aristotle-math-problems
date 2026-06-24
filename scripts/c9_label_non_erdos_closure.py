#!/usr/bin/env python3
"""
C9 (retry): apply 4-axis closure taxonomy + closure_score to non-Erdos problems.

Inputs available:
  - docs/closure_taxonomy_may30.md          (taxonomy spec)
  - analysis/non_erdos_labeled_may30.csv    (275 problems, prior labels)
  - analysis/open_problems_registry_may30.csv (805 entries, freshness)
  - analysis/literature_freshness_may30.csv (22 manual triage)

Output:
  - analysis/non_erdos_closure_labeled.csv

Axes per CLOSURE_TAXONOMY:
  CS  Closure Scope        {full_closure, direction_closure, disproof_closure,
                            bounded_version_closure, sub_claim_closure, formalization_only}
  CM  Closure Mechanism    {explicit_witness, bounded_to_infinite_lift,
                            structural_finite_reduction, disproof_construction,
                            witness_table_chunked, density_sieve_closure,
                            induction_template, none_known}
  CR  Closure Risk         {clean_decidable, partial_result_only, iff_rfl_trap,
                            witness_search_explosion, definition_mismatch,
                            em_tautology, infrastructure_overgrowth,
                            recursive_falsification}
  HM  Honesty Marker       {journal_clean, journal_partial, journal_subclaim,
                            infrastructure_only}

closure_score formula (consistent with C8 spec inferred from taxonomy):
  base from HM:
    journal_clean    -> 8
    journal_subclaim -> 5
    journal_partial  -> 3
    infrastructure_only -> 0
  adjustments:
    CS = full_closure   -> +2
    CS = direction_closure / disproof_closure -> +1
    CS = formalization_only -> -3
    CR = iff_rfl_trap / em_tautology / infrastructure_overgrowth -> -3
    CR = recursive_falsification / definition_mismatch -> -2
    CR = partial_result_only -> -1
    CR = clean_decidable -> +1
    CM = none_known -> -3
    CM = density_sieve_closure / induction_template -> -2
    CM = explicit_witness / disproof_construction / witness_table_chunked / structural_finite_reduction -> +1
  cap to [0, 10]

action:
  REAL closure candidate: CS in {full,direction,disproof} AND CM != none_known AND
                          CR in {clean_decidable, witness_search_explosion (if chunked)} AND
                          HM = journal_clean      -> CLOSURE_CANDIDATE
  Strategic subclaim:     CS in {sub_claim, bounded_version} AND
                          CM in {witness, witness_table_chunked, structural_finite_reduction, disproof_construction} AND
                          HM in {journal_partial, journal_subclaim}  -> STRATEGIC_SUBCLAIM
  Everything else      -> AVOID (infrastructure_only); special tags for SOLVED/AMBIGUOUS.
"""
import csv
import os
import sys

ROOT = "/Users/patrickkavanagh/math"
LABELED = os.path.join(ROOT, "analysis/non_erdos_labeled_may30.csv")
REGISTRY = os.path.join(ROOT, "analysis/open_problems_registry_may30.csv")
LITFRESH = os.path.join(ROOT, "analysis/literature_freshness_may30.csv")
OUT = os.path.join(ROOT, "analysis/non_erdos_closure_labeled.csv")


# ----------------- LITERATURE OVERRIDES (from C5 + C6) -----------------
# Map (source, theorem_name) -> override dict.
# Keys: solved (bool), solved_year, solved_note, ambiguous (bool).
LIT_OVERRIDES = {
    # Casas-Alvero conjecture: SOLVED 2025 by Ghosh (arXiv:2501.09272) for all d>=3.
    ("Paper", "casas_alvero_conjecture"): {
        "solved": True,
        "solved_year": "2025",
        "solved_note": "Ghosh 2025 (arXiv:2501.09272) full conjecture; remove from closure lane",
    },
    # Brocard problem: STILL_OPEN per Berndt-Galway / 2025 status; n<=10^9 verified.
    # The Lean statement is the unbounded version. slot738 already submitted as bounded extension.
    ("Wikipedia", "brocard_conjecture"): {
        "brocard_extension": True,
    },
    # Pollock tetrahedral (Salzer-Levine 1948 result form): published; the "IsGreatest 343867"
    # statement is formalization of a published bound.
    ("Wikipedia", "pollock_tetrahedral"): {
        "formalization": True,
    },
    # Lonely runner: Tao et al. recent progress; n<=8 known.
    # Leinster groups: per MEMORY.md slot739 was formalization_only.
    ("Wikipedia", "infinitely_many_leinster_groups"): {
        "memo_attempted": True,
        "memo_note": "slot739-related; per MEMORY directive: formalization-only attempts, not closure",
    },
    # Gilbreath: verified to 10^13 (Odlyzko etc).
    # Goldbach: verified to 4*10^18, still open infinite.
    # ABC: Mochizuki dispute -> still open.
    # Schanuel, Littlewood, Lehmer Mahler measure: all famous transcendence problems.
    # Pillai-Catalan: Mihailescu proved Catalan; Pillai's open.
    # Kakeya: Wang-Zahl announced May 2025 proof of full conjecture per recent buzz, but not yet peer-reviewed
    # — treat as STILL_OPEN with disclosure.
}


def load_csv(path):
    with open(path) as f:
        return list(csv.DictReader(f))


def build_registry_index(rows):
    """Index registry by theorem_name (registry uses theorem_name as problem_id)."""
    return {r["problem_id"]: r for r in rows}


# ----------------- Classification heuristics -----------------

# Source -> default closure posture
SOURCE_DEFAULTS = {
    "Millenium": {"hm": "infrastructure_only", "cm": "none_known",
                  "cr_primary": "iff_rfl_trap", "cs": "full_closure",
                  "note": "Millennium-class; no closure mechanism in Aristotle's repertoire"},
}


# Wikipedia famous-set: extreme problems where the answer is unambiguously AVOID
WIKIPEDIA_FAMOUS_TARGETS = {
    # Targets that should land HM=infrastructure_only by inspection.
    # mapped to a short rationale.
    "twin_primes":              "iff_rfl_trap; Set.Infinite wrapper; no closure mechanism",
    "goldbach":                 "infinite-parametric existence; density_sieve_closure unavailable",
    "collatz_conjecture":       "infinite-parametric; no induction template Aristotle has invented",
    "abc":                      "Set.Infinite / density wrapper; no closure mechanism",
    "lonely_runner_conjecture": "infinite-parametric; case-analysis intractable",
    "jacobian_conjecture":      "polynomial Jacobian over fields; theory-heavy formalization gap (F10)",
    "kakeya_set_conjecture":    "geometric measure theory; theory-heavy partial; iff_rfl_trap",
    "MLC":                      "LocallyConnectedSpace mandelbrotSet; theory-heavy + F1 wrapper",
    "MLC_general_exponent":     "F1 / iff_rfl wrapper",
    "density_of_hyperbolicity": "infinite-parametric F3",
    "density_of_hyperbolicity_general_exponent": "infinite-parametric F3",
    "volume_frontier_mandelbrotSet_eq_zero":     "theory-heavy / F3",
    "volume_frontier_multibrotSet_eq_zero":      "theory-heavy / F3",
    "schanuel_conjecture":      "transcendence; theory-heavy formalization gap",
    "littlewood_conjecture":    "iff_rfl_trap; Tendsto wrapper",
    "padic_littlewood_conjecture": "iff_rfl_trap; Tendsto wrapper",
    "lehmer_mahler_measure_problem": "theory-heavy; infinite-parametric",
    "P_ne_NP":                  "complexity-class equality; no closure mechanism",
    "NP_ne_coNP":               "complexity-class equality; no closure mechanism",
    "generalized_riemann_hypothesis": "Set.Infinite / Tendsto on L-zeros; F1 + F3",
    "bunyakovsky_conjecture":   "infinite-parametric prime-density",
    "first_hardy_littlewood_conjecture": "density-sieve",
    "second_hardy_littlewood_conjecture": "density-sieve",
    "charmichaelTotient":       "infinite-parametric, no advance signal",
    "regularprime_conjecture":  "infinite-parametric prime-density",
    "vaught_conjecture":        "logic, partial Mathlib coverage",
    "kummer_vandiver":          "iwasawa-theoretic; theory-heavy",
    "infinitely_many_woodall_primes": "density-sieve; F3",
    "agoh_giuga":               "infinite-parametric Bernoulli condition; F3",
    "perfect_euler_brick_existence": "infinite-parametric existence",
    "bateman_horn_conjecture":  "Set.Infinite / iff_rfl_trap",
    "firoozbakht_conjecture":   "infinite-parametric prime gaps",
    "feit_thompson_primes":     "advance-known but no closure mechanism for Aristotle",
    "andrica_conjecture":       "infinite-parametric prime gaps; no decidable scaffold",
    "infinite_pellNumber_primes": "infinite-parametric prime density",
    "lemoine_conjecture":       "infinite-parametric existential; F3",
    "lemoine_conjecture_extension": "infinite-parametric existential; F3",
    "lonely_runner_conjecture": "infinite-parametric F3",
    "lehmer_ramanujan_tau":     "theory-heavy; modular forms",
    "lehmer_totient":           "infinite-parametric existence; F8",
    "polignac_conjecture":      "density-sieve",
    "dickson_conjecture":       "density-sieve",
    "polignac_conjecture":      "density-sieve",
    "selfridge_conjecture":     "F3",
    "selfridge_seq_conjecture": "F3",
    "infinite_prime_sq_add_one": "Landau's 4th problem; density-sieve",
    "balanced_primes":          "F8",
    "balanced_primes_order":    "F8",
    "artin_primitive_roots":    "Set.Infinite + GRH-conditional; F1",
    "pillais_conjecture":       "infinite-parametric existence",
    "lebesgue_nagell":          "F3",
    "isSumOfThreeCubes_iff_mod_9": "F8",
    "fermat_catalan":           "F3",
    "union_closed":             "infinite-parametric F3",
    "rational_distance_problem": "F8",
    "mahler_conjecture":        "theory-heavy",
    "sendov_conjecture":        "F3",
    "magic_square_squares":     "F8",
    "exists_magic_square_squares": "F8",
    "determinantal_conjecture": "F3 linear-algebra heavy",
    "class_number_problem":     "F3 algebraic NT",
    "infinitely_many_mersenne_primes": "F8",
    "infinite_fermat_primes":   "F8",
    "infinite_fermat_composite": "F8",
    "fermat_number_are_composite": "F8",
    "all_fermat_squarefree":    "F8",
    "infinite_prime_euclid_numbers": "F8",
    "euclid_numbers_are_square_free": "F8",
    "beal_conjecture":          "F3",
    "Invariant_subspace_problem": "F3 functional analysis",
    "BB_6":                     "infinite-parametric F8; BB is uncomputable",
    "snake_dim_nine":           "F8; small case",
    "infinitely_many_leinster_groups": "MEMORY: slot739 formalization-only; no closure path",
    "wolstenholme_prime_infinite": "F3",
    "fib_primes_infinite":      "F3 density",
    "oppermann_conjecture":     "F3",
    "Tunnell_odd_converse":     "F3 BSD-conditional",
    "Tunnell_even_converse":    "F3 BSD-conditional",
    "herzog_schonheim_conjecture": "F3 group theory",
    "least_eleven_square_packing_in_square": "F8 partial Mathlib",
    "least_seventeen_square_packing_in_square": "F8 partial Mathlib",
    "least_three_square_packing_in_circle": "F8",
    "least_twenty_one_circle_packing_in_square": "F8",
    "least_fifteen_circle_packing_in_circle":   "F8",
    "infinite_safe_primes":     "F3",
    "infinite_cousin_primes":   "F3",
    "infinite_sexy_primes":     "F3",
    "exists_isWallSunSunPrime": "F3",
    "infinite_isWallSunSunPrime": "F3",
    "infinite_isWallSunSunPrime_of_disc_eq": "F3",
    "mean_value_problem":       "F3",
    "hall_conjecture":          "F3",
    "weak_hall_conjecture":     "F3",
    "pierce_birkhoff_conjecture": "F3 real algebra",
    "rectangles_cover_unit_square": "F8 geometry-heavy",
    "rectangles_pack_unit_square":  "F8 geometry-heavy",
    "exists_semiring_unique_left_right_maximal_ne": "F8 ring theory",
    "complexity_two_pow":       "F8 / undecidable surface",
}


# Brocard variant special handling
BROCARD_ID = ("Wikipedia", "brocard_conjecture")

# Pollock special handling
POLLOCK_ID = ("Wikipedia", "pollock_tetrahedral")


def classify(row, reg, lit_solved=False, lit_solved_year=None, lit_solved_note=None,
             ambiguous=False, ambiguous_note=None):
    """Return dict with CS/CM/CR/HM + score + action + rationale."""
    pid = row["problem_id"]
    source = row["source"]
    thname = row["theorem_name"]
    feasibility = row["feasibility_category"]
    qgeom = row["quantifier_geometry"]
    cert = row["certificate_shape"]
    snipe_match = row["snipe_signature_match"]
    failure = row["failure_mode_risk"]
    surface = row["formalization_surface"]
    domain = row["domain"]
    score_input = int(row["snipe_score_1_to_10"] or 1)

    # SOLVED override
    if lit_solved:
        return {
            "closure_scope": "formalization_only",
            "closure_mechanism": "none_known",
            "closure_risk_primary": "definition_mismatch",
            "closure_risk_secondary": "",
            "honesty_marker": "infrastructure_only",
            "closure_score": 0,
            "action": "REMOVE_SOLVED_SINCE",
            "real_closure_candidate": False,
            "strategic_subclaim": False,
            "closure_rationale": f"Solved {lit_solved_year}: {lit_solved_note}",
        }

    # AMBIGUOUS - hold for manual triage
    if ambiguous:
        return {
            "closure_scope": "formalization_only",
            "closure_mechanism": "none_known",
            "closure_risk_primary": "definition_mismatch",
            "closure_risk_secondary": "partial_result_only",
            "honesty_marker": "infrastructure_only",
            "closure_score": 1,
            "action": "HOLD_AMBIGUOUS",
            "real_closure_candidate": False,
            "strategic_subclaim": False,
            "closure_rationale": f"Ambiguous status: {ambiguous_note}",
        }

    # Millennium-class
    if source == "Millenium":
        return _result("full_closure", "none_known", "iff_rfl_trap",
                       "infrastructure_overgrowth",
                       "infrastructure_only",
                       "AVOID",
                       "Millennium-class; no closure mechanism in Aristotle's repertoire", 0)

    # Brocard - distinguish full conjecture vs bounded extension
    if (source, thname) == BROCARD_ID:
        return _result(
            "bounded_version_closure",
            "witness_table_chunked",
            "clean_decidable",
            "witness_search_explosion",
            "journal_partial",
            "STRATEGIC_SUBCLAIM",
            "Brocard full conjecture is unbounded; slot738 [501,1000] precedent shows bounded extension "
            "is publishable as 'Brocard verified for n<=N' but does NOT close the conjecture. "
            "Treat as bounded_version_closure not full closure.",
            score=4,
        )

    # Pollock - formalization-only
    if (source, thname) == POLLOCK_ID:
        return _result(
            "formalization_only",
            "explicit_witness",
            "clean_decidable",
            "witness_search_explosion",
            "infrastructure_only",
            "FORMALIZATION_ONLY",
            "Pollock tetrahedral: Salzer-Levine 1948 result (greatest n not expressible as 4 tetrahedral = 343867). "
            "Bounded verification of a published bound; not new math.",
            score=0,
        )

    # Casas-Alvero - solved already handled above
    # General Wikipedia-famous bucket -> infrastructure_only by inspection
    if source == "Wikipedia" and thname in WIKIPEDIA_FAMOUS_TARGETS:
        note = WIKIPEDIA_FAMOUS_TARGETS[thname]
        # pick CR based on F-trap
        if failure.startswith("F1") or failure == "F1-iff-rfl":
            cr = "iff_rfl_trap"
        elif failure.startswith("F8"):
            cr = "iff_rfl_trap"  # F8 vacuous iff is a variant
        elif failure.startswith("F3"):
            cr = "infrastructure_overgrowth"
        else:
            cr = "infrastructure_overgrowth"
        return _result(
            "full_closure",
            "none_known",
            cr,
            "infrastructure_overgrowth",
            "infrastructure_only",
            "AVOID",
            f"Wikipedia famous: {note}",
            score=0,
        )

    # ---- General source-blind heuristics ----
    # Map snipe scaffold matches to CS/CM
    if snipe_match == "S2-table-bridge":
        return _result(
            "bounded_version_closure",
            "witness_table_chunked",
            "clean_decidable",
            "witness_search_explosion",
            "journal_partial",
            "STRATEGIC_SUBCLAIM",
            "S2-table-bridge: chunked witness table; bounded extension of underlying infinite conjecture",
            score=4,
        )
    if snipe_match == "S6-graph-cex":
        return _result(
            "disproof_closure",
            "disproof_construction",
            "clean_decidable",
            "recursive_falsification",
            "journal_clean" if score_input >= 5 else "journal_subclaim",
            "CLOSURE_CANDIDATE" if score_input >= 5 else "STRATEGIC_SUBCLAIM",
            "S6-graph-cex: explicit counterexample possible; check for falsified-approach overlap (F5)",
            score=6 if score_input >= 5 else 5,
        )

    # Bounded / finite verification
    if feasibility == "finite-verification" or qgeom == "bounded-finite":
        return _result(
            "bounded_version_closure",
            "explicit_witness",
            "clean_decidable",
            "",
            "journal_partial",
            "STRATEGIC_SUBCLAIM",
            "Bounded-finite: native_decide candidate but only closes a bounded sub-question",
            score=4,
        )

    # Default by feasibility_category + failure_mode
    cs = "full_closure"
    cm = "none_known"
    if cert == "explicit-witness":
        cm = "explicit_witness"
        cs = "sub_claim_closure"
    elif cert == "small-table":
        cm = "witness_table_chunked"
        cs = "bounded_version_closure"
    elif cert == "pure-existence":
        cm = "explicit_witness"
        cs = "sub_claim_closure"
    elif cert == "universal-negative":
        # 'universal-negative' often means "no n exists s.t. P n" — that is
        # the open statement itself, not a disproof construction. A real
        # disproof construction needs an exhibited counterexample, which
        # implies theory-heavy/transcendence statements DON'T qualify.
        # Distinguishing rule: if formalization_surface is 'mathlib-native'
        # and the statement is decidable per element, treat as disproof_closure;
        # else AVOID (this is the open statement, not an attainable witness).
        if surface == "mathlib-native" and feasibility != "known-formalization":
            cm = "disproof_construction"
            cs = "disproof_closure"
        else:
            cm = "none_known"
            cs = "full_closure"
    elif cert == "none-known":
        cm = "none_known"
        cs = "full_closure"

    # CR by failure_mode
    cr_primary = "infrastructure_overgrowth"
    cr_secondary = ""
    if failure == "F1-iff-rfl":
        cr_primary = "iff_rfl_trap"
    elif failure == "F8-vacuous-iff":
        cr_primary = "iff_rfl_trap"
    elif failure == "F3-side-lemma-bloat":
        cr_primary = "infrastructure_overgrowth"
    elif failure == "F9-compute-explosion":
        cr_primary = "witness_search_explosion"
    elif failure == "F10-def-mismatch":
        cr_primary = "definition_mismatch"

    # HM
    if cm == "none_known":
        hm = "infrastructure_only"
        action = "AVOID"
    elif cs in ("disproof_closure",):
        hm = "journal_clean"
        action = "CLOSURE_CANDIDATE"
    elif cs in ("sub_claim_closure", "bounded_version_closure"):
        hm = "journal_partial" if cs == "bounded_version_closure" else "journal_subclaim"
        action = "STRATEGIC_SUBCLAIM"
    else:
        hm = "infrastructure_only"
        action = "AVOID"

    # Score
    score = _score(cs, cm, cr_primary, hm)
    rationale = f"feasibility={feasibility}; qgeom={qgeom}; cert={cert}; failure={failure}"
    return _result(cs, cm, cr_primary, cr_secondary, hm, action, rationale, score=score)


def _score(cs, cm, cr, hm):
    base = {"journal_clean": 8, "journal_subclaim": 5,
            "journal_partial": 3, "infrastructure_only": 0}.get(hm, 0)
    if cs == "full_closure":
        base += 2
    elif cs in ("direction_closure", "disproof_closure"):
        base += 1
    elif cs == "formalization_only":
        base -= 3
    if cr in ("iff_rfl_trap", "em_tautology", "infrastructure_overgrowth"):
        base -= 3
    elif cr in ("recursive_falsification", "definition_mismatch"):
        base -= 2
    elif cr == "partial_result_only":
        base -= 1
    elif cr == "clean_decidable":
        base += 1
    if cm == "none_known":
        base -= 3
    elif cm in ("density_sieve_closure", "induction_template"):
        base -= 2
    elif cm in ("explicit_witness", "disproof_construction",
                "witness_table_chunked", "structural_finite_reduction"):
        base += 1
    return max(0, min(10, base))


def _result(cs, cm, cr_primary, cr_secondary, hm, action, rationale, score=None):
    if score is None:
        score = _score(cs, cm, cr_primary, hm)
    real_cc = (cs in ("full_closure", "direction_closure", "disproof_closure")
               and cm != "none_known"
               and cr_primary in ("clean_decidable", "witness_search_explosion")
               and hm == "journal_clean")
    sub_cc = (cs in ("sub_claim_closure", "bounded_version_closure")
              and cm in ("explicit_witness", "witness_table_chunked",
                         "structural_finite_reduction", "disproof_construction")
              and hm in ("journal_partial", "journal_subclaim"))
    return {
        "closure_scope": cs,
        "closure_mechanism": cm,
        "closure_risk_primary": cr_primary,
        "closure_risk_secondary": cr_secondary,
        "honesty_marker": hm,
        "closure_score": score,
        "action": action,
        "real_closure_candidate": real_cc,
        "strategic_subclaim": sub_cc,
        "closure_rationale": rationale,
    }


# -------------------- Driver --------------------

def main():
    labeled = load_csv(LABELED)
    registry = load_csv(REGISTRY)
    litfresh = load_csv(LITFRESH)
    reg_idx = build_registry_index(registry)
    # Map registry freshness flags
    fresh_idx = {r["problem_id"]: r.get("freshness_flag", "") for r in registry}

    # Map literature_freshness rows by problem_id
    lit_idx = {r["problem_id"]: r for r in litfresh}

    out_rows = []
    counts = {"CLOSURE_CANDIDATE": 0, "STRATEGIC_SUBCLAIM": 0, "AVOID": 0,
              "REMOVE_SOLVED_SINCE": 0, "HOLD_AMBIGUOUS": 0, "FORMALIZATION_ONLY": 0}
    domain_counts = {}
    by_source = {}

    for row in labeled:
        thname = row["theorem_name"]
        source = row["source"]
        # Lookup overrides
        ov = LIT_OVERRIDES.get((source, thname), {})
        # Cross-check registry freshness via theorem_name
        reg_fresh = fresh_idx.get(thname, "")
        ambiguous = (reg_fresh == "AMBIGUOUS") or (reg_fresh == "POSSIBLY_SOLVED_SINCE")
        ambig_note = f"registry freshness_flag={reg_fresh}" if ambiguous else ""

        if ov.get("solved"):
            cls = classify(row, reg_idx,
                           lit_solved=True,
                           lit_solved_year=ov.get("solved_year"),
                           lit_solved_note=ov.get("solved_note"))
        elif ambiguous:
            cls = classify(row, reg_idx,
                           ambiguous=True,
                           ambiguous_note=ambig_note)
        else:
            cls = classify(row, reg_idx)

        action = cls["action"]
        counts[action] = counts.get(action, 0) + 1
        domain_counts[row["domain"]] = domain_counts.get(row["domain"], 0) + 1
        by_source[source] = by_source.get(source, {"total": 0, "AVOID": 0,
                                                   "CLOSURE_CANDIDATE": 0,
                                                   "STRATEGIC_SUBCLAIM": 0})
        by_source[source]["total"] += 1
        by_source[source][action] = by_source[source].get(action, 0) + 1

        out_rows.append({
            **row,
            **cls,
            "registry_freshness": reg_fresh,
            "override_note": ov.get("solved_note") or ov.get("memo_note") or "",
        })

    # Write output
    fieldnames = list(out_rows[0].keys())
    with open(OUT, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(out_rows)

    print(f"Wrote {OUT}  ({len(out_rows)} rows)")
    print()
    print("Action distribution:")
    for k, v in sorted(counts.items(), key=lambda x: -x[1]):
        print(f"  {k}: {v}")
    print()
    print("By source:")
    for src, st in sorted(by_source.items(), key=lambda x: -x[1]["total"]):
        print(f"  {src}: total={st['total']}  "
              f"AVOID={st.get('AVOID',0)}  "
              f"CCAND={st.get('CLOSURE_CANDIDATE',0)}  "
              f"STRAT={st.get('STRATEGIC_SUBCLAIM',0)}  "
              f"REMOVE={st.get('REMOVE_SOLVED_SINCE',0)}  "
              f"HOLD={st.get('HOLD_AMBIGUOUS',0)}  "
              f"FORMAL={st.get('FORMALIZATION_ONLY',0)}")
    print()
    print("Top 10 CLOSURE_CANDIDATE / STRATEGIC_SUBCLAIM by closure_score:")
    top = sorted(out_rows,
                 key=lambda r: (-int(r['closure_score']),
                                0 if r['action'] == 'CLOSURE_CANDIDATE' else 1))
    shown = 0
    for r in top:
        if r['action'] in ('CLOSURE_CANDIDATE', 'STRATEGIC_SUBCLAIM'):
            print(f"  [{r['closure_score']}] {r['action']}: {r['problem_id']}  "
                  f"CS={r['closure_scope']} CM={r['closure_mechanism']} "
                  f"HM={r['honesty_marker']}  ({r['domain']})")
            shown += 1
            if shown >= 15:
                break

    print()
    print("Top 5 GreensOpenProblems by closure_score:")
    greens = sorted([r for r in out_rows if r['source'] == 'GreensOpenProblems'],
                    key=lambda r: -int(r['closure_score']))
    for r in greens[:5]:
        print(f"  [{r['closure_score']}] {r['action']}: {r['theorem_name']}  "
              f"CS={r['closure_scope']} CM={r['closure_mechanism']} "
              f"HM={r['honesty_marker']}")

    print()
    print("Wikipedia famous-set verdicts (sample):")
    famous = ['twin_primes', 'goldbach', 'collatz_conjecture', 'abc', 'jacobian_conjecture',
              'kakeya_set_conjecture', 'casas_alvero_conjecture', 'MLC', 'P_ne_NP',
              'brocard_conjecture', 'union_closed', 'lonely_runner_conjecture',
              'pollock_tetrahedral', 'generalized_riemann_hypothesis',
              'irrational_five', 'four_exponentials_conjecture', 'beal_conjecture',
              'lehmer_totient', 'lemoine_conjecture', 'andrica_conjecture']
    for r in out_rows:
        if r['theorem_name'] in famous:
            print(f"  {r['theorem_name']}: action={r['action']} score={r['closure_score']} HM={r['honesty_marker']} CR={r['closure_risk_primary']}")


if __name__ == "__main__":
    main()
