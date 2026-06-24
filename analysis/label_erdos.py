#!/usr/bin/env python3
"""Label every Erdős problem in formal-conjectures against the merged taxonomy.

Output: /Users/patrickkavanagh/math/analysis/erdos_labeled_may30.csv

Authority: merged_taxonomy_may30.md (this agent), feasibility_filter_rubric.md (binding gate).
"""
import os
import re
import csv
import json
import sqlite3
from pathlib import Path

ROOT = Path('/Users/patrickkavanagh/math')
DIR = ROOT / 'formal-conjectures/FormalConjectures/ErdosProblems'
DB = ROOT / 'submissions/tracking.db'
OUT = ROOT / 'analysis/erdos_labeled_may30.csv'

# ----------------------------------------------------------------------------
# Step 1: Attempt history from DB
# ----------------------------------------------------------------------------
conn = sqlite3.connect(str(DB))
cur = conn.cursor()
attempts = {}
for row in cur.execute("""
SELECT problem_id, status, COUNT(*)
FROM submissions
WHERE problem_id IS NOT NULL AND lower(problem_id) LIKE 'erdos%'
GROUP BY problem_id, status
"""):
    pid, status, cnt = row
    if not pid:
        continue
    m = re.match(r'(?:erdos|Erdos)_?(\d+)', pid, re.IGNORECASE)
    if m:
        num = m.group(1)
        d = attempts.setdefault(num, {
            'total': 0, 'adv': 0, 'dis': 0, 'no_adv': 0, 'failed': 0, 'sub': 0
        })
        d['total'] += cnt
        if status == 'compiled_advance':
            d['adv'] += cnt
        elif status == 'disproven':
            d['dis'] += cnt
        elif status == 'compiled_no_advance':
            d['no_adv'] += cnt
        elif status == 'compile_failed':
            d['failed'] += cnt
        elif status == 'submitted':
            d['sub'] += cnt
conn.close()

# ----------------------------------------------------------------------------
# Step 2: Classify each Erdős file
# ----------------------------------------------------------------------------
def classify(pid: str, text: str):
    """Return a dict of taxonomy labels for the file."""
    # ---- Pull main "research open" docstring + theorem
    open_thm = None
    main_doc = None
    for m in re.finditer(
        r'/--\s*([\s\S]*?)-/\s*@\[category research open[^\]]*\]\s*theorem\s+([\w.]+)([\s\S]*?):=\s*by\s*\n?\s*sorry',
        text
    ):
        doc = m.group(1)
        name = m.group(2)
        body = m.group(3)
        # Prefer the "erdos_N" main theorem
        if re.match(r'erdos_?' + pid + r'\b', name):
            main_doc = doc
            open_thm = (name, body)
            break
    if not open_thm:
        # fallback to first research open theorem
        m = re.search(
            r'/--\s*([\s\S]*?)-/\s*@\[category research open[^\]]*\]\s*theorem\s+([\w.]+)([\s\S]*?):=\s*by\s*\n?\s*sorry',
            text
        )
        if m:
            main_doc = m.group(1)
            open_thm = (m.group(2), m.group(3))

    # If still no open theorem, check for solved-only
    if not open_thm:
        return None

    name, body = open_thm
    # ---- Compose full text we analyze
    relevant = (main_doc or '') + ' ' + body

    # ---- D2 quantifier_geometry
    has_inf_density = bool(re.search(r'(upperDensity|lowerDensity|HasDensity|positive.*density)', body))
    has_irrational = 'Irrational' in body
    has_summable = 'Summable' in body or 'tsum' in body or "∑'" in body
    has_atTop = 'atTop' in body or 'Tendsto' in body
    has_setinfinite = '.Infinite' in body or 'Set.Infinite' in body
    has_log = bool(re.search(r'\blog\b', body)) or 'Real.log' in body
    has_real = ' ℝ' in body or ' Real' in body or '∀ ε' in body
    has_complex = 'ℂ' in body or ' Complex' in body
    has_for_all_set = bool(re.search(r'∀.*Set\s', body))
    has_for_all_fn = bool(re.search(r'∀\s*\w+\s*:\s*ℕ\s*→', body))
    has_for_all_graph = bool(re.search(r'∀.*SimpleGraph', body)) or 'SimpleGraph' in body
    has_for_all_finite_n = bool(re.search(r'(∀|∀ᵉ)\s*[Nn]\s*[≤<]', body)) or bool(re.search(r'Finset\.range\s+\d+', body))
    has_bounded_const = bool(re.search(r'\b\d{2,}\b.*native_decide', body))
    has_existential_witness = re.search(r'∃\s*[a-zA-Z]\w*\s*[,:]\s*[\w\(\)\.\s]*Prime', body) is not None
    has_setinf_ex = bool(re.search(r'\.Infinite\b', body)) and '∃' in body

    # ---- Determine quantifier geometry
    if has_for_all_finite_n and re.search(r'∀.*≤\s*\d+', body):
        q_geom = 'bounded-finite'
    elif has_for_all_graph or has_for_all_set or has_for_all_fn or 'Filter.atTop' in body:
        if has_irrational or has_summable or has_inf_density or has_atTop:
            q_geom = 'full-structural'
        else:
            q_geom = 'full-structural'
    elif has_setinfinite or has_inf_density or has_irrational or has_summable:
        q_geom = 'full-structural'
    elif re.search(r'∀\s*p\s*:\s*ℕ.*Prime', body) or 'p.Prime' in body and '∀' in body:
        q_geom = 'infinite-parametric'
    elif '∃' in body and ('∀' in body or 'Infinite' in body):
        q_geom = 'finite-reducible-infinite'
    elif '∃' in body and '∀' not in body:
        q_geom = 'fixed-finite-object' if 'Finset' in body else 'finite-reducible-infinite'
    elif '∀' in body:
        q_geom = 'infinite-parametric' if 'Prime' in body else 'full-structural'
    else:
        q_geom = 'full-structural'

    # ---- D3 certificate_shape
    if has_irrational or has_summable or has_inf_density:
        cert = 'none-known'  # F1 risk
    elif has_setinfinite and '∃' in body and ('Prime' in body or 'covering' in body.lower()):
        if 'covering' in str(main_doc).lower() or 'Cover' in body or 'covering' in body.lower():
            cert = 'greedy-CRT'
        else:
            cert = 'pure-existence'
    elif '∃' in body and not has_inf_density:
        if 'Prime' in body or 'Finset' in body:
            cert = 'explicit-witness'
        else:
            cert = 'pure-existence'
    elif has_setinfinite:
        cert = 'pure-existence'
    elif has_for_all_graph:
        cert = 'universal-negative'
    elif has_atTop or has_setinf_ex:
        cert = 'pure-existence'
    elif '↔ False' in body:
        cert = 'explicit-witness'  # counterexample sought
    elif 'Tendsto' in body:
        cert = 'none-known'
    else:
        cert = 'none-known'

    # ---- D1 feasibility_category
    if q_geom == 'bounded-finite':
        feasibility = 'finite-verification'
    elif cert == 'explicit-witness' and q_geom in ('fixed-finite-object', 'finite-reducible-infinite'):
        feasibility = 'constructive-search'
    elif cert == 'greedy-CRT':
        feasibility = 'constructive-search'
    elif has_irrational or has_summable or has_inf_density:
        feasibility = 'structural-open'
    elif q_geom == 'full-structural':
        feasibility = 'structural-open'
    elif cert == 'none-known':
        feasibility = 'structural-open'
    else:
        feasibility = 'structural-open'

    # ---- Sanity flags
    has_large_card = bool(re.search(r'(ℵ_|Cardinal|Ordinal|ℵ₀|ℵ₁|ℵ_)', body)) or 'universe u' in text or 'Type u' in body
    has_full_graph_quant = bool(re.search(r'∀\s*[\(\{]?\s*[VG]\s*:\s*Type', body))  # ∀ V : Type
    has_hat_r = 'sizeRamsey' in body or 'hypergraphRamsey' in body
    has_chromatic = 'chromaticNumber' in body or 'chromaticCardinal' in body
    # Real-valued constants c > 0 in conjecture
    has_real_constant = bool(re.search(r'∃\s*c\s*>\s*\(?\s*0\s*:\s*ℝ', body))
    has_C_constant = bool(re.search(r'∃\s*C\s*>\s*\(?\s*0\s*:\s*ℝ', body))
    has_const_universal = has_real_constant or has_C_constant  # asymptotic constants
    # binomial, factorial, infinite sum, log -- analytic
    has_analytic_nt = bool(re.search(r'\b(centralBinom|tsum|cofinite|nhds|Tendsto|atTop|loglog|logb)\b', body))
    # set-theoretic: density, Set.Infinite, log
    has_set_density = ('upperDensity' in body or 'lowerDensity' in body or
                        'HasDensity' in body or '.Infinite' in body or
                        'Filter.cofinite' in body)
    # Witness is concrete (a number, e.g., `∃ k, ...` where k is ℕ AND body has decidable predicate)
    has_concrete_existential = ('∃ k' in body or '∃ n' in body or '∃ m' in body) and not has_const_universal

    # Universal-quantifier-over-rich-type detector
    has_univ_Q = bool(re.search(r'∀\s*\(?\s*q\s*:\s*ℚ', body))
    has_univ_set = bool(re.search(r'∀\s*\(?\s*A\s*:\s*Set', body))
    has_univ_R = bool(re.search(r'∀\s*\(?\s*ε\s*>', body)) or bool(re.search(r'∀\s*\(?\s*x\s*:\s*ℝ', body))
    has_univ_type = bool(re.search(r'∀\s*\(?\s*[Vv]\s*:\s*Type', body))
    has_set_finite = '.Finite' in body or 'Set.Finite' in body

    # ---- D4 snipe signature match
    snipe_sig = 'none'
    if q_geom == 'bounded-finite' and not has_irrational and not has_summable and not has_set_density:
        snipe_sig = 'S1-decide'
    elif ('SimpleGraph' in body and '∃' in body
          and not has_large_card
          and not has_full_graph_quant
          and not has_hat_r
          and not has_chromatic
          and not has_real_constant
          and not has_analytic_nt):
        # Only match S6 if it's bounded finite combinatorics, NOT infinite Ramsey theory
        snipe_sig = 'S6-graph-cex'
    elif cert == 'greedy-CRT':
        snipe_sig = 'S4-greedy-CRT'
    elif (cert == 'explicit-witness'
          and has_concrete_existential
          and not has_large_card
          and not has_const_universal
          and not has_setinfinite
          and not has_set_finite
          and not has_analytic_nt
          and not has_set_density
          and not has_univ_Q
          and not has_univ_set
          and not has_univ_R
          and not has_univ_type
          and 'Set.univ' not in body  # equality with Set.univ = density-style claim
          and 'Set.range' not in body
          and 'cardinal' not in body.lower()
          ):
        snipe_sig = 'S7-algebraic-witness'
    elif '∃ᵉ' in body and ('Fermat' in str(main_doc) or 'mod' in body):
        snipe_sig = 'S3-residue-fermat'
    elif cert == 'small-table' or (has_for_all_finite_n and 'σ' in body):
        snipe_sig = 'S2-table-bridge'

    # ---- D5 failure mode risk
    f_risk = 'low'
    if has_irrational or has_summable or has_inf_density:
        f_risk = 'F1-iff-rfl'
    elif has_atTop and not has_for_all_finite_n:
        f_risk = 'F1-iff-rfl'
    elif q_geom == 'full-structural' and cert == 'none-known':
        f_risk = 'F3-side-lemma-bloat'
    elif 'Pell' in str(main_doc) or 'sieve' in str(main_doc):
        f_risk = 'F3-side-lemma-bloat'
    elif has_setinfinite and cert == 'pure-existence':
        f_risk = 'F3-side-lemma-bloat'
    elif q_geom == 'infinite-parametric' and not has_for_all_finite_n:
        f_risk = 'F1-iff-rfl' if (has_irrational or has_summable) else 'F3-side-lemma-bloat'

    # ---- D6 negative_evidence
    att = attempts.get(pid, None)
    if att is None:
        neg_ev = 'untouched'
    elif att['total'] >= 10:
        neg_ev = 'project-carcass'
    elif att['total'] >= 6:
        neg_ev = 'attempted-high'
    elif att['total'] >= 3:
        neg_ev = 'attempted-medium'
    else:
        neg_ev = 'attempted-low'
    if att and att['adv'] > 0:
        neg_ev = 'attempted-medium'  # but with an advance, lower priority to label
    if att and att['dis'] > 0 and att['adv'] == 0:
        # disproven on a variant — still actionable
        pass

    # ---- Domain (AMS)
    ams_match = re.search(r'AMS\s+([0-9 ]+)', text)
    ams = ams_match.group(1).strip() if ams_match else ''
    if '05' in ams or '5' == ams.strip():
        domain = 'combinatorics'
    elif '11' in ams:
        domain = 'nt'
    elif '52' in ams:
        domain = 'geometry'
    elif '03' in ams or '3' == ams.strip():
        domain = 'logic'
    elif '30' in ams:
        domain = 'analysis'
    else:
        domain = 'unknown'

    # ---- Snipe score
    score = 5
    if snipe_sig in ('S1-decide', 'S6-graph-cex'):
        score += 4
    elif snipe_sig in ('S2-table-bridge', 'S3-residue-fermat', 'S5-case-split'):
        score += 3
    elif snipe_sig in ('S4-greedy-CRT', 'S7-algebraic-witness'):
        score += 2
    if q_geom == 'full-structural' and cert == 'none-known':
        score -= 4
    if f_risk == 'F1-iff-rfl':
        score -= 3
    if f_risk == 'F3-side-lemma-bloat':
        score -= 3
    if neg_ev == 'attempted-high':
        score -= 2
    if neg_ev == 'project-carcass':
        score -= 5

    # Mathlib-native bonus
    mathlib_native = bool(re.search(r'\b(Nat\.Prime|σ|totient|factorial|gcd|divisors|primeFactors|Coprime|Finset\.range|Finset\.Icc|Nat\.minFac|ZMod)\b', body))
    if mathlib_native:
        score += 1

    # Theory heavy penalty - expanded to include infinite Ramsey, cardinals, ordinals,
    # advanced analytic NT, hypergraph Ramsey, real-valued constants in structural conjectures,
    # measure theory, large cardinals
    theory_heavy = bool(re.search(
        r'\b(hypergraphRamsey|Ordinal|ℵ_|Cardinal|chromaticCardinal|Hausdorff|EllipticCurve|MeasureTheory|ENNReal|hadamard|jacobianDet|liouville|sizeRamsey|Ramsey|chromaticNumber|indepNum|cliqueNum|girth|coloring|hypergraph|centralBinom|cofinite|tsum)\b',
        body))
    if has_large_card or has_full_graph_quant or has_analytic_nt:
        theory_heavy = True
    if theory_heavy:
        score -= 2

    # Disproven once → counterexample known; still actionable but lower priority
    if att and att['dis'] > 0:
        score = max(score, 6)  # at least 6, since gap-resolution proof exists somewhere

    score = max(1, min(10, score))

    # ---- Recommended next action
    if att and att['total'] >= 6 and att['adv'] == 0:
        action = 'ALREADY_TRIED_RECENT'
    elif att and att['total'] >= 10 and att['adv'] == 0:
        action = 'ALREADY_TRIED_RECENT'
    elif feasibility == 'structural-open' and f_risk in ('F1-iff-rfl', 'F3-side-lemma-bloat') and (att is None or att['adv'] == 0):
        # avoid theory-heavy structural with no fresh diagnostic
        if theory_heavy:
            action = 'AVOID'
        elif score <= 3:
            action = 'AVOID'
        elif score >= 5 and neg_ev in ('untouched', 'attempted-low'):
            action = 'RESEARCH_REQUIRED'
        else:
            action = 'RESEARCH_REQUIRED'
    elif score >= 7 and neg_ev in ('untouched', 'attempted-low'):
        action = 'SUBMIT_NOW'
    elif score >= 5 and feasibility in ('finite-verification', 'constructive-search'):
        action = 'DRAFT_FIRST'
    elif score <= 3:
        action = 'AVOID'
    elif neg_ev in ('attempted-high', 'attempted-medium'):
        action = 'RESEARCH_REQUIRED'
    else:
        action = 'RESEARCH_REQUIRED'

    return {
        'problem_id': f'erdos_{pid}',
        'file_path': f'formal-conjectures/FormalConjectures/ErdosProblems/{pid}.lean',
        'theorem_name': name,
        'domain': domain,
        'feasibility': feasibility,
        'quantifier_geom': q_geom,
        'certificate_shape': cert,
        'snipe_signature': snipe_sig,
        'failure_risk': f_risk,
        'negative_evidence': neg_ev,
        'attempts_total': att['total'] if att else 0,
        'attempts_no_adv': att['no_adv'] if att else 0,
        'attempts_disproven': att['dis'] if att else 0,
        'mathlib_native': 'yes' if mathlib_native else 'no',
        'theory_heavy': 'yes' if theory_heavy else 'no',
        'snipe_score_1_to_10': score,
        'recommended_next_action': action,
    }

# ----------------------------------------------------------------------------
# Run over all files
# ----------------------------------------------------------------------------
all_rows = []
skipped = []
for fname in sorted(os.listdir(DIR), key=lambda x: int(x.replace('.lean', ''))):
    if not fname.endswith('.lean'):
        continue
    pid = fname.replace('.lean', '')
    with open(DIR / fname) as fp:
        text = fp.read()
    row = classify(pid, text)
    if row:
        all_rows.append(row)
    else:
        # solved-only file (or undergraduate / test only) — note as known-formalization
        ams_match = re.search(r'AMS\s+([0-9 ]+)', text)
        ams = ams_match.group(1).strip() if ams_match else ''
        if '05' in ams or '5' == ams.strip():
            domain = 'combinatorics'
        elif '11' in ams:
            domain = 'nt'
        elif '52' in ams:
            domain = 'geometry'
        elif '30' in ams:
            domain = 'analysis'
        else:
            domain = 'unknown'
        att = attempts.get(pid)
        all_rows.append({
            'problem_id': f'erdos_{pid}',
            'file_path': f'formal-conjectures/FormalConjectures/ErdosProblems/{pid}.lean',
            'theorem_name': '(no research open theorem)',
            'domain': domain,
            'feasibility': 'known-formalization',
            'quantifier_geom': 'n/a',
            'certificate_shape': 'n/a',
            'snipe_signature': 'none',
            'failure_risk': 'low',
            'negative_evidence': 'untouched' if not att else 'attempted-low',
            'attempts_total': att['total'] if att else 0,
            'attempts_no_adv': att['no_adv'] if att else 0,
            'attempts_disproven': att['dis'] if att else 0,
            'mathlib_native': 'n/a',
            'theory_heavy': 'n/a',
            'snipe_score_1_to_10': 1,
            'recommended_next_action': 'AVOID',  # per rubric, known-formalization excluded
        })
        skipped.append(pid)

# Write CSV
fields = [
    'problem_id', 'file_path', 'theorem_name', 'domain',
    'feasibility', 'quantifier_geom', 'certificate_shape',
    'snipe_signature', 'failure_risk', 'negative_evidence',
    'attempts_total', 'attempts_no_adv', 'attempts_disproven',
    'mathlib_native', 'theory_heavy',
    'snipe_score_1_to_10', 'recommended_next_action'
]
with open(OUT, 'w', newline='') as fp:
    w = csv.DictWriter(fp, fieldnames=fields)
    w.writeheader()
    for r in all_rows:
        w.writerow(r)

print(f"Wrote {len(all_rows)} rows to {OUT}")
print(f"Skipped (no open theorem): {len(skipped)}")

# Distribution
from collections import Counter
print("\nAction distribution:")
for k, v in Counter(r['recommended_next_action'] for r in all_rows).most_common():
    print(f"  {k}: {v}")

print("\nSnipe-score distribution:")
for k, v in sorted(Counter(r['snipe_score_1_to_10'] for r in all_rows).items()):
    print(f"  score={k}: {v}")

print("\nTop 15 by snipe_score (untouched):")
top = sorted([r for r in all_rows if r['negative_evidence'] == 'untouched'],
              key=lambda r: (-r['snipe_score_1_to_10']))
for r in top[:15]:
    print(f"  {r['problem_id']:>15s} score={r['snipe_score_1_to_10']} {r['snipe_signature']:25s} {r['certificate_shape']:25s} {r['recommended_next_action']}")
