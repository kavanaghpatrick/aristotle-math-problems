#!/usr/bin/env python3
"""Re-label every Erdős problem in formal-conjectures against the closure-potential
taxonomy (CS/CM/CR/HM), starting from the snipe labels in erdos_labeled_may30.csv.

Inputs:
  - analysis/erdos_labeled_may30.csv (prior snipe labels, STARTING POINT)
  - analysis/open_problems_registry_may30.csv (statement first-lines)
  - docs/closure_taxonomy_may30.md (the new taxonomy)
  - formal-conjectures/FormalConjectures/ErdosProblems/*.lean (source)

Output:
  - analysis/erdos_closure_labeled.csv

Closure axes (per docs/closure_taxonomy_may30.md):
  CS (Closure Scope): full_closure / direction_closure / disproof_closure /
                       bounded_version_closure / sub_claim_closure / formalization_only
  CM (Closure Mechanism): explicit_witness / bounded_to_infinite_lift /
                            structural_finite_reduction / disproof_construction /
                            witness_table_chunked / density_sieve_closure /
                            induction_template / none_known
  CR (Closure Risk): clean_decidable / partial_result_only / iff_rfl_trap /
                       witness_search_explosion / definition_mismatch /
                       em_tautology / infrastructure_overgrowth / recursive_falsification
  HM (Honesty Marker): journal_clean / journal_partial / journal_subclaim /
                         infrastructure_only

closure_score formula (per agent #8 instructions):
  Start with 5 (no agent #7 closure_feasibility available)
  +2 if CS == full_closure or direction_closure
  +1 if CS == disproof_closure
  -3 if CS == formalization_only
  -2 if HM == infrastructure_only
  -2 if CR in {iff_rfl_trap, definition_mismatch}
  Clamp to [1, 10]

Action:
  CLOSURE_CANDIDATE  (score >= 7)
  CLOSURE_PROBE      (score 5-6)
  BOUNDED_ONLY       (score 3-4)
  AVOID              (score <= 2 or formalization_only)
"""
import os
import re
import csv
import sqlite3
from pathlib import Path
from collections import Counter

ROOT = Path('/Users/patrickkavanagh/math')
DIR = ROOT / 'formal-conjectures/FormalConjectures/ErdosProblems'
DB = ROOT / 'submissions/tracking.db'
PRIOR_CSV = ROOT / 'analysis/erdos_labeled_may30.csv'
REGISTRY_CSV = ROOT / 'analysis/open_problems_registry_may30.csv'
OUT_CSV = ROOT / 'analysis/erdos_closure_labeled.csv'


# ----------------------------------------------------------------------------
# Load prior snipe labels
# ----------------------------------------------------------------------------
def load_prior_labels():
    with open(PRIOR_CSV) as f:
        return {r['problem_id']: r for r in csv.DictReader(f)}


# ----------------------------------------------------------------------------
# Load registry — multiple statements per file
# ----------------------------------------------------------------------------
def load_registry():
    # problem_id -> list of (theorem_name, statement_first_line)
    by_pid = {}
    with open(REGISTRY_CSV) as f:
        for r in csv.DictReader(f):
            if '/ErdosProblems/' not in r['file_path']:
                continue
            pid = r['problem_id']
            by_pid.setdefault(pid, []).append({
                'theorem_name': r['theorem_name'],
                'statement': r['statement_first_line'],
                'prior_attempts': int(r.get('prior_attempts_count') or 0),
                'year': r.get('year_stated') or '',
            })
    return by_pid


# ----------------------------------------------------------------------------
# DB attempt history (per-erdos with status counts)
# ----------------------------------------------------------------------------
def load_attempts():
    conn = sqlite3.connect(str(DB))
    cur = conn.cursor()
    attempts = {}
    for pid, status, cnt in cur.execute("""
        SELECT problem_id, status, COUNT(*)
        FROM submissions
        WHERE problem_id IS NOT NULL
        GROUP BY problem_id, status
    """):
        m = re.match(r'(?:erdos|Erdos)_?(\d+)', pid or '', re.IGNORECASE)
        if not m:
            continue
        num = m.group(1)
        d = attempts.setdefault(num, {'total': 0, 'adv': 0, 'dis': 0,
                                       'no_adv': 0, 'failed': 0, 'sub': 0})
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
    return attempts


# ----------------------------------------------------------------------------
# Heuristic signals from raw Lean text
# ----------------------------------------------------------------------------
PATTERN_IRRATIONAL = re.compile(r'\bIrrational\b')
PATTERN_SUMMABLE = re.compile(r'\bSummable\b|\btsum\b')
PATTERN_DENSITY = re.compile(r'\b(upperDensity|lowerDensity|HasDensity|HasPosDensity|hasDensity)\b')
PATTERN_INFINITE_SET = re.compile(r'\.Infinite\b|Set\.Infinite\b')
PATTERN_FINITE_SET = re.compile(r'\.Finite\b|Set\.Finite\b')
PATTERN_TENDSTO = re.compile(r'\bTendsto\b|atTop')
PATTERN_LIMSUP = re.compile(r'\b(limsup|liminf)\b')
PATTERN_IS_LITTLE_O = re.compile(r'=o\[|=O\[|=Θ\[')
PATTERN_FREE_FN = re.compile(r'∀\s*\w+\s*:\s*ℕ\s*→')
PATTERN_FREE_GRAPH = re.compile(r'∀.*SimpleGraph')
PATTERN_FREE_SET_NAT = re.compile(r'∀\s*\(?\s*[A-Z]\s*:\s*Set\s+ℕ')
PATTERN_RAMSEY = re.compile(r'\b(Ramsey|sizeRamsey|hypergraphRamsey)\b')
PATTERN_CARDINAL = re.compile(r'\b(Cardinal|Ordinal|ℵ_|ℵ₀|ℵ₁|chromaticCardinal)\b')
PATTERN_FINSET_RANGE = re.compile(r'\bFinset\.(range|Icc|Ioc|Ioo|Ico)\s+\d+')
PATTERN_FINITE_LE = re.compile(r'(∀|∀ᵉ)\s*\(?\s*\w+\s*(?:≥|>)\s*\(?\s*\(?\s*\d+\s*\)?\s*\)?\s*[,)]')
PATTERN_AMS = re.compile(r'AMS\s+([0-9 ]+)')
PATTERN_ERDOS_HEADER = re.compile(r'# Erd[oő]s Problem\s+(\d+)')
PATTERN_THM_OPEN = re.compile(
    r'/--\s*([\s\S]*?)-/\s*@\[category research open[^\]]*\]\s*theorem\s+([\w.]+)([\s\S]*?):=\s*by\s*\n?\s*sorry'
)
PATTERN_THM_SOLVED = re.compile(
    r'@\[category research solved[^\]]*\]\s*theorem\s+([\w.]+)'
)
PATTERN_DISPROVED = re.compile(
    r'@\[category research (?:disproved|refuted|counterexample)[^\]]*\]'
)
PATTERN_PUBLISHED = re.compile(
    r'(Hough\b|Helfgott\b|Heath-?Brown\b|Granville\b|Tao\b|Soundararajan\b|Maynard\b|Ferreira\b|Konyagin\b|Banks\b|Pintz\b|Iwaniec\b|de la Bret[eè]che\b)'
)
PATTERN_KNOWN_FOR_SMALL = re.compile(
    r'(verified for all (?:n|N) ≤|verified up to|all known|conjectured|computer|computational|by computer)'
)
PATTERN_OEIS = re.compile(r'OEIS[:/-]?\s*A\d+', re.IGNORECASE)
PATTERN_ANS_SORRY = re.compile(r'answer\s*\(\s*sorry\s*\)')


def parse_file(text: str):
    """Extract all open theorems and the file's docstring."""
    # All research open theorems
    open_thms = []
    for m in PATTERN_THM_OPEN.finditer(text):
        doc = m.group(1)
        name = m.group(2)
        body = m.group(3)
        open_thms.append({'docstring': doc, 'name': name, 'body': body})
    has_solved = bool(PATTERN_THM_SOLVED.search(text))
    has_disproved_thm = bool(PATTERN_DISPROVED.search(text))
    return {
        'open_thms': open_thms,
        'has_solved': has_solved,
        'has_disproved_thm': has_disproved_thm,
        'full_text': text,
    }


# ----------------------------------------------------------------------------
# Classify CS/CM/CR/HM
# ----------------------------------------------------------------------------
def classify_closure(pid: str, prior: dict, parsed: dict, attempts: dict, registry_rows: list):
    """Return CS, CM, CR (primary), HM, closure_score, action, justification."""
    body_blocks = [t['body'] for t in parsed['open_thms']]
    docs = [t['docstring'] for t in parsed['open_thms']]
    full = parsed['full_text']
    body = ' '.join(body_blocks)
    doc = ' '.join(docs)

    feasibility = prior.get('feasibility', 'structural-open')
    cert = prior.get('certificate_shape', 'none-known')
    quant = prior.get('quantifier_geom', 'full-structural')
    snipe_sig = prior.get('snipe_signature', 'none')
    failure_risk = prior.get('failure_risk', 'low')
    snipe_score = int(prior.get('snipe_score_1_to_10', 5) or 5)
    prior_action = prior.get('recommended_next_action', 'AVOID')
    neg_ev = prior.get('negative_evidence', 'untouched')
    domain = prior.get('domain', 'unknown')
    theory_heavy = prior.get('theory_heavy', 'no') == 'yes'
    mathlib_native = prior.get('mathlib_native', 'no') == 'yes'

    # Signals
    has_irrational = bool(PATTERN_IRRATIONAL.search(body)) or 'Irrational' in doc
    has_summable = bool(PATTERN_SUMMABLE.search(body))
    has_density = bool(PATTERN_DENSITY.search(body)) or 'density' in doc.lower()
    has_inf_set = bool(PATTERN_INFINITE_SET.search(body))
    has_fin_set = bool(PATTERN_FINITE_SET.search(body))
    has_tendsto = bool(PATTERN_TENDSTO.search(body))
    has_limsup = bool(PATTERN_LIMSUP.search(body))
    has_asym = bool(PATTERN_IS_LITTLE_O.search(body))
    has_free_fn = bool(PATTERN_FREE_FN.search(body))
    has_free_set = bool(PATTERN_FREE_SET_NAT.search(body))
    has_free_graph = bool(PATTERN_FREE_GRAPH.search(body))
    has_ramsey = bool(PATTERN_RAMSEY.search(body))
    has_cardinal = bool(PATTERN_CARDINAL.search(body)) or bool(PATTERN_CARDINAL.search(full))
    has_bounded = bool(PATTERN_FINSET_RANGE.search(body)) or bool(PATTERN_FINITE_LE.search(body))
    has_ans_sorry = bool(PATTERN_ANS_SORRY.search(body)) or bool(PATTERN_ANS_SORRY.search(full))
    has_disproved_thm = parsed['has_disproved_thm']
    has_published_attrib = bool(PATTERN_PUBLISHED.search(doc)) or bool(PATTERN_PUBLISHED.search(full))
    has_oeis = bool(PATTERN_OEIS.search(doc)) or bool(PATTERN_OEIS.search(full))
    has_for_all_eps = bool(re.search(r'∀\s*\(?ε\s*[>:]', body))
    has_for_all_q = bool(re.search(r'∀\s*\(?\s*q\s*:\s*ℚ', body))

    # ---- CS classification
    # Default
    cs = 'sub_claim_closure'

    # Detect: is the conjecture genuinely bounded in source, or does the source have
    # an unbounded outer quantifier that Aristotle can only do bounded versions of?
    # ∀ n ≥ 1 / ∀ n, ... = unbounded universal; closure requires witness function
    # ∃ m, ∀ k l, ... = unbounded inside ∃ scope; closure requires a single witness
    # ∀ n ≤ N (concrete N) = bounded universal; closure_clean if decidable
    has_unbounded_forall_nat = bool(re.search(r'∀\s*\(?\s*\w+\s*≥\s*\(?\s*\d+\s*\)?\s*,', body)) or bool(re.search(r'∀\s*\(?\s*\w+\s*:\s*ℕ', body)) or bool(re.search(r'∀\s*\(?\s*\w+\s*[,:]\s*[^≤<\d]+,', body))
    has_concrete_bound = bool(re.search(r'(?:≤|<)\s*\d{1,12}', body)) and not has_unbounded_forall_nat
    has_exists_outer = bool(re.search(r'^\s*∃\s*\w', body.strip()[:50])) or re.match(r'\s*∃', body.strip())
    has_finset_icc = bool(PATTERN_FINSET_RANGE.search(body))

    if feasibility == 'known-formalization':
        cs = 'formalization_only'
    elif has_disproved_thm or (attempts.get(pid, {}).get('dis', 0) > 0):
        # Already disproven once on this problem
        cs = 'disproof_closure'
    elif has_published_attrib and re.search(r'(proved|proven|theorem of|verified by|due to|by [A-Z][a-z]+)', doc.lower()):
        # Already proved in literature (Hough, Helfgott, etc.) -> formalization only
        cs = 'formalization_only'
    elif has_irrational or has_summable or has_density or has_inf_set or has_tendsto or has_limsup or has_asym:
        # Structural infinite predicate, F1 risk: bounded version is the realistic target
        cs = 'bounded_version_closure'
    elif has_free_graph or has_free_set or has_cardinal or has_ramsey:
        # Highly structural over rich types -> sub_claim only
        cs = 'sub_claim_closure'
    elif has_free_fn:
        # ∀ function-from-ℕ-to-ℕ -> structural full
        cs = 'sub_claim_closure'
    elif cert == 'greedy-CRT':
        # Covering-system construction. Source is `∃ m, ∀ k l, ¬Prime(...)`,
        # outer ∃ followed by inner ∀. If a single witness m exists, that's full_closure.
        cs = 'full_closure'
    elif quant == 'bounded-finite' and cert in ('explicit-witness', 'small-table'):
        # Bounded universal with explicit witness — could be full closure if statement IS bounded
        # If the statement has a concrete bound, full closure; else it's bounded version of unbounded conjecture
        cs = 'full_closure' if has_concrete_bound else 'bounded_version_closure'
    elif quant == 'fixed-finite-object' and cert == 'explicit-witness':
        cs = 'full_closure'
    elif feasibility == 'finite-verification' and cert in ('explicit-witness', 'small-table'):
        # Finite-verification by definition is a bounded check — full closure only if conjecture IS bounded
        cs = 'full_closure' if has_concrete_bound else 'bounded_version_closure'
    elif cert == 'explicit-witness' and feasibility == 'constructive-search':
        # Construction target. If outer is ∃ ... (one witness closes), full_closure.
        # If outer is ∀ n, ∃ k ... (witness function over infinite n), bounded version is realistic.
        if has_unbounded_forall_nat:
            cs = 'bounded_version_closure'
        else:
            cs = 'full_closure'
    elif quant == 'finite-reducible-infinite':
        # ∃ over an infinite domain that reduces to bounded if you find the witness
        cs = 'bounded_version_closure'
    elif quant == 'full-structural' and cert == 'none-known':
        cs = 'sub_claim_closure'
    elif quant == 'infinite-parametric':
        cs = 'bounded_version_closure'

    # Boost: if the conjecture is itself an iff with answer(sorry), then *closing the iff*
    # would be a full_closure but with high iff_rfl_trap risk
    has_ans_iff_full = has_ans_sorry and '↔' in body

    # ---- CM classification
    cm = 'none_known'
    if cs == 'formalization_only':
        cm = 'explicit_witness' if quant in ('bounded-finite', 'fixed-finite-object') else 'none_known'
    elif cs == 'disproof_closure':
        cm = 'disproof_construction'
    elif snipe_sig == 'S1-decide' or quant == 'bounded-finite':
        cm = 'explicit_witness'
    elif snipe_sig == 'S2-table-bridge':
        cm = 'witness_table_chunked'
    elif snipe_sig == 'S3-residue-fermat':
        cm = 'structural_finite_reduction'
    elif snipe_sig == 'S4-greedy-CRT' or cert == 'greedy-CRT':
        cm = 'structural_finite_reduction' if 'covering' in doc.lower() else 'explicit_witness'
    elif snipe_sig == 'S5-case-split':
        cm = 'structural_finite_reduction'
    elif snipe_sig == 'S6-graph-cex':
        cm = 'disproof_construction'
    elif snipe_sig == 'S7-algebraic-witness':
        cm = 'explicit_witness'
    elif has_density or has_summable or has_inf_set:
        cm = 'density_sieve_closure'
    elif has_tendsto or has_limsup or has_asym:
        cm = 'density_sieve_closure'
    elif cert == 'explicit-witness' and feasibility == 'constructive-search':
        cm = 'explicit_witness'
    elif quant == 'finite-reducible-infinite' and cert in ('explicit-witness', 'small-table'):
        cm = 'bounded_to_infinite_lift'
    elif feasibility == 'structural-open' and cert == 'none-known':
        cm = 'none_known'

    # Aristotle has NEVER closed via density_sieve or induction_template -- demote those to "none_known"
    # if classified naively
    if cm == 'density_sieve_closure':
        # No precedent -> still call it density_sieve_closure but it implies infrastructure_only.
        pass

    # ---- CR primary risk
    cr = 'clean_decidable'
    # Identify the dominant fail mode
    if has_irrational or has_summable or has_density or has_tendsto or has_limsup or has_asym:
        cr = 'iff_rfl_trap'
    elif has_inf_set or has_fin_set:
        # Set.Infinite / Set.Finite — F1 risk if RHS is undecidable
        cr = 'iff_rfl_trap'
    elif has_free_graph or has_free_set or has_cardinal or has_ramsey:
        cr = 'infrastructure_overgrowth'
    elif has_free_fn:
        cr = 'infrastructure_overgrowth'
    elif failure_risk == 'F1-iff-rfl':
        cr = 'iff_rfl_trap'
    elif failure_risk == 'F3-side-lemma-bloat':
        cr = 'infrastructure_overgrowth'
    elif cm == 'witness_table_chunked' and quant in ('bounded-finite', 'finite-reducible-infinite'):
        cr = 'witness_search_explosion'
    elif quant in ('bounded-finite', 'fixed-finite-object') and cm in ('explicit_witness', 'witness_table_chunked', 'structural_finite_reduction'):
        cr = 'clean_decidable'
    elif cs == 'bounded_version_closure':
        cr = 'partial_result_only'
    elif cs == 'sub_claim_closure' and cm == 'none_known':
        cr = 'infrastructure_overgrowth'

    # special: project-carcass implies recursive_falsification on tuza-style problems
    if neg_ev == 'project-carcass':
        cr = 'recursive_falsification'

    # ---- HM honesty marker
    if cs == 'formalization_only':
        hm = 'infrastructure_only'
    elif cm == 'none_known':
        # No closure mechanism -> any output is infrastructure
        hm = 'infrastructure_only'
    elif cm == 'density_sieve_closure':
        # Aristotle has NEVER closed via density/sieve; output will be infrastructure
        hm = 'infrastructure_only'
    elif cm == 'induction_template':
        # No precedent; output will be infrastructure
        hm = 'infrastructure_only'
    elif cs in ('full_closure', 'direction_closure', 'disproof_closure'):
        hm = 'journal_clean'
    elif cs == 'sub_claim_closure':
        hm = 'journal_subclaim'
    elif cs == 'bounded_version_closure':
        hm = 'journal_partial'
    else:
        hm = 'infrastructure_only'

    # ---- Closure score
    # Base: 5 (no agent #7 closure_feasibility available)
    score = 5
    if cs in ('full_closure', 'direction_closure'):
        score += 2
    if cs == 'disproof_closure':
        score += 1
    if cs == 'formalization_only':
        score -= 3
    if hm == 'infrastructure_only':
        score -= 2
    if cr in ('iff_rfl_trap', 'definition_mismatch'):
        score -= 2

    # Honor existing snipe insights as soft priors (small +/-)
    if snipe_score >= 8 and cs in ('full_closure', 'direction_closure', 'disproof_closure', 'sub_claim_closure'):
        score += 1
    if snipe_score <= 2:
        score -= 1
    if neg_ev == 'project-carcass':
        score -= 2
    if attempts.get(pid, {}).get('adv', 0) > 0:
        score += 1
    if theory_heavy:
        score -= 1

    score = max(1, min(10, score))

    # ---- Action
    if cs == 'formalization_only':
        action = 'AVOID'
    elif score >= 7:
        action = 'CLOSURE_CANDIDATE'
    elif score >= 5:
        action = 'CLOSURE_PROBE'
    elif score >= 3:
        action = 'BOUNDED_ONLY'
    else:
        action = 'AVOID'

    # ---- Justification (one sentence)
    if cs == 'formalization_only':
        just = "Already published; Lean port only — outside closure lane."
    elif cs == 'full_closure' and cm == 'explicit_witness':
        just = "Constructive existence with explicit witness — Aristotle can `decide` if witness fits the kernel."
    elif cs == 'full_closure' and cm == 'witness_table_chunked':
        just = "Bounded existence over a chunkable Finset — strongest S2 template."
    elif cs == 'full_closure' and cm == 'structural_finite_reduction':
        just = "Structural finite reduction via residue/Cunningham split — S3/S5 reusable."
    elif cs == 'disproof_closure':
        just = "Counterexample target — explicit graph/witness disproof construction template."
    elif cs == 'direction_closure':
        just = "Single iff direction; closing the open half is journal-clean."
    elif cs == 'bounded_version_closure':
        just = "Open conjecture has unbounded quantifier; only bounded slice is reachable — partial result."
    elif cs == 'sub_claim_closure' and cm == 'none_known':
        just = "Structural-open with no known closure mechanism — infrastructure-only outcome expected."
    elif cs == 'sub_claim_closure':
        just = "Strict sub-statement closable via " + cm.replace('_', ' ') + "; full conjecture stays open."
    else:
        just = f"{cs} via {cm}; CR={cr}."

    return {
        'CS': cs,
        'CM': cm,
        'CR': cr,
        'HM': hm,
        'closure_score': score,
        'closure_action': action,
        'closure_justification': just,
    }


# ----------------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------------
def main():
    prior_labels = load_prior_labels()
    registry = load_registry()
    attempts = load_attempts()

    rows = []
    for fname in sorted(os.listdir(DIR), key=lambda x: int(x.replace('.lean', '')) if x.replace('.lean', '').isdigit() else 999999):
        if not fname.endswith('.lean'):
            continue
        pid = fname.replace('.lean', '')
        problem_id = f'erdos_{pid}'

        with open(DIR / fname) as fp:
            text = fp.read()
        parsed = parse_file(text)

        prior = prior_labels.get(problem_id, {})
        reg_rows = registry.get(problem_id, [])

        closure = classify_closure(pid, prior, parsed, attempts, reg_rows)

        # Merge prior + closure
        row = dict(prior)  # all prior columns
        if not row:
            # missing in prior — derive minimal stub
            row = {
                'problem_id': problem_id,
                'file_path': f'formal-conjectures/FormalConjectures/ErdosProblems/{pid}.lean',
                'theorem_name': parsed['open_thms'][0]['name'] if parsed['open_thms'] else '(no research open theorem)',
                'domain': 'nt', 'feasibility': 'structural-open',
                'quantifier_geom': 'full-structural', 'certificate_shape': 'none-known',
                'snipe_signature': 'none', 'failure_risk': 'low',
                'negative_evidence': 'untouched',
                'attempts_total': '0', 'attempts_no_adv': '0', 'attempts_disproven': '0',
                'mathlib_native': 'no', 'theory_heavy': 'no',
                'snipe_score_1_to_10': '5', 'recommended_next_action': 'AVOID',
            }
        row.update(closure)
        rows.append(row)

    # Write
    fields = [
        'problem_id', 'file_path', 'theorem_name', 'domain',
        'feasibility', 'quantifier_geom', 'certificate_shape',
        'snipe_signature', 'failure_risk', 'negative_evidence',
        'attempts_total', 'attempts_no_adv', 'attempts_disproven',
        'mathlib_native', 'theory_heavy',
        'snipe_score_1_to_10', 'recommended_next_action',
        # New closure columns
        'CS', 'CM', 'CR', 'HM',
        'closure_score', 'closure_action', 'closure_justification',
    ]
    with open(OUT_CSV, 'w', newline='') as fp:
        w = csv.DictWriter(fp, fieldnames=fields)
        w.writeheader()
        for r in rows:
            w.writerow(r)

    print(f"Wrote {len(rows)} rows to {OUT_CSV}")

    # Distribution
    print("\nClosure action distribution:")
    for k, v in Counter(r['closure_action'] for r in rows).most_common():
        print(f"  {k:>22s}: {v}")

    print("\nCS distribution:")
    for k, v in Counter(r['CS'] for r in rows).most_common():
        print(f"  {k:>30s}: {v}")

    print("\nCM distribution:")
    for k, v in Counter(r['CM'] for r in rows).most_common():
        print(f"  {k:>30s}: {v}")

    print("\nCR distribution:")
    for k, v in Counter(r['CR'] for r in rows).most_common():
        print(f"  {k:>30s}: {v}")

    print("\nHM distribution:")
    for k, v in Counter(r['HM'] for r in rows).most_common():
        print(f"  {k:>30s}: {v}")

    print("\nclosure_score distribution:")
    for k, v in sorted(Counter(r['closure_score'] for r in rows).items()):
        print(f"  score={k}: {v}")

    # Top closure candidates
    print("\nTop 25 CLOSURE_CANDIDATE / CLOSURE_PROBE (sorted by closure_score):")
    cands = sorted(
        [r for r in rows if r['closure_action'] in ('CLOSURE_CANDIDATE', 'CLOSURE_PROBE')],
        key=lambda r: (-int(r['closure_score']), r['problem_id'])
    )
    for r in cands[:25]:
        print(f"  {r['problem_id']:>15s} score={r['closure_score']} CS={r['CS']:25s} CM={r['CM']:25s} act={r['closure_action']}")

    # Surprises
    print("\nMost surprising re-classifications (high snipe_score but low closure_score, or vice versa):")
    surprises = []
    for r in rows:
        ss = int(r['snipe_score_1_to_10'])
        cs_score = int(r['closure_score'])
        gap = abs(ss - cs_score)
        if gap >= 3:
            surprises.append((gap, ss, cs_score, r['problem_id'], r['CS'], r['CM'], r['HM']))
    surprises.sort(reverse=True, key=lambda x: x[0])
    for gap, ss, cs_score, pid, CS, CM, HM in surprises[:15]:
        direction = "snipe-high closure-low" if ss > cs_score else "snipe-low closure-high"
        print(f"  {pid:>15s}  snipe={ss}  closure={cs_score}  ({direction:>22s})  CS={CS:25s} CM={CM:25s} HM={HM}")


if __name__ == '__main__':
    main()
