#!/usr/bin/env python3
"""Agent #9: Re-label non-Erdős open problems by closure potential.

Inputs:
  - docs/closure_taxonomy_may30.md (authority)
  - analysis/non_erdos_labeled_may30.csv (prior agent #8/snipe labels)
  - formal-conjectures/FormalConjectures/{Wikipedia,GreensOpenProblems,Mathoverflow,
    OEIS,Paper,Arxiv,Other,WrittenOnTheWallII,Millenium,Books}/*.lean (source statements)

Output:
  analysis/non_erdos_closure_labeled.csv with closure columns appended:
    closure_scope (CS), closure_mechanism (CM), closure_risk (CR), honesty_marker (HM),
    closure_score (1-10), closure_action, closure_rationale.

Scoring formula (consistent with agent #8 expected):
  base = 5
  +3 if CS in {full_closure, disproof_closure}
  +2 if CS == direction_closure
  +1 if CS in {sub_claim_closure}
  +0 if CS == bounded_version_closure
  -2 if CS == formalization_only
  +3 if CM in {explicit_witness, disproof_construction, witness_table_chunked}
  +2 if CM == structural_finite_reduction
  +1 if CM == bounded_to_infinite_lift
  -3 if CM == none_known
  -2 if CM in {density_sieve_closure, induction_template}
  +2 if CR == clean_decidable
  +0 if CR == witness_search_explosion
  -1 if CR == partial_result_only
  -3 if CR in {iff_rfl_trap, em_tautology, definition_mismatch, infrastructure_overgrowth}
  -2 if CR == recursive_falsification
  +2 if HM == journal_clean
  +1 if HM in {journal_partial, journal_subclaim}
  -3 if HM == infrastructure_only
  clamp to [1,10]

Action:
  closure_score >= 8 AND HM in {journal_clean, journal_subclaim}  -> CLOSURE_CANDIDATE
  closure_score >= 6 AND HM in {journal_clean, journal_subclaim,
                                journal_partial}                   -> CLOSURE_PROBE
  closure_score >= 5 AND HM == journal_partial                     -> BOUNDED_ONLY
  otherwise                                                         -> AVOID
"""
import csv
import re
from pathlib import Path

ROOT = Path('/Users/patrickkavanagh/math')
PRIOR = ROOT / 'analysis/non_erdos_labeled_may30.csv'
SRC_BASE = ROOT / 'formal-conjectures/FormalConjectures'
OUT = ROOT / 'analysis/non_erdos_closure_labeled.csv'


def read_source(file_path: str) -> str:
    """Read the .lean source file. Return '' if missing."""
    p = Path(file_path)
    if not p.exists():
        return ''
    try:
        return p.read_text()
    except Exception:
        return ''


def find_target_theorem(text: str, theorem_name: str) -> str:
    """Extract the text of the named theorem (or '' if not found)."""
    pat = re.compile(
        r'@\[category research open[^\]]*\]\s*theorem\s+' + re.escape(theorem_name)
        + r'([\s\S]*?):=\s*by\s*\n?\s*sorry'
    )
    m = pat.search(text)
    if m:
        return m.group(1)
    # fallback: try without namespace prefix or with trailing dots
    short = theorem_name.split('.')[-1]
    pat2 = re.compile(
        r'@\[category research open[^\]]*\]\s*theorem\s+' + re.escape(short)
        + r'([\s\S]*?):=\s*by\s*\n?\s*sorry'
    )
    m2 = pat2.search(text)
    if m2:
        return m2.group(1)
    # fallback to first research open theorem
    pat3 = re.compile(
        r'@\[category research open[^\]]*\]\s*theorem\s+\S+([\s\S]*?):=\s*by\s*\n?\s*sorry'
    )
    m3 = pat3.search(text)
    return m3.group(1) if m3 else ''


# ---------------------------------------------------------------------------
# Heuristic detectors
# ---------------------------------------------------------------------------

# F1 iff_rfl_trap predicates: undecidable Mathlib wrappers
IFF_RFL_PREDICATES = [
    'Irrational', 'IsAlgebraic', 'Transcendental', 'isAlgebraic', 'isTranscendental',
    'Tendsto', 'IsEquivalent', 'Summable', 'tsum', 'Set.Infinite', '.Infinite',
    'Cardinal.', 'Ordinal.', 'Quotient', 'Liouville',
    'IsBigO', 'IsLittleO', '≪', 'isBigO', 'isLittleO',
    'upperDensity', 'lowerDensity', 'HasDensity',
    'volume', 'IsManifold', 'AlmostEverywhere', 'measurable', 'measureSpace',
    'IsOpen', 'IsClosed', 'IsConnected', 'IsConnectedMap',
    'Set.range', 'BddAbove', 'BddBelow', '⨆', '⨅',
]

# Heavy/theory_heavy predicates that suggest no clean closure mechanism
HEAVY_PREDICATES = [
    'EllipticCurve', 'L-function', 'lFunction', 'modularForm', 'rankOne', 'rankTwo',
    'Hadamard', 'Carleson', 'Hausdorff', 'Lebesgue', 'manifold', 'CW',
    'Galois', 'Schanuel', 'sizeRamsey', 'hypergraphRamsey', 'Ramsey',
    'chromatic', 'mandelbrot', 'multibrot', 'measureSpace', 'MeasureTheory',
    'Category', 'Functor', 'simplicial', 'sheaf',
    'gradient', 'derivative', 'integral', 'inscribedRectangle',
    'CauchyTransform', 'fourier', 'Fourier',
    'ZModFreeRank', 'EllipticCurveRank', 'BSDConjecture',
    'AffineSubspace', 'IsHomogeneous',
]

# Famous "complete-open" problems — known infrastructure_only
FAMOUS_INFRASTRUCTURE_ONLY = {
    # The famous Millennium / Wikipedia famous set
    'twin_primes', 'goldbach', 'abc', 'beal_conjecture', 'kakeya_set_conjecture',
    'collatz_conjecture', 'jacobian_conjecture', 'invariant_subspace_problem',
    'lehmer_mahler_measure_problem', 'lehmer_totient', 'lehmer_ramanujan_tau',
    'mahler_conjecture', 'sendov_conjecture', 'kummer_vandiver',
    'inverse_galois_problem', 'agoh_giuga', 'class_number_problem',
    'mean_value_problem', 'schinzel_conjecture', 'schanuel_conjecture',
    'pebbling_number_conjecture', 'zero_divisor_conjecture', 'idempotent_conjecture',
    'vaught_conjecture', 'sendov_conjecture', 'pierce_birkhoff_conjecture',
    'union_closed', 'singmaster',
    'KotheConjecture', 'KotherConjecture', 'bounded_burnside_problem',
    'first_hardy_littlewood_conjecture', 'second_hardy_littlewood_conjecture',
    'rational_distance_problem', 'andrica_conjecture',
    'fermat_catalan', 'beal_conjecture', 'hall_conjecture', 'weak_hall_conjecture',
    'firoozbakht_conjecture', 'oppermann_conjecture', 'polignac_conjecture',
    'legendre_conjecture', 'cramer_conjecture',
    'feit_thompson_primes', 'kakeya_set_conjecture',
    'mosers_worm_problem', 'convex_mosers_worm_problem',
    'inscribed_square_problem', 'inscribed_rectangle_problem',
    'mathoverflow_31809', 'mathoverflow_1973',
    'is_every_convex_polyhedron_rupert', 'strong_sensitivity_conjecture',
    'kurepa_conjecture', 'homogeneousSpace_exists_inj_tendsto',
    'lonely_runner_conjecture',
    'fortune', 'agoh_giuga',
}

# Bounded-version_closure candidates — known to be approachable via S2 witness-table chunking
BOUNDED_CLOSURE_CANDIDATES = {
    'brocard_conjecture',          # n in [N1, N2]; S2-witness-table
    'pollock_tetrahedral',         # Salzer-Levine bounded set verification
    'snake_dim_nine',              # LongestSnakeInTheBox 9 = ?; bounded compute
    'BB_6',                        # Busy Beaver 6 unknown lower bound
    'HadamardConjecture',          # 4*167 etc unknown
    'least_eleven_square_packing_in_square',
    'least_seventeen_square_packing_in_square',
    'least_three_square_packing_in_circle',
    'least_twenty_one_circle_packing_in_square',
    'least_fifteen_circle_packing_in_circle',
}

# Disproof / witness_search: explicit-search problems
DISPROOF_CANDIDATES = {
    'exists_isWallSunSunPrime',          # search for a Wall-Sun-Sun prime
    'infinite_isWallSunSunPrime',        # infinite version (less tractable)
    'infinite_isWallSunSunPrime_of_disc_eq',
    'wieferich_search',
    'exists_magic_square_squares',       # search for 3x3 magic square of distinct squares
    'perfect_euler_brick_existence',     # search for perfect Euler brick (witness)
    'four_dim_euler_brick_existence',    # 4-dim Euler hyper-brick witness
    'n_dim_euler_brick_existence',
    'conway99Graph',                     # exists 99-vertex strongly regular?
    'feit_thompson_primes',              # two-prime witness search
    'wolstenholme_prime_infinite',       # only ~2 known; bounded search probe
    'fermat_number_are_composite',       # find new Fermat composite (every F_5..F_32 are composite)
    'all_fermat_squarefree',             # disproof: find Fermat with square divisor
    'infinite_fermat_composite',         # asks for infinitely many composite Fermats
}

# Strongly suspect "answer(sorry)" template -> iff_rfl_trap
ANSWER_TEMPLATE_RE = re.compile(r'answer\s*\(\s*sorry\s*\)')

# Counterexample search patterns
EXISTS_NAT_WITNESS = re.compile(r'∃\s*[a-zA-Z]\w*\s*[:,]\s*ℕ')
EXISTS_INT_WITNESS = re.compile(r'∃\s*[a-zA-Z]\w*\s*[:,]\s*ℤ')
EXISTS_PRIME = re.compile(r'∃\s*\w+.*Prime')
EXISTS_FINSET = re.compile(r'∃\s*\w+\s*[:,]\s*Finset')

# Bounded numeric ceiling pattern
BOUNDED_BODY = re.compile(r'(≤\s*\d{2,})|(<\s*\d{2,})|(Finset\.Icc\s+\d+\s+\d+)|(Finset\.range\s+\d+)')

# 'covering' (Erdős cover-system style)
COVERING_RE = re.compile(r'(covering|Cover\b|Cover[^a-z])', re.IGNORECASE)

# Cardinal/large
LARGE_TYPE = re.compile(r'(ℵ_|Cardinal|Ordinal|Type\s*\*|Type\s*u_)')

# Asymptotic constants ∃ c > 0
ASYMPTOTIC = re.compile(r'∃\s*c\s*>\s*\(?\s*0\s*:\s*ℝ|atTop|∀ᶠ|cofinite|Tendsto|≪|=O\[|=Θ\[|=o\[')

# 'Type-quantified' graph/group conjecture
TYPE_QUANTIFIED = re.compile(r'∀\s*[\(\{]?\s*[A-Z]\s*:\s*Type')

# Reuses an Erdős theorem? (type_of%)
TYPE_OF_PCT = re.compile(r'type_of%\s+Erdos\d+')


def classify_closure(row: dict) -> dict:
    pid = row['problem_id']
    theorem_name = row['theorem_name']
    file_path = row['file_path']
    namespace = row['namespace']
    source_text = read_source(file_path)
    body = find_target_theorem(source_text, theorem_name) if source_text else ''
    has_answer_template = ANSWER_TEMPLATE_RE.search(body) is not None
    has_iff_rfl_predicate = any(p in body for p in IFF_RFL_PREDICATES)
    has_heavy_predicate = any(p in body for p in HEAVY_PREDICATES)
    has_bounded = BOUNDED_BODY.search(body) is not None
    has_exists_nat_witness = EXISTS_NAT_WITNESS.search(body) is not None
    has_exists_finset = EXISTS_FINSET.search(body) is not None
    has_existential = '∃' in body
    has_asymptotic = ASYMPTOTIC.search(body) is not None
    has_covering = COVERING_RE.search(body) is not None or COVERING_RE.search(source_text or '') is not None
    has_type_quantified = TYPE_QUANTIFIED.search(body) is not None
    has_large_type = LARGE_TYPE.search(body) is not None
    has_type_of_pct = TYPE_OF_PCT.search(source_text or '') is not None
    is_em_tautology = '∨' in body and '¬' in body and re.search(r'\(\s*[A-Z]\w*\s*\)\s*∨\s*¬\s*\(\s*[A-Z]\w*\s*\)', body) is not None

    # Detect direct theorem-name patterns
    short_name = theorem_name.split('.')[-1]
    feasibility = row.get('feasibility_category', '')
    quantifier = row.get('quantifier_geometry', '')
    cert_shape = row.get('certificate_shape', '')
    failure = row.get('failure_mode_risk', '')
    prior_score = int(row.get('snipe_score_1_to_10') or 1)

    # ----------------------------------------------------------------------
    # Decide CS (Closure Scope)
    # ----------------------------------------------------------------------
    cs = 'formalization_only'  # default conservative
    if has_type_of_pct:
        # alias of an Erdős problem; not non-Erdős closure
        cs = 'formalization_only'
    elif is_em_tautology:
        cs = 'formalization_only'
    elif short_name in BOUNDED_CLOSURE_CANDIDATES:
        cs = 'bounded_version_closure'
    elif short_name in DISPROOF_CANDIDATES:
        cs = 'disproof_closure'
    elif short_name in FAMOUS_INFRASTRUCTURE_ONLY:
        cs = 'formalization_only'
    elif has_answer_template:
        # answer(sorry) ↔ ... template — Aristotle would discharge as iff_rfl
        cs = 'formalization_only'
    elif has_existential and has_bounded and not has_asymptotic and not has_iff_rfl_predicate:
        # existential bounded statement -> potential disproof or sub-claim
        cs = 'sub_claim_closure'
    elif has_asymptotic or has_iff_rfl_predicate:
        cs = 'formalization_only'
    elif has_existential and not has_asymptotic and not has_iff_rfl_predicate:
        # pure existential, possibly disproof candidate
        if 'Squarefree' in body or 'Prime' in body or 'Composite' in body:
            cs = 'disproof_closure'
        else:
            cs = 'sub_claim_closure'
    elif has_type_quantified or has_large_type:
        cs = 'formalization_only'
    else:
        # ∀-only or other shape -> structural
        if has_bounded:
            cs = 'bounded_version_closure'
        else:
            cs = 'formalization_only'

    # ----------------------------------------------------------------------
    # Decide CM (Closure Mechanism)
    # ----------------------------------------------------------------------
    cm = 'none_known'
    if cs == 'bounded_version_closure' and short_name in BOUNDED_CLOSURE_CANDIDATES:
        cm = 'witness_table_chunked'
    elif cs == 'disproof_closure':
        cm = 'disproof_construction'
    elif cs == 'sub_claim_closure' and has_exists_nat_witness:
        cm = 'explicit_witness'
    elif cs == 'bounded_version_closure':
        cm = 'witness_table_chunked'
    elif has_covering and has_existential:
        cm = 'structural_finite_reduction'
    elif has_asymptotic or has_iff_rfl_predicate:
        cm = 'none_known'
    else:
        cm = 'none_known'

    # ----------------------------------------------------------------------
    # Decide CR (Closure Risk - primary)
    # ----------------------------------------------------------------------
    if is_em_tautology:
        cr = 'em_tautology'
    elif has_answer_template or 'answer(sorry)' in body:
        cr = 'iff_rfl_trap'
    elif has_iff_rfl_predicate and cs == 'formalization_only':
        cr = 'iff_rfl_trap'
    elif cs == 'bounded_version_closure' and cm == 'witness_table_chunked':
        cr = 'witness_search_explosion'  # mitigable via chunking
    elif cs == 'disproof_closure':
        cr = 'witness_search_explosion'  # search may not terminate
    elif cs == 'sub_claim_closure' and cm == 'explicit_witness':
        cr = 'clean_decidable'
    elif failure == 'F1-iff-rfl':
        cr = 'iff_rfl_trap'
    elif failure == 'F3-side-lemma-bloat':
        cr = 'infrastructure_overgrowth'
    elif failure == 'F8-vacuous-iff':
        cr = 'iff_rfl_trap'
    elif failure == 'F9-compute-explosion':
        cr = 'witness_search_explosion'
    elif has_heavy_predicate:
        cr = 'definition_mismatch'
    else:
        cr = 'infrastructure_overgrowth'

    # ----------------------------------------------------------------------
    # Decide HM (Honesty Marker)
    # ----------------------------------------------------------------------
    if cs == 'full_closure' and cr == 'clean_decidable':
        hm = 'journal_clean'
    elif cs == 'disproof_closure' and cr == 'clean_decidable':
        hm = 'journal_clean'
    elif cs == 'disproof_closure':
        # Witness disproof closure — if found, it IS the answer
        hm = 'journal_clean'
    elif cs == 'bounded_version_closure':
        hm = 'journal_partial'
    elif cs == 'sub_claim_closure':
        hm = 'journal_subclaim'
    elif cs == 'direction_closure':
        hm = 'journal_subclaim'
    elif cs == 'formalization_only':
        hm = 'infrastructure_only'
    else:
        hm = 'infrastructure_only'

    # ----------------------------------------------------------------------
    # Scoring
    # ----------------------------------------------------------------------
    score = 5
    score += {
        'full_closure': 3, 'disproof_closure': 3, 'direction_closure': 2,
        'sub_claim_closure': 1, 'bounded_version_closure': 0,
        'formalization_only': -2,
    }.get(cs, 0)
    score += {
        'explicit_witness': 3, 'disproof_construction': 3, 'witness_table_chunked': 3,
        'structural_finite_reduction': 2, 'bounded_to_infinite_lift': 1,
        'none_known': -3, 'density_sieve_closure': -2, 'induction_template': -2,
    }.get(cm, 0)
    score += {
        'clean_decidable': 2, 'witness_search_explosion': 0,
        'partial_result_only': -1,
        'iff_rfl_trap': -3, 'em_tautology': -3,
        'definition_mismatch': -3, 'infrastructure_overgrowth': -3,
        'recursive_falsification': -2,
    }.get(cr, 0)
    score += {
        'journal_clean': 2, 'journal_partial': 1, 'journal_subclaim': 1,
        'infrastructure_only': -3,
    }.get(hm, 0)
    score = max(1, min(10, score))

    # ----------------------------------------------------------------------
    # Action
    # ----------------------------------------------------------------------
    if score >= 8 and hm in ('journal_clean', 'journal_subclaim'):
        action = 'CLOSURE_CANDIDATE'
    elif score >= 6 and hm in ('journal_clean', 'journal_subclaim', 'journal_partial'):
        action = 'CLOSURE_PROBE'
    elif score >= 5 and hm == 'journal_partial':
        action = 'BOUNDED_ONLY'
    else:
        action = 'AVOID'

    # ----------------------------------------------------------------------
    # Rationale - concise
    # ----------------------------------------------------------------------
    bits = []
    if cs == 'formalization_only':
        bits.append('formalization_only')
    elif cs in ('bounded_version_closure', 'sub_claim_closure', 'disproof_closure'):
        bits.append(cs)
    if cm in ('witness_table_chunked', 'explicit_witness', 'disproof_construction'):
        bits.append(cm)
    elif cm == 'none_known':
        bits.append('CM=none')
    if cr == 'iff_rfl_trap':
        bits.append('iff_rfl_trap (answer-template)')
    elif cr == 'em_tautology':
        bits.append('em_tautology')
    elif cr == 'witness_search_explosion':
        bits.append('search_explosion (chunked?)')
    elif cr == 'infrastructure_overgrowth':
        bits.append('F3 bloat')
    elif cr == 'definition_mismatch':
        bits.append('def_mismatch (theory-heavy)')
    if hm == 'journal_clean':
        bits.append('HM=journal_clean')
    elif hm == 'journal_partial':
        bits.append('HM=journal_partial')
    elif hm == 'journal_subclaim':
        bits.append('HM=journal_subclaim')
    else:
        bits.append('HM=infra')
    rationale = '; '.join(bits)

    return {
        'closure_scope': cs,
        'closure_mechanism': cm,
        'closure_risk': cr,
        'honesty_marker': hm,
        'closure_score': str(score),
        'closure_action': action,
        'closure_rationale': rationale,
    }


def main():
    rows_out = []
    fieldnames = None
    with open(PRIOR, newline='') as fp:
        reader = csv.DictReader(fp)
        in_fields = list(reader.fieldnames)
        # New columns appended after prior columns
        new_fields = in_fields + [
            'closure_scope', 'closure_mechanism', 'closure_risk', 'honesty_marker',
            'closure_score', 'closure_action', 'closure_rationale',
        ]
        fieldnames = new_fields
        for row in reader:
            extra = classify_closure(row)
            row.update(extra)
            rows_out.append(row)

    with open(OUT, 'w', newline='') as fp:
        writer = csv.DictWriter(fp, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows_out:
            writer.writerow(row)
    print(f"Wrote {len(rows_out)} rows to {OUT}")


if __name__ == '__main__':
    main()
