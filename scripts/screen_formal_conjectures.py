#!/usr/bin/env python3
"""
Batch screen formal-conjectures problems for AI theorem proving suitability.
Focused on finding genuinely OPEN problems that Aristotle can solve.

KEY PRINCIPLE: We want OPEN problems where computation or witness-finding
IS the proof strategy. Not formalizations of known results.

Priority tiers:
  TIER 1: Open + fully finite domain (native_decide closes the full theorem)
  TIER 2: Open + answer(sorry) (determining True/False is the contribution)
  TIER 3: Open + pure existential (finding a witness solves it)
  TIER 4: Open + falsifiable (counterexample on small instance disproves it)
  TIER 5: Open + known proof sketch (INFORMAL mode can formalize)
  REJECT: Open + requires novel math over infinite domain

Scans any directory of Lean files (Erdos, Wikipedia, Green, OEIS, etc.)
and ranks open problems by AI-solvability.
"""
import os
import re
import json
import sys
import sqlite3
from pathlib import Path
from collections import Counter

DB_PATH = Path("submissions/tracking.db")

# Default scan targets — all problem directories
DEFAULT_DIRS = [
    "formal-conjectures/FormalConjectures/ErdosProblems",
    "formal-conjectures/FormalConjectures/Wikipedia",
    "formal-conjectures/FormalConjectures/GreensOpenProblems",
    "formal-conjectures/FormalConjectures/OEIS",
    "formal-conjectures/FormalConjectures/Paper",
    "formal-conjectures/FormalConjectures/Arxiv",
    "formal-conjectures/FormalConjectures/Mathoverflow",
    "formal-conjectures/FormalConjectures/Other",
]

# AMS code to domain mapping
AMS_DOMAIN = {
    "05": "combinatorics", "11": "number_theory",
    "12": "algebra", "13": "algebra", "15": "algebra", "16": "algebra", "20": "algebra",
    "26": "analysis", "28": "analysis", "30": "analysis", "33": "analysis",
    "42": "analysis", "46": "analysis",
    "51": "geometry", "52": "geometry",
    "60": "probability", "68": "cs", "90": "optimization", "97": "education",
}

# Domain to AI success rate (from literature: MiniF2F, CombiBench, HILBERT, etc.)
DOMAIN_SCORE = {
    "algebra": 9, "number_theory": 8, "analysis": 5, "probability": 5,
    "geometry": 3, "combinatorics": 2, "cs": 4, "optimization": 4,
    "education": 7, "unknown": 4,
}

# ─── Open theorem statement analysis ───────────────────────────────────────────
# These patterns in an OPEN theorem statement signal that the claim is
# infinite/asymptotic and likely NOT solvable by native_decide or short proof.
HARD_SIGNALS = [
    # Limits / filters / asymptotics
    r'Tendsto', r'atTop', r'atBot', r'𝓝', r'nhds', r'Filter\.',
    r'=O\[', r'=o\[', r'=Θ\[', r'∀ᶠ', r'∃ᶠ', r'cofinite', r'cocompact',
    # Density / measure
    r'HasDensity', r'lowerDensity', r'upperDensity', r'MeasureTheory',
    # Infinite sets
    r'Set\.Infinite', r'\.Infinite\b',
    # Analysis / continuous math
    r'∑\'', r'tsum', r'HasSum', r'Summable', r'limsup', r'liminf',
    r'ContinuousOn', r'Differentiable', r'Integrable', r'∫',
    r'Real\.exp', r'Complex\.', r'Polynomial\b', r'PowerSeries',
    r'Irrational', r'Transcendental',
    # Infinite sequences / functions
    r'Function\.Injective',
    r'GaussianInt',
]

# These patterns signal GOOD structure for AI solving
GOOD_SIGNALS = [
    r'\bFin\b', r'\bZMod\b', r'\bFinset\b', r'\bFintype\b',
    r'\bDecidableEq\b', r'\bDecidable\b',
    r'\.minFac\b', r'\.choose\b', r'\.factorial\b', r'\.Prime\b',
    r'\.divisors\b', r'\.gcd\b', r'\.lcm\b',
    r'\bNat\.card\b', r'\bcentralBinom\b',
    r'\borderOf\b', r'\bIsCyclic\b', r'\bSubgroup\b',
    r'\bnative_decide\b', r'\bdecide\b',
]


def extract_open_theorems(content):
    """Extract individual open theorem blocks with their statements."""
    # Match: @[category research open ...] theorem/lemma name ... := by\n  sorry
    pattern = r'(@\[category\s+research\s+open[^\]]*\].*?(?:theorem|lemma)\s+(\S+)(.*?):=\s*by\s*\n\s*sorry)'
    matches = re.findall(pattern, content, re.DOTALL)
    theorems = []
    for full_block, name, sig in matches:
        stmt_lines = full_block.strip().split('\n')
        theorems.append({
            'name': name,
            'full': full_block.strip(),
            'signature': sig.strip(),
            'lines': len(stmt_lines),
            'short': ' '.join(l.strip() for l in stmt_lines[1:5])[:200],
        })
    return theorems


def classify_quantifiers(thm_text):
    """Classify whether the theorem is over finite or infinite domain."""
    # Fully finite: only quantifies over Fin, ZMod, bounded types
    has_fin_quant = bool(re.search(r'(?:Fin|ZMod|Equiv\.Perm|DihedralGroup)\s+\d+', thm_text))
    has_finset = bool(re.search(r'\bFinset\b|\bFintype\b', thm_text))

    # Infinite quantifiers: ∀/∃ over ℕ, ℤ, ℝ without finite bound
    has_nat_univ = bool(re.search(r'∀\s*[^,]*:\s*ℕ', thm_text)) and not has_fin_quant
    has_int_univ = bool(re.search(r'∀\s*[^,]*:\s*ℤ', thm_text))
    has_real = bool(re.search(r':\s*ℝ', thm_text))
    has_type_univ = bool(re.search(r'∀\s*\([^)]*:\s*Type', thm_text))

    # Pure existential (no universal over infinite type)
    has_exists = bool(re.search(r'∃\s', thm_text))
    infinite_universal = has_nat_univ or has_int_univ or has_real or has_type_univ

    return {
        'fully_finite': has_fin_quant and not infinite_universal,
        'has_finset': has_finset,
        'infinite_universal': infinite_universal,
        'pure_existential': has_exists and not infinite_universal,
        'has_nat_universal': has_nat_univ,
        'has_type_universal': has_type_univ,
    }


def score_open_theorem(thm_text):
    """Score a single open theorem for AI-solvability. Returns (score, reasons, tier)."""
    score = 5.0  # baseline
    reasons = []
    tier = 'UNKNOWN'

    quant = classify_quantifiers(thm_text)

    # ─── TIER CLASSIFICATION (most important) ────────────────────────────────

    # TIER 1: Fully finite domain — computation IS the proof
    if quant['fully_finite']:
        score += 3.0
        reasons.append('TIER1: fully finite domain — native_decide could close')
        tier = 'FINITE'

    # answer(sorry) — determining True/False IS the open question
    if 'answer(sorry)' in thm_text:
        score += 2.0  # BIG bonus: this is where we add value
        reasons.append('TIER2: answer(sorry) — True/False unknown, high-value target')
        if tier == 'UNKNOWN':
            tier = 'ANSWER_UNKNOWN'

    # answer already known — less interesting (just formalization)
    if 'answer(True)' in thm_text or 'answer(False)' in thm_text:
        score -= 0.5  # slight penalty: answer known, just need proof
        reasons.append('answer already determined (formalization only)')

    # Pure existential over computable domain — find a witness
    if quant['pure_existential'] and not quant['infinite_universal']:
        score += 1.5
        reasons.append('TIER3: pure existential — witness search')
        if tier == 'UNKNOWN':
            tier = 'WITNESS'

    # Negation of existence — falsification-friendly
    if re.search(r'¬\s*∃', thm_text):
        score += 1.0
        reasons.append('TIER4: negation of ∃ — falsification target')
        if tier == 'UNKNOWN':
            tier = 'FALSIFY'

    # ─── HARD SIGNALS (infinite/asymptotic → penalty) ────────────────────────

    hard_count = 0
    for pat in HARD_SIGNALS:
        if re.search(pat, thm_text):
            hard_count += 1
    if hard_count >= 3:
        score -= 3.0
        reasons.append(f'{hard_count} hard signals (infinite/asymptotic)')
        tier = 'INFINITE'
    elif hard_count >= 1:
        score -= 1.0 * hard_count
        reasons.append(f'{hard_count} hard signal(s)')

    # ─── GOOD SIGNALS (finite/decidable → bonus) ────────────────────────────

    good_count = 0
    for pat in GOOD_SIGNALS:
        if re.search(pat, thm_text):
            good_count += 1
    if good_count >= 3:
        score += 2.0
        reasons.append(f'{good_count} good signals (finite/decidable)')
    elif good_count >= 1:
        score += 0.5 * good_count
        reasons.append(f'{good_count} good signal(s)')

    # ─── STATEMENT STRUCTURE ─────────────────────────────────────────────────

    line_count = len(thm_text.strip().split('\n'))
    if line_count <= 4:
        score += 1.0
        reasons.append('short statement (≤4 lines)')
    elif line_count <= 7:
        score += 0.5
    elif line_count > 12:
        score -= 1.0
        reasons.append('long statement (>12 lines)')

    # Universal over ℕ without Fin — needs infinite argument
    if quant['has_nat_universal']:
        score -= 1.5
        reasons.append('∀ over ℕ without finite bound')
        if tier == 'UNKNOWN':
            tier = 'INFINITE'

    # Universal over Type* — very abstract
    if quant['has_type_universal']:
        score -= 0.5
        reasons.append('∀ over Type* (abstract)')

    # .Finite claim — proving finiteness is hard
    if re.search(r'\.Finite\b', thm_text):
        score -= 1.5
        reasons.append('proving .Finite over ℕ subset')
        tier = 'INFINITE'

    if tier == 'UNKNOWN':
        tier = 'MIXED'

    return max(0, min(10, score)), reasons, tier


def extract_metadata(filepath):
    """Extract metadata from a single Lean file."""
    content = filepath.read_text(errors='replace')

    # Determine source category from path
    parts = filepath.parts
    source_cat = 'unknown'
    for p in parts:
        if p in ('ErdosProblems', 'Wikipedia', 'GreensOpenProblems', 'OEIS',
                 'Paper', 'Arxiv', 'Mathoverflow', 'Other'):
            source_cat = p
            break

    result = {
        'file': filepath.name,
        'problem_id': filepath.stem,
        'path': str(filepath),
        'source_cat': source_cat,
        'lines': len(content.splitlines()),
        'categories': [],
        'ams_codes': [],
        'domains': [],
        'is_open': False,
        'is_solved': False,
        'is_formally_solved': False,
        'has_answer_sorry': False,
        'has_answer_known': False,
        'sorry_count': 0,
        'open_theorems': [],
        'open_count': 0,
        'best_open_score': 0,
        'best_open_name': '',
        'best_open_reasons': [],
        'best_open_short': '',
        'has_decide': False,
        'has_proven_lemmas': False,  # file has non-sorry proofs (scaffolding exists)
        'domain_score': 0,
    }

    # Extract category tags
    cat_matches = re.findall(r'@\[category\s+([^\]]+)\]', content)
    for cat in cat_matches:
        result['categories'].append(cat.strip())
        if 'research open' in cat:
            result['is_open'] = True
        if 'research solved' in cat and 'formally' not in cat:
            result['is_solved'] = True
        if 'formally_solved' in cat:
            result['is_formally_solved'] = True

    # Extract AMS codes
    ams_matches = re.findall(r'AMS\s+(\d+)', content)
    result['ams_codes'] = list(set(ams_matches))

    # Map AMS to domains
    for code in result['ams_codes']:
        domain = AMS_DOMAIN.get(code, "unknown")
        if domain not in result['domains']:
            result['domains'].append(domain)
    if not result['domains']:
        result['domains'] = ['unknown']

    # Domain score
    result['domain_score'] = max(DOMAIN_SCORE.get(d, 4) for d in result['domains'])

    # Count sorry
    result['sorry_count'] = len(re.findall(r'\bsorry\b', content))

    # Check for answer patterns
    result['has_answer_sorry'] = 'answer(sorry)' in content
    result['has_answer_known'] = bool(re.search(r'answer\((?:True|False)\)', content))

    # Check for decide/native_decide (signals finite computability)
    result['has_decide'] = bool(re.search(r'\b(?:decide|native_decide)\b', content))

    # Check for proven lemmas (non-sorry proofs exist in file)
    result['has_proven_lemmas'] = bool(re.search(
        r'(?:theorem|lemma)\s+\w+.*?:=\s*by\s*\n(?!\s*sorry)', content, re.DOTALL))

    # Extract and score open theorems individually
    open_thms = extract_open_theorems(content)
    result['open_count'] = len(open_thms)
    result['best_tier'] = 'NONE'

    best_score = 0
    for thm in open_thms:
        thm_score, reasons, tier = score_open_theorem(thm['full'])

        # Domain bonus applied at theorem level
        thm_score_with_domain = thm_score + (result['domain_score'] - 5) * 0.3

        # Existing infrastructure bonus
        if result['has_decide']:
            thm_score_with_domain += 0.5
        if result['has_proven_lemmas']:
            thm_score_with_domain += 0.3

        thm_score_with_domain = max(0, min(10, thm_score_with_domain))

        thm['score'] = round(thm_score_with_domain, 1)
        thm['reasons'] = reasons
        thm['tier'] = tier

        if thm_score_with_domain > best_score:
            best_score = thm_score_with_domain
            result['best_open_score'] = round(thm_score_with_domain, 1)
            result['best_open_name'] = thm['name']
            result['best_open_reasons'] = reasons
            result['best_open_short'] = thm['short']
            result['best_tier'] = tier

    result['open_theorems'] = open_thms
    return result


def main():
    # Parse command-line args
    scan_dirs = []
    if len(sys.argv) > 1:
        for arg in sys.argv[1:]:
            p = Path(arg)
            if p.is_dir():
                scan_dirs.append(p)
            else:
                print(f"WARNING: {arg} is not a directory, skipping")
    else:
        scan_dirs = [Path(d) for d in DEFAULT_DIRS if Path(d).exists()]

    if not scan_dirs:
        print("ERROR: No valid directories to scan.")
        print(f"Usage: {sys.argv[0]} [dir1] [dir2] ...")
        print(f"Default dirs: {DEFAULT_DIRS}")
        return

    # Collect all Lean files
    all_files = []
    for d in scan_dirs:
        files = sorted(d.glob("*.lean"))
        all_files.extend(files)
        print(f"  {d}: {len(files)} files")

    print(f"\nScanning {len(all_files)} Lean files across {len(scan_dirs)} directories...")

    all_meta = []
    for f in all_files:
        try:
            meta = extract_metadata(f)
            if meta['is_open']:  # Only care about open problems
                all_meta.append(meta)
        except Exception as e:
            print(f"  ERROR on {f.name}: {e}")

    # Sort by best_open_score descending
    all_meta.sort(key=lambda m: m['best_open_score'], reverse=True)

    # Summary
    domains = Counter(d for m in all_meta for d in m['domains'])
    sources = Counter(m['source_cat'] for m in all_meta)
    total_open_thms = sum(m['open_count'] for m in all_meta)

    print(f"\n{'='*70}")
    print(f"OPEN PROBLEM SCREENING: {len(all_meta)} files with open problems")
    print(f"Total open theorem statements: {total_open_thms}")
    print(f"{'='*70}")

    print(f"\nBy source:")
    for src, count in sources.most_common():
        print(f"  {src}: {count}")

    print(f"\nBy domain:")
    for domain, count in domains.most_common():
        score = DOMAIN_SCORE.get(domain, 0)
        print(f"  {domain}: {count} (AI score: {score}/10)")

    # Score distribution
    brackets = {'8+': 0, '6-8': 0, '4-6': 0, '2-4': 0, '0-2': 0}
    for m in all_meta:
        s = m['best_open_score']
        if s >= 8: brackets['8+'] += 1
        elif s >= 6: brackets['6-8'] += 1
        elif s >= 4: brackets['4-6'] += 1
        elif s >= 2: brackets['2-4'] += 1
        else: brackets['0-2'] += 1

    print(f"\nAI-solvability score distribution:")
    for bracket, count in brackets.items():
        bar = '█' * count
        print(f"  {bracket:>5}: {count:>3} {bar}")

    # ─── TIER SUMMARY ─────────────────────────────────────────────────────────
    tiers = Counter(m['best_tier'] for m in all_meta)
    print(f"\nBy tier (priority):")
    tier_order = ['FINITE', 'ANSWER_UNKNOWN', 'WITNESS', 'FALSIFY', 'MIXED', 'INFINITE', 'NONE']
    tier_desc = {
        'FINITE': 'fully finite — computation IS proof',
        'ANSWER_UNKNOWN': 'answer(sorry) — True/False unknown',
        'WITNESS': 'pure existential — find a witness',
        'FALSIFY': 'negation of ∃ — counterexample search',
        'MIXED': 'mixed structure',
        'INFINITE': 'infinite domain — needs novel math',
        'NONE': 'no open theorems extracted',
    }
    for t in tier_order:
        if tiers.get(t, 0) > 0:
            marker = '★' if t in ('FINITE', 'ANSWER_UNKNOWN', 'WITNESS', 'FALSIFY') else ' '
            print(f"  {marker} {t:<18} {tiers[t]:>3}  ({tier_desc.get(t, '')})")

    # ─── TOP TARGETS BY TIER ─────────────────────────────────────────────────
    # Show high-value tiers first, then by score within tier
    priority_tiers = {'FINITE', 'ANSWER_UNKNOWN', 'WITNESS', 'FALSIFY'}
    high_value = [m for m in all_meta if m['best_tier'] in priority_tiers]
    high_value.sort(key=lambda m: m['best_open_score'], reverse=True)

    if high_value:
        print(f"\n{'='*70}")
        print(f"HIGH-VALUE TARGETS: {len(high_value)} open problems where computation could solve")
        print(f"{'='*70}")
        print(f"{'Score':<6} {'Tier':<16} {'Source':<10} {'Problem':<30} {'Domain':<12} {'Why'}")
        print("-" * 120)

        for m in high_value[:30]:
            domain_str = '/'.join(m['domains'][:2])
            reasons_short = '; '.join(m['best_open_reasons'][:2])
            src = m['source_cat'][:10]
            print(f"  {m['best_open_score']:<5} {m['best_tier']:<16} {src:<10} {m['best_open_name']:<30} {domain_str:<12} {reasons_short[:45]}")

    # ─── ALL TOP 30 ──────────────────────────────────────────────────────────
    print(f"\n{'='*70}")
    print(f"TOP 30 ALL OPEN PROBLEMS BY SCORE")
    print(f"{'='*70}")
    print(f"{'Score':<6} {'Tier':<16} {'Source':<10} {'Problem':<30} {'Domain':<12} {'Why'}")
    print("-" * 120)

    for m in all_meta[:30]:
        domain_str = '/'.join(m['domains'][:2])
        reasons_short = '; '.join(m['best_open_reasons'][:2])
        src = m['source_cat'][:10]
        print(f"  {m['best_open_score']:<5} {m['best_tier']:<16} {src:<10} {m['best_open_name']:<30} {domain_str:<12} {reasons_short[:45]}")

    # ─── DETAILED TOP 10 HIGH-VALUE ──────────────────────────────────────────
    detail_targets = high_value[:10] if high_value else all_meta[:10]
    label = "HIGH-VALUE" if high_value else "ALL"
    print(f"\n{'='*70}")
    print(f"DETAILED TOP 10 ({label})")
    print(f"{'='*70}")

    for i, m in enumerate(detail_targets, 1):
        print(f"\n--- #{i}: {m['best_open_name']} (score {m['best_open_score']}/10, tier {m['best_tier']}) ---")
        print(f"File: {m['path']}")
        print(f"Domain: {'/'.join(m['domains'])} | Source: {m['source_cat']} | Open theorems: {m['open_count']}")
        print(f"Infrastructure: decide={'Y' if m['has_decide'] else 'N'} | proven_lemmas={'Y' if m['has_proven_lemmas'] else 'N'} | answer_known={'Y' if m['has_answer_known'] else 'N'} | answer_sorry={'Y' if m['has_answer_sorry'] else 'N'}")
        print(f"Reasons: {', '.join(m['best_open_reasons'])}")
        print(f"Statement: {m['best_open_short']}")

    # Save full results (high-value first, then rest by score)
    output_path = Path("docs/open_problem_screening.json")
    # Serialize without open_theorems to keep file manageable
    slim_meta = []
    # High-value targets first
    for m in high_value:
        slim = {k: v for k, v in m.items() if k != 'open_theorems'}
        slim_meta.append(slim)
    # Then everything else
    hv_ids = {m['problem_id'] for m in high_value}
    for m in all_meta:
        if m['problem_id'] not in hv_ids:
            slim = {k: v for k, v in m.items() if k != 'open_theorems'}
            slim_meta.append(slim)
    with open(output_path, 'w') as f:
        json.dump(slim_meta, f, indent=2, default=str)
    print(f"\nFull results saved to {output_path}")


if __name__ == '__main__':
    main()
