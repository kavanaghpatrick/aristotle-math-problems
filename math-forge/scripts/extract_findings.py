#!/usr/bin/env python3
"""extract_findings.py — Parse Aristotle .lean result files into knowledge.db findings.

Usage:
    python3 extract_findings.py <result_file> [--slot N] [--problem-id ID] [--db PATH]

Extraction stages:
    1. Structural: theorem names, lemma names, def names (regex)
    2. Import analysis: Mathlib imports used (regex)
    3. Metric: sorry count, axiom count, proof line count
    4. Technique inference: heuristic from tactics used (regex)
    5. Finding generation: one finding per theorem proved
"""

import re
import sys
import sqlite3
import argparse
from pathlib import Path
from datetime import datetime

# --- Regex patterns for Lean 4 extraction ---

# Theorem/lemma/def declarations
DECL_RE = re.compile(
    r'^(theorem|lemma|def|noncomputable def|instance)\s+'
    r'(\w+)',
    re.MULTILINE
)

# Mathlib imports
IMPORT_RE = re.compile(r'^import\s+(Mathlib\.\w[\w.]*)', re.MULTILINE)

# Sorry locations
SORRY_RE = re.compile(r'\bsorry\b')

# Axiom declarations
AXIOM_RE = re.compile(r'^axiom\s+(\w+)', re.MULTILINE)

# Tactic usage (for technique inference)
TACTIC_PATTERNS = {
    'native_decide': re.compile(r'\bnative_decide\b'),
    'decide': re.compile(r'\bdecide\b'),
    'omega': re.compile(r'\bomega\b'),
    'simp': re.compile(r'\bsimp\b'),
    'ring': re.compile(r'\bring\b'),
    'norm_num': re.compile(r'\bnorm_num\b'),
    'induction': re.compile(r'\binduction\b'),
    'cases': re.compile(r'\bcases\b'),
    'contradiction': re.compile(r'\bcontradiction\b'),
    'exact': re.compile(r'\bexact\b'),
    'apply': re.compile(r'\bapply\b'),
    'calc': re.compile(r'\bcalc\b'),
    'interval_cases': re.compile(r'\binterval_cases\b'),
    'field_simp': re.compile(r'\bfield_simp\b'),
    'zify': re.compile(r'\bzify\b'),
    'push_cast': re.compile(r'\bpush_cast\b'),
}

# Technique inference heuristics
TECHNIQUE_MAP = {
    'native_decide': 'finite computation (native_decide)',
    'decide': 'finite computation (decide)',
    'omega': 'linear arithmetic (omega)',
    'norm_num': 'numerical normalization',
    'ring': 'ring tactic',
    'induction': 'induction',
    'interval_cases': 'interval case analysis',
    'field_simp': 'field simplification',
    'calc': 'calculational proof',
}


def extract_from_lean(content: str, filepath: str) -> dict:
    """Extract structured data from a .lean file."""

    # Declarations
    declarations = []
    for match in DECL_RE.finditer(content):
        decl_type = match.group(1)
        decl_name = match.group(2)
        # Find the statement (text until := or where or by)
        start = match.end()
        stmt_match = re.search(r'(:=|\bwhere\b|\bby\b)', content[start:start+500])
        statement = content[match.start():start + (stmt_match.start() if stmt_match else 200)].strip()

        # Check if this specific declaration has sorry
        # Look for 'sorry' between this declaration and the next one
        next_decl = DECL_RE.search(content, start)
        end_pos = next_decl.start() if next_decl else len(content)
        block = content[start:end_pos]
        has_sorry = bool(SORRY_RE.search(block))

        declarations.append({
            'type': decl_type,
            'name': decl_name,
            'statement': statement[:500],  # Truncate long statements
            'has_sorry': has_sorry,
            'line_count': block.count('\n'),
        })

    # Imports
    imports = [m.group(1) for m in IMPORT_RE.finditer(content)]

    # Global metrics
    sorry_count = len(SORRY_RE.findall(content))
    axiom_matches = AXIOM_RE.findall(content)
    total_lines = content.count('\n') + 1

    # Technique inference
    tactic_counts = {}
    for name, pattern in TACTIC_PATTERNS.items():
        count = len(pattern.findall(content))
        if count > 0:
            tactic_counts[name] = count

    # Determine primary technique
    primary_technique = None
    if tactic_counts:
        # Priority: specific tactics first
        for tactic in ['native_decide', 'decide', 'induction', 'calc', 'interval_cases']:
            if tactic in tactic_counts:
                primary_technique = TECHNIQUE_MAP.get(tactic, tactic)
                break
        if not primary_technique:
            # Most-used tactic
            top_tactic = max(tactic_counts, key=tactic_counts.get)
            primary_technique = TECHNIQUE_MAP.get(top_tactic, top_tactic)

    return {
        'declarations': declarations,
        'imports': imports,
        'sorry_count': sorry_count,
        'axiom_count': len(axiom_matches),
        'axiom_names': axiom_matches,
        'total_lines': total_lines,
        'tactic_counts': tactic_counts,
        'primary_technique': primary_technique,
    }


def infer_domain(imports: list[str], content: str) -> str:
    """Infer mathematical domain from imports and content."""
    nt_signals = ['Mathlib.NumberTheory', 'Mathlib.Data.ZMod', 'Nat.Prime',
                  'Mathlib.RingTheory', 'Mathlib.FieldTheory']
    algebra_signals = ['Mathlib.Algebra', 'Mathlib.GroupTheory', 'Mathlib.LinearAlgebra']
    combo_signals = ['Mathlib.Combinatorics', 'SimpleGraph', 'Finset.sym2', 'Hypergraph']
    analysis_signals = ['Mathlib.Analysis', 'Mathlib.MeasureTheory', 'Mathlib.Topology']

    scores = {'nt': 0, 'algebra': 0, 'combinatorics': 0, 'analysis': 0}
    for imp in imports:
        for signal in nt_signals:
            if signal in imp:
                scores['nt'] += 1
        for signal in algebra_signals:
            if signal in imp:
                scores['algebra'] += 1
        for signal in combo_signals:
            if signal in imp:
                scores['combinatorics'] += 1
        for signal in analysis_signals:
            if signal in imp:
                scores['analysis'] += 1

    if max(scores.values()) == 0:
        return 'nt'  # Default for this project
    return max(scores, key=scores.get)


def generate_findings(extracted: dict, slot: int, problem_id: str,
                      domain: str, filepath: str) -> list[dict]:
    """Generate finding records from extracted data."""
    findings = []

    is_proven = extracted['sorry_count'] == 0 and extracted['axiom_count'] == 0

    for decl in extracted['declarations']:
        if decl['type'] in ('theorem', 'lemma') and not decl['has_sorry']:
            findings.append({
                'finding_type': 'theorem',
                'domain_id': domain,
                'title': f"{decl['name']} ({decl['type']})",
                'description': f"Proven {decl['type']} from slot{slot}: {decl['statement'][:200]}",
                'problem_id': problem_id,
                'source_slot': slot,
                'source_file': filepath,
                'theorem_name': decl['name'],
                'theorem_statement': decl['statement'],
                'proof_technique': extracted['primary_technique'],
                'mathlib_imports': ', '.join(extracted['imports'][:10]),
                'proof_lines': decl['line_count'],
                'confidence': 'verified' if is_proven else 'medium',
                'tags': domain,
            })

    # If the whole file is proven, add a technique finding
    if is_proven and extracted['primary_technique']:
        findings.append({
            'finding_type': 'technique',
            'domain_id': domain,
            'title': f"Technique: {extracted['primary_technique']} (slot{slot})",
            'description': (
                f"Proof technique '{extracted['primary_technique']}' used successfully "
                f"in slot{slot} for problem {problem_id}. "
                f"Tactics: {', '.join(sorted(extracted['tactic_counts'].keys()))}. "
                f"Key imports: {', '.join(extracted['imports'][:5])}."
            ),
            'problem_id': problem_id,
            'source_slot': slot,
            'source_file': filepath,
            'proof_technique': extracted['primary_technique'],
            'mathlib_imports': ', '.join(extracted['imports'][:10]),
            'proof_lines': extracted['total_lines'],
            'confidence': 'verified',
            'tags': f"{domain},technique",
        })

    # If it failed (many sorry), add a failure finding
    if extracted['sorry_count'] > 2:
        findings.append({
            'finding_type': 'failure',
            'domain_id': domain,
            'title': f"Failed attempt: slot{slot} ({extracted['sorry_count']} sorry)",
            'description': (
                f"Aristotle attempt on {problem_id} in slot{slot} resulted in "
                f"{extracted['sorry_count']} sorry gaps out of "
                f"{len(extracted['declarations'])} declarations."
            ),
            'problem_id': problem_id,
            'source_slot': slot,
            'source_file': filepath,
            'why_failed': f"{extracted['sorry_count']} sorry remaining",
            'confidence': 'high',
            'tags': f"{domain},failure",
        })

    return findings


def insert_findings(db_path: str, findings: list[dict]) -> int:
    """Insert findings into knowledge.db. Returns count inserted."""
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    inserted = 0

    for f in findings:
        try:
            cursor.execute("""
                INSERT INTO findings (
                    finding_type, domain_id, title, description, problem_id,
                    source_slot, source_file, theorem_name, theorem_statement,
                    proof_technique, mathlib_imports, proof_lines,
                    counterexample, why_failed, avoid_pattern,
                    confidence, tags, notes
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                f.get('finding_type'), f.get('domain_id'), f.get('title'),
                f.get('description'), f.get('problem_id'), f.get('source_slot'),
                f.get('source_file'), f.get('theorem_name'), f.get('theorem_statement'),
                f.get('proof_technique'), f.get('mathlib_imports'), f.get('proof_lines'),
                f.get('counterexample'), f.get('why_failed'), f.get('avoid_pattern'),
                f.get('confidence'), f.get('tags'), f.get('notes'),
            ))
            inserted += 1
        except sqlite3.IntegrityError as e:
            print(f"[math-forge] WARN: Skipping duplicate finding: {f['title']} ({e})",
                  file=sys.stderr)

    conn.commit()
    conn.close()
    return inserted


def main():
    parser = argparse.ArgumentParser(description='Extract findings from Aristotle result files')
    parser.add_argument('result_file', help='Path to .lean result file')
    parser.add_argument('--slot', type=int, help='Slot number (auto-detected from filename if omitted)')
    parser.add_argument('--problem-id', help='Problem ID (auto-detected from filename if omitted)')
    parser.add_argument('--db', default=None, help='Path to knowledge.db')
    args = parser.parse_args()

    filepath = Path(args.result_file)
    if not filepath.exists():
        print(f"[math-forge] ERROR: File not found: {filepath}", file=sys.stderr)
        sys.exit(1)

    content = filepath.read_text()

    # Auto-detect slot from filename
    slot = args.slot
    if slot is None:
        slot_match = re.search(r'slot(\d+)', filepath.name)
        if slot_match:
            slot = int(slot_match.group(1))
        else:
            print("[math-forge] ERROR: Cannot detect slot number. Use --slot N.", file=sys.stderr)
            sys.exit(1)

    # Auto-detect problem ID from filename
    problem_id = args.problem_id
    if problem_id is None:
        # e.g., slot614_erdos_850_prime_factor_triples_result.lean -> erdos_850
        name_part = filepath.stem.replace(f'slot{slot}_', '').replace('_result', '')
        # Take first 2-3 segments as problem ID
        segments = name_part.split('_')
        if len(segments) >= 2:
            problem_id = '_'.join(segments[:3])
        else:
            problem_id = name_part

    # Resolve DB path
    db_path = args.db
    if db_path is None:
        plugin_root = Path(__file__).parent.parent
        db_path = str(plugin_root / 'data' / 'knowledge.db')

    # Ensure DB exists
    if not Path(db_path).exists():
        schema_path = Path(db_path).parent / 'schema.sql'
        if schema_path.exists():
            import subprocess
            subprocess.run(['sqlite3', db_path], stdin=open(schema_path), check=True)
            print(f"[math-forge] Created knowledge.db at {db_path}")
        else:
            # Try the math-forge schema.sql
            plugin_root = Path(__file__).parent.parent
            schema_path = plugin_root / 'data' / 'schema.sql'
            if schema_path.exists():
                import subprocess
                subprocess.run(['sqlite3', db_path], stdin=open(schema_path), check=True)
                print(f"[math-forge] Created knowledge.db at {db_path}")
            else:
                print(f"[math-forge] ERROR: DB not found and no schema.sql available", file=sys.stderr)
                sys.exit(1)

    # Extract
    extracted = extract_from_lean(content, str(filepath))
    domain = infer_domain(extracted['imports'], content)

    # Generate findings
    findings = generate_findings(extracted, slot, problem_id, domain, str(filepath))

    if not findings:
        print(f"[math-forge] No findings extracted from {filepath.name}")
        return

    # Insert
    count = insert_findings(db_path, findings)

    # Update problem record
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()

    proven_count = sum(1 for f in findings if f['finding_type'] == 'theorem' and f['confidence'] == 'verified')
    failed_count = sum(1 for f in findings if f['finding_type'] == 'failure')

    status = 'proven' if extracted['sorry_count'] == 0 and extracted['axiom_count'] == 0 else 'partial'
    if extracted['sorry_count'] > 2:
        status = 'open'

    cursor.execute("""
        INSERT INTO problems (id, name, domain_id, status, submission_count, proven_count, failed_count, statement)
        VALUES (?, ?, ?, ?, 1, ?, ?, ?)
        ON CONFLICT(id) DO UPDATE SET
            submission_count = submission_count + 1,
            proven_count = proven_count + excluded.proven_count,
            failed_count = failed_count + excluded.failed_count,
            status = CASE WHEN excluded.status = 'proven' THEN 'proven' ELSE status END,
            updated_at = datetime('now')
    """, (problem_id, problem_id, domain, status, proven_count, failed_count, ''))

    conn.commit()
    conn.close()

    print(f"[math-forge] Extracted {count} findings from slot{slot} ({filepath.name})")
    print(f"  Declarations: {len(extracted['declarations'])}")
    print(f"  Sorry: {extracted['sorry_count']} | Axioms: {extracted['axiom_count']}")
    print(f"  Domain: {domain} | Technique: {extracted['primary_technique'] or 'unknown'}")
    print(f"  Imports: {len(extracted['imports'])}")


if __name__ == '__main__':
    main()
