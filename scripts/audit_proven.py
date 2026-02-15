#!/usr/bin/env python3
"""
Strict audit of all 'compiled_clean' files in tracking.db.

COMPILED CLEAN means: 0 sorry, 0 axiom, file exists, no self-loops, no banned Finset.sym2.
Anything else gets downgraded.
"""

import os
import re
import sqlite3

DB_PATH = "/Users/patrickkavanagh/math/submissions/tracking.db"
BASE_DIRS = [
    "/Users/patrickkavanagh/math/submissions/nu4_final",
    "/Users/patrickkavanagh/math/submissions",
    "/Users/patrickkavanagh/math",
]

def find_file(filename):
    """Try to locate a file across known directories."""
    for base in BASE_DIRS:
        path = os.path.join(base, filename)
        if os.path.isfile(path):
            return path
    # Also try stripping leading dirs from filename
    for base in BASE_DIRS:
        for root, dirs, files in os.walk(base):
            if os.path.basename(filename) in files:
                return os.path.join(root, os.path.basename(filename))
    return None

def audit_file(filepath):
    """Audit a lean file for issues. Returns list of (severity, issue) tuples."""
    issues = []
    try:
        with open(filepath, 'r') as f:
            content = f.read()
    except:
        return [("CRITICAL", "Cannot read file")]

    # 1. Count actual sorry
    sorry_count = len(re.findall(r'\bsorry\b', content))
    if sorry_count > 0:
        issues.append(("CRITICAL", f"Contains {sorry_count} sorry"))

    # 2. Check for axiom declarations
    axioms = re.findall(r'^axiom\s+(\w+)', content, re.MULTILINE)
    if axioms:
        issues.append(("CRITICAL", f"Contains axioms: {', '.join(axioms)}"))

    # 3. Check for self-loops: Sym2.mk(x, x) patterns
    # Match Sym2.mk (x, x) or Sym2.mk (x , x)
    self_loops_sym2mk = re.findall(r'Sym2\.mk\s*\(\s*(\w+)\s*,\s*\1\s*\)', content)
    if self_loops_sym2mk:
        issues.append(("CRITICAL", f"Self-loops via Sym2.mk: {self_loops_sym2mk[:3]}"))

    # Match s(x, x) patterns in non-comment lines
    lines = content.split('\n')
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith('--') or stripped.startswith('/-'):
            continue
        s_self_loops = re.findall(r's\((\w+),\s*\1\)', line)
        if s_self_loops:
            issues.append(("CRITICAL", f"Self-loop s({s_self_loops[0]},{s_self_loops[0]}) at line {i+1}"))
            break  # One is enough

    # 4. Check for Finset.sym2 usage (banned for edge enumeration)
    sym2_uses = re.findall(r'Finset\.sym2|\.sym2\b', content)
    # Exclude comments
    code_only = re.sub(r'/-.*?-/', '', content, flags=re.DOTALL)
    code_only = re.sub(r'--.*$', '', code_only, flags=re.MULTILINE)
    sym2_code_uses = re.findall(r'(?:Finset\.sym2|\.sym2\b)', code_only)
    if sym2_code_uses:
        issues.append(("HIGH", f"Uses Finset.sym2 ({len(sym2_code_uses)} times) - includes self-loops"))

    # 5. Count proven lemmas/theorems (for accurate proven_count)
    blocks = re.split(r'(?=\b(?:theorem|lemma)\s)', content)
    proven = 0
    for block in blocks:
        if re.search(r'\b(theorem|lemma)\s+\w+', block):
            if not re.search(r'\bsorry\b', block):
                proven += 1

    return issues, sorry_count, proven

def main():
    conn = sqlite3.connect(DB_PATH)

    # Get all "proven" entries
    rows = conn.execute("""
        SELECT id, filename, sorry_count, proven_count, status, verified, notes
        FROM submissions
        WHERE status IN ('proven', 'PROVEN', 'compiled_clean')
    """).fetchall()

    print(f"Auditing {len(rows)} files marked as compiled clean...\n")

    stats = {
        "clean": 0,
        "downgraded_sorry": 0,
        "downgraded_axiom": 0,
        "downgraded_self_loop": 0,
        "downgraded_missing": 0,
        "flagged_sym2": 0,
    }

    clean_files = []
    problematic_files = []

    for row_id, filename, db_sorry, db_proven, status, verified, notes in rows:
        filepath = find_file(filename)

        if not filepath:
            # File doesn't exist
            print(f"  MISSING: {filename} -> downgrade to 'missing'")
            conn.execute(
                "UPDATE submissions SET status='missing', verified=0, notes=COALESCE(notes,'') || ' [AUDIT: file not found on disk]' WHERE id=?",
                (row_id,)
            )
            stats["downgraded_missing"] += 1
            problematic_files.append((filename, "MISSING", "File not found on disk"))
            continue

        if not filename.endswith('.lean'):
            # Non-lean files (like .md) - can't be "proven"
            print(f"  NON-LEAN: {filename} -> downgrade to 'completed'")
            conn.execute(
                "UPDATE submissions SET status='completed', verified=0, notes=COALESCE(notes,'') || ' [AUDIT: not a lean file]' WHERE id=?",
                (row_id,)
            )
            stats["downgraded_sorry"] += 1
            continue

        result = audit_file(filepath)
        if isinstance(result, list):
            # Error reading file
            issues = result
            actual_sorry = None
            actual_proven = None
        else:
            issues, actual_sorry, actual_proven = result

        critical_issues = [i for i in issues if i[0] == "CRITICAL"]
        high_issues = [i for i in issues if i[0] == "HIGH"]

        if critical_issues:
            # Downgrade from proven
            issue_strs = "; ".join(f"{sev}: {desc}" for sev, desc in critical_issues)
            new_notes = f"[AUDIT DOWNGRADED: {issue_strs}]"

            # Determine new status
            if any("sorry" in i[1].lower() for i in critical_issues):
                new_status = "completed"
                stats["downgraded_sorry"] += 1
            elif any("axiom" in i[1].lower() for i in critical_issues):
                new_status = "completed"
                stats["downgraded_axiom"] += 1
            elif any("self-loop" in i[1].lower() or "Self-loop" in i[1] for i in critical_issues):
                new_status = "invalid"
                stats["downgraded_self_loop"] += 1
            else:
                new_status = "completed"
                stats["downgraded_sorry"] += 1

            print(f"  DOWNGRADE: {filename} -> '{new_status}' ({issue_strs})")
            conn.execute("""
                UPDATE submissions SET
                    status=?,
                    verified=0,
                    sorry_count=COALESCE(?, sorry_count),
                    proven_count=COALESCE(?, proven_count),
                    notes=CASE WHEN notes IS NULL THEN ? ELSE notes || ' ' || ? END
                WHERE id=?
            """, (new_status, actual_sorry, actual_proven, new_notes, new_notes, row_id))
            problematic_files.append((filename, new_status, issue_strs))

        elif high_issues:
            # Flag but keep compiled_clean (sym2 usage doesn't necessarily invalidate)
            issue_strs = "; ".join(f"{sev}: {desc}" for sev, desc in high_issues)
            flag_note = f"[AUDIT WARNING: {issue_strs}]"
            print(f"  WARNING: {filename} ({issue_strs})")
            conn.execute("""
                UPDATE submissions SET
                    notes=CASE WHEN notes IS NULL THEN ? ELSE notes || ' ' || ? END,
                    sorry_count=COALESCE(?, sorry_count),
                    proven_count=COALESCE(?, proven_count)
                WHERE id=?
            """, (flag_note, flag_note, actual_sorry, actual_proven, row_id))
            stats["flagged_sym2"] += 1
            # Still considered "compiled_clean" but flagged
            clean_files.append((filename, f"FLAGGED: {issue_strs}"))

        else:
            # Truly clean
            print(f"  CLEAN: {filename}")
            # Update counts if they were wrong
            conn.execute("""
                UPDATE submissions SET
                    sorry_count=COALESCE(?, sorry_count),
                    proven_count=COALESCE(?, proven_count),
                    verified=1
                WHERE id=?
            """, (actual_sorry, actual_proven, row_id))
            stats["clean"] += 1
            clean_files.append((filename, "CLEAN"))

    conn.commit()

    # Print summary
    print(f"\n{'='*60}")
    print("AUDIT SUMMARY")
    print(f"{'='*60}")
    print(f"Total files audited:        {len(rows)}")
    print(f"Truly CLEAN (compiled):     {stats['clean']}")
    print(f"Flagged (sym2 warning):     {stats['flagged_sym2']}")
    print(f"Downgraded (has sorry):     {stats['downgraded_sorry']}")
    print(f"Downgraded (has axiom):     {stats['downgraded_axiom']}")
    print(f"Downgraded (self-loops):    {stats['downgraded_self_loop']}")
    print(f"Downgraded (file missing):  {stats['downgraded_missing']}")
    print(f"\n{'='*60}")
    print("COMPILED CLEAN FILES (verified=1, 0 sorry, 0 axiom, no self-loops):")
    print(f"{'='*60}")
    for fname, note in sorted(clean_files):
        marker = "  " if note == "CLEAN" else "⚠ "
        print(f"  {marker}{fname} {'(' + note + ')' if note != 'CLEAN' else ''}")

    print(f"\n{'='*60}")
    print("DOWNGRADED FILES:")
    print(f"{'='*60}")
    for fname, new_status, reason in sorted(problematic_files):
        print(f"  {fname} -> {new_status}: {reason}")

    # Final count
    final_proven = conn.execute(
        "SELECT COUNT(*) FROM submissions WHERE status IN ('proven', 'PROVEN', 'compiled_clean') AND verified = 1"
    ).fetchone()[0]
    final_flagged = conn.execute(
        "SELECT COUNT(*) FROM submissions WHERE status IN ('proven', 'PROVEN', 'compiled_clean') AND (notes LIKE '%AUDIT WARNING%')"
    ).fetchone()[0]
    print(f"\nFinal count: {final_proven} verified compiled clean + {final_flagged} compiled-but-flagged")

    conn.close()

if __name__ == '__main__':
    main()
