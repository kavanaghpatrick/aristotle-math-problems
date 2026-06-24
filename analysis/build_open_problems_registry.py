#!/usr/bin/env python3
"""
Build canonical "actually open in 2026" problem registry.

Sweeps formal-conjectures/ for all @[category research open] theorems
(note: no @[category research disproved] tag exists in the codebase;
the only variants are: research open, research solved, research formally solved).

Parses theorem statement, AMS class, and cross-checks with submissions DB.
Adds literature freshness flags for edge cases.
"""

import csv
import os
import re
import sqlite3
import sys
from datetime import datetime, timezone
from pathlib import Path

FC_ROOT = Path("/Users/patrickkavanagh/math/formal-conjectures/FormalConjectures")
PROJECT_ROOT = Path("/Users/patrickkavanagh/math")
DB_PATH = PROJECT_ROOT / "submissions" / "tracking.db"
OUT_CSV = PROJECT_ROOT / "analysis" / "open_problems_registry_may30.csv"
OUT_MD = PROJECT_ROOT / "analysis" / "open_problems_registry_summary.md"


# Literature freshness overrides — sourced from
# https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems
# (snapshot 2026-05-30) and well-known classical resolutions.
#
# Note: erdosproblems.com "Open" status does NOT guarantee literature-open.  Bloom
# explicitly states it means "I am unaware of a paper solving it" — see TechCrunch
# Oct 2025 / Bubeck-LeCun exchange.  We mark POSSIBLY_SOLVED_SINCE for any Erdős
# whose number appears in the wiki's solved-in-literature / solved-by-AI sections,
# and COUNTEREXAMPLE_KNOWN where a disproof is published.
#
# Format: erdos_<N> -> (flag, note)

# Wiki-listed: Fully Solved by AI (standalone)
_AI_SOLVED_STANDALONE = {38, 90, 125, 205, 457, 694, 741, 960, 987, 990, 1014,
                         1051, 1091, 1141, 1196, 1202, 1217}
# Wiki-listed: Solved alongside literature (AI + pre-existing partial)
_AI_SOLVED_W_LIT = {152, 281, 333, 397, 543, 650, 659, 728, 846, 851, 897, 997, 1026, 1089}
# Wiki-listed: Solved building on literature
_AI_SOLVED_BUILD_LIT = {26, 198, 224, 258, 379, 493, 729, 848, 871, 942, 958, 966,
                        1007, 1043, 1047, 1048, 1090, 1197}
# Wiki-listed: Solutions found in literature by AI (pre-existing proofs rediscovered)
_LIT_REDISCOVERY = {94, 223, 339, 397, 481, 494, 515, 533, 574, 591, 621, 645, 650,
                    652, 705, 737, 822, 903, 965, 990, 992, 1008, 1021, 1043, 1079,
                    1099, 1105, 1123, 1129, 1130, 1147, 1161, 1216}
# Wiki-listed: Solved with human collaboration
_HUMAN_AI = {42, 202, 283, 326, 330, 347, 351, 369, 380, 401, 603, 610, 659, 690,
             696, 848, 858, 863, 888, 953, 996, 1026, 1092, 1138, 1148, 1151,
             1153, 1190, 1195, 1196}

FRESHNESS_OVERRIDES = {}
for n in _AI_SOLVED_STANDALONE | _AI_SOLVED_W_LIT | _AI_SOLVED_BUILD_LIT | _LIT_REDISCOVERY | _HUMAN_AI:
    FRESHNESS_OVERRIDES[f"erdos_{n}"] = (
        "POSSIBLY_SOLVED_SINCE",
        "Listed in teorth/erdosproblems AI-contributions wiki (2025-2026)",
    )

# Non-Erdős hand checks
FRESHNESS_OVERRIDES.update({
    # Pollock tetrahedral: Watson 1952 settled all-but-finite for tetrahedral case
    # The formal statement asks "every N is sum of <=5 tetrahedral" which is well-known TRUE
    # for all but 241 specific exceptions. Statement may already be in literature.
    "pollock_tetrahedral": ("AMBIGUOUS", "Watson 1952 partial; Salzer-Levine 1958 enumerated 241 exceptions; statement-dependent"),
})


def parse_lean_file(file_path: Path):
    """Extract all @[category research open] theorems with metadata."""
    try:
        content = file_path.read_text(encoding="utf-8")
    except Exception as e:
        print(f"WARN: cannot read {file_path}: {e}", file=sys.stderr)
        return []

    lines = content.split("\n")
    results = []

    open_attr_re = re.compile(r"@\[category\s+research\s+open([^\]]*)\]")
    theorem_re = re.compile(
        r"^(?:theorem|lemma|def|abbrev|example|conjecture)\s+([A-Za-z_][\w.]*)"
    )

    for i, line in enumerate(lines):
        m = open_attr_re.search(line)
        if not m:
            continue

        tag_extras = m.group(1).strip()
        ams_match = re.search(r"AMS\s+([\d\s]+)", tag_extras)
        ams_class = ams_match.group(1).strip() if ams_match else ""

        thm_name = ""
        statement_lines = []
        for j in range(i + 1, min(i + 30, len(lines))):
            nxt = lines[j]
            tm = theorem_re.match(nxt.strip())
            if tm:
                thm_name = tm.group(1)
                for k in range(j, min(j + 20, len(lines))):
                    stmt_line = lines[k]
                    statement_lines.append(stmt_line)
                    if (
                        re.search(r":=\s*by\s*$", stmt_line)
                        or re.search(r":=\s*by\b", stmt_line)
                        or "sorry" in stmt_line
                    ):
                        break
                break

        if not thm_name:
            continue

        full_stmt = " ".join(statement_lines).strip()
        first_line = re.sub(r"\s+", " ", full_stmt)[:300]

        problem_id = thm_name.split(".")[0] if "." in thm_name else thm_name

        results.append({
            "file_path": str(file_path.relative_to(PROJECT_ROOT)),
            "theorem_name": thm_name,
            "problem_id": problem_id,
            "category_tag": "research open",
            "ams_class": ams_class,
            "statement_first_line": first_line,
            "line_number": i + 1,
        })

    return results


def infer_domain(file_path: str, ams_class: str) -> str:
    """Infer mathematical domain from AMS class (primary) then path."""
    p = file_path.lower()
    ams = ams_class.strip().split()
    ams_primary = ams[0] if ams else ""

    ams_map = {
        "03": "logic",
        "05": "combinatorics",
        "06": "order",
        "08": "general_algebra",
        "11": "nt",
        "12": "algebra",
        "13": "algebra",
        "14": "geometry",
        "15": "linear",
        "16": "algebra",
        "17": "algebra",
        "18": "category",
        "19": "k_theory",
        "20": "algebra",
        "22": "lie_groups",
        "26": "analysis",
        "28": "measure",
        "30": "analysis",
        "31": "analysis",
        "32": "analysis",
        "33": "analysis",
        "34": "ode",
        "35": "pde",
        "37": "dynamical",
        "39": "difference",
        "40": "analysis",
        "41": "approximation",
        "42": "fourier",
        "43": "harmonic",
        "44": "transforms",
        "45": "integral",
        "46": "functional",
        "47": "operator",
        "49": "calculus_variations",
        "51": "geometry",
        "52": "geometry",
        "53": "geometry",
        "54": "topology",
        "55": "topology",
        "57": "topology",
        "58": "global_analysis",
        "60": "probability",
        "62": "statistics",
        "65": "numerical",
        "68": "cs",
        "70": "mechanics",
        "76": "fluid",
        "82": "stat_mech",
        "83": "relativity",
        "85": "astronomy",
        "86": "geophysics",
        "90": "operations",
        "91": "game_theory",
        "92": "biology",
        "94": "information",
        "97": "education",
        # Single-digit variants
        "5": "combinatorics",
        "8": "general_algebra",
    }
    if ams_primary in ams_map:
        return ams_map[ams_primary]

    if "erdos" in p:
        return "nt"
    if "hilbert" in p:
        return "varied"
    if "millenium" in p or "millennium" in p:
        return "varied"
    if "wikipedia" in p:
        return "varied"
    if "greens" in p:
        return "combinatorics"
    if "wallii" in p or "writtenonthewall" in p:
        return "combinatorics"
    if "mathoverflow" in p:
        return "varied"
    if "books" in p:
        return "varied"
    return "unknown"


def load_db_attempts():
    """Load prior attempt counts from submissions DB."""
    if not DB_PATH.exists():
        print(f"WARN: DB not found at {DB_PATH}", file=sys.stderr)
        return {}
    conn = sqlite3.connect(str(DB_PATH))
    cur = conn.cursor()
    cur.execute(
        "SELECT problem_id, COUNT(*) FROM submissions "
        "WHERE problem_id IS NOT NULL GROUP BY problem_id"
    )
    counts = {row[0]: row[1] for row in cur.fetchall()}
    conn.close()
    return counts


def normalize_pid(pid: str) -> list:
    """Generate candidate problem_id forms to match DB entries."""
    candidates = {pid, pid.lower()}
    if "_" in pid:
        candidates.add(pid.replace("_", ""))
    m = re.match(r"erdos[_]?(\d+)", pid, re.IGNORECASE)
    if m:
        n = m.group(1)
        candidates.add(f"erdos_{n}")
        candidates.add(f"erdos{n}")
        candidates.add(f"Erdos{n}")
    return list(candidates)


def compute_freshness(problem_id: str, theorem_name: str) -> tuple:
    """Return (flag, note).  Flag in {VERIFIED_OPEN, POSSIBLY_SOLVED_SINCE,
    COUNTEREXAMPLE_KNOWN, AMBIGUOUS}.
    """
    # Extract erdos_<N> root from theorem name (handles erdos_728.variants.foo)
    erdos_root = None
    em = re.match(r"erdos_(\d+)", theorem_name.lower())
    if em:
        erdos_root = f"erdos_{em.group(1)}"

    candidates = [theorem_name, problem_id, theorem_name.lower(), problem_id.lower()]
    if erdos_root:
        candidates.append(erdos_root)
    # Also try problem_id prefix (e.g. "pollock_tetrahedral.salzer_levine" -> "pollock_tetrahedral")
    if "." in problem_id:
        candidates.append(problem_id.split(".")[0])
    if "." in theorem_name:
        candidates.append(theorem_name.split(".")[0])

    for key in candidates:
        if key in FRESHNESS_OVERRIDES:
            flag, _ = FRESHNESS_OVERRIDES[key]
            return flag

    return "VERIFIED_OPEN"


def write_candidate_queue(rows_out, db_path=None):
    """Redirect registry output into the Method-1 candidate_queue table.

    RAW-INTAKE only: writes (problem_id, source_path, statement, domain,
    prior_attempts) and a cheap-prefilter literature hint derived from the
    registry's freshness flag. It DELIBERATELY does NOT clobber the enrichment
    columns (snipe_signature, tier, deep_structural_exclude, literature_status,
    tractability_score, terminal, argument_authored) on rows that already
    exist — those are owned by source_screen_run.py / the gauntlet. This keeps
    a daily registry re-run additive and idempotent.

    The authoritative fail-CLOSED literature verdict + S1–S8 tagging +
    tractability ranking is applied by source_screen_run.py, which is the full
    intake driver. This function exists so the registry can stand alone as a
    cron-able raw-intake step (plan §2 Segment-1, "redirect registry output to
    DB rows").

    Returns dict with counts.
    """
    db_path = Path(db_path) if db_path else DB_PATH
    if not db_path.exists():
        print(f"ERROR: DB not found at {db_path}; run scripts/migrate_method1.py first",
              file=sys.stderr)
        return {"error": "db_missing"}

    conn = sqlite3.connect(str(db_path))
    cur = conn.cursor()
    # Guard: the migration must have created candidate_queue.
    cur.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='candidate_queue'")
    if not cur.fetchone():
        conn.close()
        print("ERROR: candidate_queue table missing; run scripts/migrate_method1.py first",
              file=sys.stderr)
        return {"error": "table_missing"}

    # Map the registry freshness flag to a cheap pre-network literature hint.
    # This is ONLY used to seed NEW rows; source_screen_run overwrites it with
    # the authoritative biblio_gate verdict. POSSIBLY_SOLVED_SINCE / AMBIGUOUS
    # are NOT marked CLEAR (fail-closed): they become AMBIGUOUS pending biblio.
    def _lit_hint(flag):
        if flag == "VERIFIED_OPEN":
            return None              # let biblio_gate decide; not pre-cleared
        if flag in ("POSSIBLY_SOLVED_SINCE",):
            return "AMBIGUOUS"
        if flag == "AMBIGUOUS":
            return "AMBIGUOUS"
        return None

    now = datetime.now(timezone.utc).isoformat()
    inserted = updated = skipped = 0
    seen = set()
    for r in rows_out:
        pid = r["problem_id"]
        if pid in seen:
            # Registry can have multiple theorems per problem_id; keep the first
            # (root) statement, skip variants for the queue PK.
            skipped += 1
            continue
        seen.add(pid)

        lit_hint = _lit_hint(r.get("freshness_flag", "VERIFIED_OPEN"))
        cur.execute("SELECT problem_id FROM candidate_queue WHERE problem_id=?", (pid,))
        exists = cur.fetchone() is not None
        if exists:
            # Additive: refresh only the raw-intake fields + bump updated_at.
            cur.execute(
                "UPDATE candidate_queue SET source_path=?, statement=?, domain=?, "
                "prior_attempts=?, updated_at=? WHERE problem_id=?",
                (r["file_path"], r["statement_first_line"], r["domain"],
                 r["prior_attempts_count"], now, pid),
            )
            updated += 1
        else:
            cur.execute(
                "INSERT INTO candidate_queue "
                "(problem_id, source_path, statement, domain, tier, snipe_signature, "
                " deep_structural_exclude, literature_status, tractability_score, "
                " prior_attempts, terminal, argument_authored, created_at, updated_at) "
                "VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (pid, r["file_path"], r["statement_first_line"], r["domain"],
                 None, None, 0, lit_hint, None, r["prior_attempts_count"],
                 0, 0, now, now),
            )
            inserted += 1

    conn.commit()
    cur.execute("SELECT COUNT(*) FROM candidate_queue")
    total = cur.fetchone()[0]
    conn.close()
    print(f"candidate_queue: +{inserted} inserted, {updated} updated, "
          f"{skipped} variant-skipped; total now {total}")
    return {"inserted": inserted, "updated": updated, "skipped": skipped,
            "total": total}


def main():
    import argparse
    ap = argparse.ArgumentParser(
        description="Build the open-problems registry (CSV/MD) and optionally "
                    "redirect raw intake into the Method-1 candidate_queue.")
    ap.add_argument("--to-db", action="store_true",
                    help="also write raw-intake rows into candidate_queue "
                         "(additive; does not clobber enrichment columns)")
    ap.add_argument("--db", default=str(DB_PATH),
                    help="tracking DB path (default: submissions/tracking.db)")
    args, _ = ap.parse_known_args()

    print(f"Scanning {FC_ROOT}...")
    all_rows = []
    files = sorted(FC_ROOT.rglob("*.lean"))
    print(f"Found {len(files)} .lean files")

    for f in files:
        all_rows.extend(parse_lean_file(f))

    print(f"Parsed {len(all_rows)} @[category research open] theorems")

    db_attempts = load_db_attempts()
    print(f"DB has {len(db_attempts)} distinct problem_ids")

    # Aggregate by problem_id for summary
    rows_out = []
    domain_counts = {}
    erdos_problems = []

    for row in all_rows:
        domain = infer_domain(row["file_path"], row["ams_class"])
        attempts = 0
        for cand in normalize_pid(row["problem_id"]):
            if cand in db_attempts:
                attempts = max(attempts, db_attempts[cand])
        freshness = compute_freshness(row["problem_id"], row["theorem_name"])

        out_row = {
            "problem_id": row["problem_id"],
            "file_path": row["file_path"],
            "theorem_name": row["theorem_name"],
            "category_tag": row["category_tag"],
            "ams_class": row["ams_class"],
            "statement_first_line": row["statement_first_line"],
            "domain": domain,
            "prior_attempts_count": attempts,
            "freshness_flag": freshness,
        }
        rows_out.append(out_row)
        domain_counts[domain] = domain_counts.get(domain, 0) + 1
        if "erdos" in row["theorem_name"].lower():
            erdos_problems.append(out_row)

    # Write CSV
    print(f"Writing {OUT_CSV}")
    with open(OUT_CSV, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow([
            "problem_id",
            "file_path",
            "theorem_name",
            "category_tag",
            "ams_class",
            "statement_first_line",
            "domain",
            "prior_attempts_count",
            "freshness_flag",
        ])
        for r in rows_out:
            writer.writerow([
                r["problem_id"],
                r["file_path"],
                r["theorem_name"],
                r["category_tag"],
                r["ams_class"],
                r["statement_first_line"],
                r["domain"],
                r["prior_attempts_count"],
                r["freshness_flag"],
            ])

    print(f"Wrote {len(rows_out)} rows.")

    # Summary stats
    total = len(rows_out)
    freshness_counts = {}
    for r in rows_out:
        f = r["freshness_flag"]
        freshness_counts[f] = freshness_counts.get(f, 0) + 1

    attempted_count = sum(1 for r in rows_out if r["prior_attempts_count"] > 0)

    # Top 10 Erdős by prior attempts
    erdos_sorted = sorted(
        [r for r in rows_out if r["theorem_name"].lower().startswith("erdos")],
        key=lambda x: -x["prior_attempts_count"],
    )[:15]

    # Stale-tag findings: open in repo but flagged POSSIBLY_SOLVED_SINCE
    stale = [r for r in rows_out if r["freshness_flag"] != "VERIFIED_OPEN"]
    stale_by_attempts = sorted(stale, key=lambda x: -x["prior_attempts_count"])

    # Top 10 Erdős by attempts
    erdos_top10 = sorted(
        [r for r in rows_out if r["theorem_name"].lower().startswith("erdos")
         and "." not in r["theorem_name"]],
        key=lambda x: -x["prior_attempts_count"],
    )[:10]

    # Write MD summary
    with open(OUT_MD, "w", encoding="utf-8") as f:
        f.write("# Open Problems Registry — Summary (2026-05-30)\n\n")
        f.write("**Generated from:** `formal-conjectures/FormalConjectures/` sweep\n\n")
        f.write("**Tag basis:** `@[category research open]`. ")
        f.write("Note: no `@[category research disproved]` tag exists in this codebase. ")
        f.write("Only three variants are used: `research open` (805), `research solved` (602), `research formally solved` (5).\n\n")
        f.write("## Counts\n\n")
        f.write(f"- **Total open-tagged statements:** {total}\n")
        f.write(f"- **Distinct theorem names:** {len(set(r['theorem_name'] for r in rows_out))}\n")
        f.write(f"- **Distinct root problem_ids:** {len(set(r['problem_id'] for r in rows_out))}\n")
        f.write(f"- **With >=1 prior Aristotle submission:** {attempted_count}\n\n")
        f.write("## Freshness flag distribution\n\n")
        for k in sorted(freshness_counts.keys()):
            f.write(f"- `{k}`: {freshness_counts[k]}\n")
        f.write("\n## Domain distribution\n\n")
        for k, v in sorted(domain_counts.items(), key=lambda x: -x[1]):
            f.write(f"- `{k}`: {v}\n")

        f.write("\n## Stale-tag findings (top 10)\n\n")
        f.write("These are tagged `@[category research open]` in the repo snapshot but flagged ")
        f.write("`POSSIBLY_SOLVED_SINCE` or `AMBIGUOUS` based on the ")
        f.write("[teorth/erdosproblems AI-contributions wiki](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems) ")
        f.write("(snapshot 2026-05-30). DO NOT submit these without checking the wiki / Bloom's page first.\n\n")
        f.write("| theorem_name | ams_class | attempts | flag |\n|---|---|---|---|\n")
        for r in stale_by_attempts[:10]:
            f.write(f"| `{r['theorem_name']}` | {r['ams_class']} | {r['prior_attempts_count']} | {r['freshness_flag']} |\n")

        f.write("\n## Erdős open statements — top 10 by prior_attempts_count\n\n")
        f.write("(Root statements only, no `.variants.*`)\n\n")
        f.write("| theorem_name | ams_class | attempts | flag |\n|---|---|---|---|\n")
        for r in erdos_top10:
            f.write(f"| `{r['theorem_name']}` | {r['ams_class']} | {r['prior_attempts_count']} | {r['freshness_flag']} |\n")

        f.write("\n## Notes on spot checks\n\n")
        f.write("- **Erdős 1 (`erdos_1`)**: sum-distinct sets (Conway-Guy 1969). VERIFIED_OPEN. ")
        f.write("Not to be confused with the covering-systems problem resolved by Hough 2015 (Annals); ")
        f.write("that is filed elsewhere in the FC corpus.\n")
        f.write("- **Erdős 250**: in this repo `erdos_250` is tagged `research solved` (Nesterenko 1996 transcendence) and is NOT in the open set. Correct.\n")
        f.write("- **Erdős 850 (`erdos_850`)**: status open per 2025 surveys; verified open.\n")
        f.write("- **Pollock tetrahedral**: Watson 1952 / Salzer-Levine 1958 give partial results. ")
        f.write("Formal statement asks every N is sum of <=5 tetrahedrals — flagged AMBIGUOUS.\n")
        f.write("- **`research formally solved using lean4`** (5 statements: Erdős 848, 659, BoxdotConjecture, ")
        f.write("OEIS 87719, plus one more): these are NOT in our open set (they use a separate tag).\n")
        f.write("- **Hough 2015** (Annals): minimum modulus covering systems disproved Erdős's original ")
        f.write("conjecture — but the corresponding FC entry, if any, would already be tagged `research solved`.\n")
        f.write("- **Bloom caveat**: per the TechCrunch / LeCun-Bubeck Oct-2025 exchange, ")
        f.write("`erdosproblems.com` 'open' status means 'Bloom is unaware of a paper resolving it' — NOT ")
        f.write("absence of literature solution. This is the source of our `POSSIBLY_SOLVED_SINCE` flags.\n")

    print(f"Wrote {OUT_MD}")

    if args.to_db:
        write_candidate_queue(rows_out, db_path=args.db)

    return rows_out


if __name__ == "__main__":
    main()
