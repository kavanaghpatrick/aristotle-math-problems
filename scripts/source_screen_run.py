#!/usr/bin/env python3
"""
source_screen_run.py — daily Method-1 intake driver (Segment 1 of the conveyor).

Chains the four intake stages into one idempotent, cron-able sweep that
populates the ``candidate_queue`` table (the single source of truth the
Method-1 orchestrator polls via ``v_method1_ready``):

  Stage 1  SOURCE     pull every @[category research open] statement from
                      formal-conjectures/ (reuses build_open_problems_registry
                      .parse_lean_file — the permissive extractor that also
                      catches multi-line `:= by` shapes screen's strict regex
                      misses).
  Stage 2  SCREEN     class-screen each root statement (reuses
                      screen_formal_conjectures.score_open_theorem for tier +
                      snipe_classify for the S1–S8 signature and the
                      deep_structural_exclude famous-structural reject).
  Stage 3  LITERATURE fail-CLOSED biblio_gate.check_literature → literature_status
                      (CLEAR | CLOSED | AMBIGUOUS | UNKNOWN). Cards-only when
                      --skip-network; live free APIs otherwise. NEVER fabricates
                      CLEAR.
  Stage 4  RANK       composite tractability_score (snipe*0.45 + closure*0.35 +
                      neglect*0.20, per plan §2) → INSERT-OR-REPLACE candidate_queue.

The result: the orchestrator reads
    SELECT * FROM v_method1_ready
       (WHERE literature_status='CLEAR' AND deep_structural_exclude=0
        AND terminal=0 ORDER BY tractability_score DESC, prior_attempts ASC)
and is fed only easy-tail, literature-clean, ranked targets.

SAFETY: this is an INTAKE driver. It writes ONLY the new candidate_queue table
(sanctioned per the build boundary), is fully additive/idempotent
(INSERT-OR-REPLACE keyed on problem_id), and fires NO Aristotle submission.

CLI:
  python3 scripts/source_screen_run.py                 # full live sweep
  python3 scripts/source_screen_run.py --skip-network  # offline (cards only; fast)
  python3 scripts/source_screen_run.py --limit 50      # cap files (testing)
  python3 scripts/source_screen_run.py --dirs ErdosProblems Wikipedia
  python3 scripts/source_screen_run.py --dry-run       # screen + rank, NO db write
  python3 scripts/source_screen_run.py --db /tmp/x.db  # alternate DB (write tests)
  python3 scripts/source_screen_run.py --report        # just print v_method1_ready
"""
from __future__ import annotations

import argparse
import os
import re
import sqlite3
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
DB_PATH = PROJECT_ROOT / "submissions" / "tracking.db"
FC_ROOT = PROJECT_ROOT / "formal-conjectures" / "FormalConjectures"

# Make sibling modules importable (the repo's standard sys.path dance).
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))
sys.path.insert(0, str(PROJECT_ROOT / "analysis"))

# Reuse verified primitives — do NOT reinvent.
from build_open_problems_registry import (  # noqa: E402
    parse_lean_file,
    infer_domain,
    normalize_pid,
    compute_freshness,
)
from screen_formal_conjectures import (  # noqa: E402
    score_open_theorem,
    snipe_classify,
    classify_quantifiers,
)

# biblio_gate is the fail-CLOSED literature authority. Import defensively: if it
# is unavailable for any reason, the driver degrades fail-closed (every row gets
# literature_status='UNKNOWN', so nothing leaks into v_method1_ready as CLEAR).
try:
    import biblio_gate  # noqa: E402
    _HAVE_BIBLIO = True
except Exception as _e:  # pragma: no cover - defensive
    biblio_gate = None
    _HAVE_BIBLIO = False
    print(f"WARN: biblio_gate unavailable ({_e}); literature_status forced UNKNOWN",
          file=sys.stderr)

# Source directories to sweep (all research-open corpora).
DEFAULT_DIRS = [
    "ErdosProblems", "Wikipedia", "GreensOpenProblems", "OEIS",
    "Paper", "Arxiv", "Mathoverflow", "Other", "Books",
    "HilbertProblems", "Millenium", "WrittenOnTheWallII",
]

# Snipe signatures that carry a finite/decidable handle (Aristotle's sweet spot
# per advance_dna_may30.md). These get a snipe-component boost in the rank.
GOOD_SNIPES = {"S1", "S2", "S3", "S4", "S6", "S7"}
# S8 is negative-only (does not resolve the gap); NONE is no scaffold.
WEAK_SNIPES = {"S5"}            # structural-existence; harder but real
NEUTRAL_SNIPES = {"S8", "NONE"}


# ---------------------------------------------------------------------------
# Stage 1 — SOURCE
# ---------------------------------------------------------------------------
def collect_open_statements(dirs=None, limit=None):
    """Pull the root open statement per problem_id from formal-conjectures.

    Reuses the registry's permissive parser. Returns a list of dicts:
      {problem_id, file_path(abs), source_rel, theorem_name, statement,
       ams_class, domain, freshness_flag}
    Keyed to the ROOT theorem per problem_id (variants are dropped for the
    candidate_queue PK; they share literature/tractability with the root).
    """
    dirs = dirs or DEFAULT_DIRS
    targets = []
    for d in dirs:
        dpath = FC_ROOT / d
        if dpath.exists():
            targets.extend(sorted(dpath.rglob("*.lean")))
    if limit:
        targets = targets[:limit]

    by_pid = {}
    for f in targets:
        try:
            parsed = parse_lean_file(f)        # registry parser; abs path ok
        except Exception as e:                 # pragma: no cover - defensive
            print(f"WARN: parse failed on {f}: {e}", file=sys.stderr)
            continue
        for row in parsed:
            pid = row["problem_id"]
            tname = row["theorem_name"]
            # Prefer the bare root theorem (no `.variants.` / `.` suffix) as the
            # canonical statement for this problem_id.
            is_root = "." not in tname
            if pid not in by_pid:
                by_pid[pid] = (is_root, row)
            else:
                prev_root, _ = by_pid[pid]
                if is_root and not prev_root:
                    by_pid[pid] = (is_root, row)

    out = []
    for pid, (_, row) in by_pid.items():
        ams = row.get("ams_class", "")
        domain = infer_domain(row["file_path"], ams)
        freshness = compute_freshness(pid, row["theorem_name"])
        out.append({
            "problem_id": pid,
            "file_path": row["file_path"],         # relative (registry already rel)
            "theorem_name": row["theorem_name"],
            "statement": row["statement_first_line"],
            "ams_class": ams,
            "domain": domain,
            "freshness_flag": freshness,
        })
    return out


# ---------------------------------------------------------------------------
# Stage 2 — SCREEN (class + snipe + deep_structural_exclude)
# ---------------------------------------------------------------------------
def screen_statement(stmt_text):
    """Run the screen scorer + snipe tagger on a single statement.

    Returns dict {score, tier, snipe, deep_structural_exclude, reasons}.
    """
    score, reasons, tier = score_open_theorem(stmt_text)
    quant = classify_quantifiers(stmt_text)
    snipe, dse, snipe_reasons = snipe_classify(stmt_text, quant)
    # Map screen's textual tier to the integer `tier` column. Priority tiers
    # (computation/witness/falsify) get the low integers (1=best).
    tier_int = {
        "FINITE": 1, "ANSWER_UNKNOWN": 2, "WITNESS": 3, "FALSIFY": 4,
        "MIXED": 5, "INFINITE": 6, "UNKNOWN": 5, "NONE": 6,
    }.get(tier, 5)
    return {
        "score": float(score),
        "tier_text": tier,
        "tier": tier_int,
        "snipe": snipe,
        "deep_structural_exclude": dse,
        "reasons": reasons + snipe_reasons,
    }


# ---------------------------------------------------------------------------
# Stage 3 — LITERATURE (fail-closed)
# ---------------------------------------------------------------------------
_ERDOS_RE = re.compile(r"erdos[_]?(\d+)", re.IGNORECASE)

# Map kill-list / card status strings to the candidate_queue literature_status
# enum. Mirrors biblio_gate's own mapping so an exact card hit here agrees with
# what biblio_gate would have said on an exact match.
_CARD_CLOSED = {"CLOSED", "SOLVED", "DISPROVED", "RESOLVED", "AI_CLOSED",
                "RECENTLY_SOLVED", "LITERATURE_CLOSED", "COUNTEREXAMPLE_KNOWN"}
_CARD_AMBIGUOUS = {"AMBIGUOUS", "PARTIAL", "POSSIBLY_SOLVED", "POSSIBLY_SOLVED_SINCE"}


def _exact_card_status(conn, problem_id):
    """EXACT-match card lookup for a problem_id against named_conjecture_status
    and the kill-list CSV.

    This deliberately avoids biblio_gate's substring card matcher, which has a
    confirmed false-positive: problem_id='erdos_1' substring-matches the card
    'erdos_1051' (and 'erdos_11' matches 'erdos_1105_cycles'), branding
    genuinely-open low-numbered problems CLOSED. We require EXACT equality on
    either the underscore form or the digit-normalized form, so erdos_1 never
    collides with erdos_1051 while erdos_1051 itself still hits its card.

    Returns 'CLOSED' | 'AMBIGUOUS' | None (None => no exact card; fall through
    to the network gate).
    """
    if not problem_id:
        return None
    pid = problem_id.strip().lower()
    pid_compact = pid.replace("_", "")
    forms = {pid, pid_compact}

    # 1) named_conjecture_status DB table (exact name match only).
    try:
        cur = conn.execute(
            "SELECT name FROM sqlite_master WHERE type='table' "
            "AND name='named_conjecture_status'")
        if cur.fetchone():
            for name, status in conn.execute(
                    "SELECT name, status FROM named_conjecture_status"):
                nm = (name or "").strip().lower()
                if nm in forms or nm.replace("_", "") in forms:
                    st = (status or "").strip().upper()
                    if st in _CARD_CLOSED:
                        return "CLOSED"
                    if st in _CARD_AMBIGUOUS:
                        return "AMBIGUOUS"
    except sqlite3.Error:
        pass

    # 2) kill-list CSV (exact problem_id match only).
    kill_csv = PROJECT_ROOT / "analysis" / "literature_kill_list.csv"
    if kill_csv.exists():
        try:
            import csv as _csv
            with kill_csv.open() as f:
                for row in _csv.DictReader(f):
                    rpid = (row.get("problem_id") or "").strip().lower()
                    if rpid and (rpid in forms or rpid.replace("_", "") in forms):
                        st = (row.get("literature_status") or "").strip().upper()
                        if st in _CARD_CLOSED:
                            return "CLOSED"
                        if st in _CARD_AMBIGUOUS:
                            return "AMBIGUOUS"
        except (OSError, _csv.Error):
            pass
    return None


# Famous, DISTINCTIVELY-NAMED conjectures whose name is a precise zbMATH/Crossref
# query term. ONLY these get passed as named_conjecture to biblio_gate's network
# search. A bare "Erdős problem N" is deliberately NOT here: it is too generic —
# it matches any Erdős paper and produces false CLOSED verdicts (e.g. "Optimal
# Solution to Erdős Distinct Distances" branding the unrelated erdos_1 closed).
# Known closures for numbered problems are caught by the exact card pre-check
# (_exact_card_status); everything else falls back to statement-keyword search,
# which biblio_gate caps at AMBIGUOUS (never CLOSED without a named match).
_FAMOUS_NAMED = {
    "brocard": "Brocard's conjecture",
    "lehmer": "Lehmer's totient problem",
    "collatz": "Collatz conjecture",
    "goldbach": "Goldbach's conjecture",
    "twin_prime": "Twin prime conjecture",
    "riemann": "Riemann hypothesis",
    "feit_thompson": "Feit-Thompson conjecture",
    "tuza": "Tuza's conjecture",
    "herzog_schonheim": "Herzog-Schönheim conjecture",
    "casas_alvero": "Casas-Alvero conjecture",
    "vaught": "Vaught conjecture",
    "leinster": "Leinster group problem",
    "pollock": "Pollock conjecture",
}


def derive_named_conjecture(problem_id, statement):
    """Named-conjecture hint for biblio_gate recall — precise names ONLY.

    Returns a distinctive conjecture name when the problem_id/statement clearly
    corresponds to a famous named problem (these are precise network-query
    terms), else None. Returning None makes biblio_gate fall back to
    statement-keyword search, which is capped at AMBIGUOUS (never a false
    CLOSED). A generic "Erdős problem N" is NEVER emitted — see _FAMOUS_NAMED.
    """
    pid = (problem_id or "").lower()
    blob = (pid + " " + (statement or "")).lower()
    for key, name in _FAMOUS_NAMED.items():
        if key in pid or key.replace("_", " ") in blob or key.replace("_", "") in pid:
            return name
    return None


def literature_check(statement, problem_id, named, skip_network):
    """Wrap biblio_gate.check_literature with the fail-CLOSED contract.

    Any unavailability/exception -> 'UNKNOWN' (never 'CLEAR').
    """
    if not _HAVE_BIBLIO:
        return {"status": "UNKNOWN",
                "evidence": "biblio_gate unavailable (fail-closed)", "sources": []}
    try:
        return biblio_gate.check_literature(
            statement, problem_id=problem_id, named_conjecture=named,
            skip_network=skip_network,
        )
    except Exception as e:  # pragma: no cover - biblio_gate has its own backstop
        return {"status": "UNKNOWN",
                "evidence": f"biblio_gate raised {e!r} (fail-closed)", "sources": []}


# ---------------------------------------------------------------------------
# Stage 4 — RANK (composite tractability)
# ---------------------------------------------------------------------------
def tractability(screen_res, prior_attempts):
    """Composite tractability score in [0, 10], per plan §2:

        snipe*0.45 + closure*0.35 + neglect*0.20

    - snipe   : the S1–S8 scaffold strength, blended with the screen score.
    - closure : how cleanly the problem reduces to a verifiable artifact —
                proxied by the screen tier (FINITE/WITNESS/FALSIFY high).
    - neglect : under-attempted problems rank higher (Method-1 wants fresh
                targets, not the over-tried ones).
    """
    snipe = screen_res["snipe"]
    score = screen_res["score"]            # 0..10 from the screen scorer
    tier_int = screen_res["tier"]          # 1(best)..6(worst)

    # snipe component (0..10): a recognized good scaffold floors high.
    if snipe in GOOD_SNIPES:
        snipe_comp = max(score, 7.0)
    elif snipe in WEAK_SNIPES:
        snipe_comp = max(score, 5.0)
    else:                                   # S8 / NONE
        snipe_comp = min(score, 5.0)

    # closure component (0..10): low tier_int = clean closure.
    closure_comp = max(0.0, 10.0 - (tier_int - 1) * 1.8)

    # neglect component (0..10): 0 attempts -> 10; decays with attempts.
    neglect_comp = 10.0 / (1.0 + 0.5 * max(0, prior_attempts))

    val = 0.45 * snipe_comp + 0.35 * closure_comp + 0.20 * neglect_comp
    return round(max(0.0, min(10.0, val)), 3)


# ---------------------------------------------------------------------------
# DB write
# ---------------------------------------------------------------------------
CQ_COLUMNS = (
    "problem_id", "source_path", "statement", "domain", "tier",
    "snipe_signature", "deep_structural_exclude", "literature_status",
    "tractability_score", "prior_attempts", "terminal", "argument_authored",
    "created_at", "updated_at",
)


def load_prior_attempts(conn):
    """Map problem_id -> count of prior submissions (read-only on submissions)."""
    counts = {}
    try:
        cur = conn.execute(
            "SELECT problem_id, COUNT(*) FROM submissions "
            "WHERE problem_id IS NOT NULL GROUP BY problem_id"
        )
        counts = {row[0]: row[1] for row in cur.fetchall()}
    except sqlite3.Error:
        pass
    return counts


def attempts_for(pid, counts):
    n = 0
    for cand in normalize_pid(pid):
        if cand in counts:
            n = max(n, counts[cand])
    return n


def upsert_candidate(conn, row):
    """INSERT-OR-REPLACE one fully-enriched candidate_queue row, but PRESERVE
    a terminal/argument_authored flag already set by a downstream stage."""
    cur = conn.cursor()
    cur.execute("SELECT terminal, argument_authored, created_at "
                "FROM candidate_queue WHERE problem_id=?", (row["problem_id"],))
    existing = cur.fetchone()
    now = datetime.now(timezone.utc).isoformat()
    if existing:
        # Preserve downstream-owned flags + original created_at.
        terminal = existing[0] if existing[0] is not None else row["terminal"]
        arg_authored = existing[1] if existing[1] is not None else row["argument_authored"]
        created_at = existing[2] or now
    else:
        terminal = row["terminal"]
        arg_authored = row["argument_authored"]
        created_at = now

    cur.execute(
        "INSERT OR REPLACE INTO candidate_queue "
        "(problem_id, source_path, statement, domain, tier, snipe_signature, "
        " deep_structural_exclude, literature_status, tractability_score, "
        " prior_attempts, terminal, argument_authored, created_at, updated_at) "
        "VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
        (row["problem_id"], row["source_path"], row["statement"], row["domain"],
         row["tier"], row["snipe_signature"], row["deep_structural_exclude"],
         row["literature_status"], row["tractability_score"], row["prior_attempts"],
         terminal, arg_authored, created_at, now),
    )


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------
def run(db_path=None, dirs=None, limit=None, skip_network=False,
        dry_run=False, verbose=False):
    db_path = Path(db_path) if db_path else DB_PATH
    if not db_path.exists():
        print(f"ERROR: DB not found at {db_path}; run scripts/migrate_method1.py first",
              file=sys.stderr)
        return {"error": "db_missing"}

    conn = sqlite3.connect(str(db_path))
    cur = conn.execute(
        "SELECT name FROM sqlite_master WHERE type='table' AND name='candidate_queue'")
    if not cur.fetchone():
        conn.close()
        print("ERROR: candidate_queue missing; run scripts/migrate_method1.py first",
              file=sys.stderr)
        return {"error": "table_missing"}

    print(f"[1/4] SOURCE: scanning {FC_ROOT} ...")
    stmts = collect_open_statements(dirs=dirs, limit=limit)
    print(f"      collected {len(stmts)} root open statements")

    prior_counts = load_prior_attempts(conn)
    print(f"      submissions DB has prior attempts on {len(prior_counts)} problem_ids")

    stats = {
        "total": 0, "screened": 0, "deep_excluded": 0,
        "lit_CLEAR": 0, "lit_CLOSED": 0, "lit_AMBIGUOUS": 0, "lit_UNKNOWN": 0,
        "written": 0, "ready": 0,
    }
    net_calls = 0
    enriched = []

    print(f"[2/4] SCREEN + [3/4] LITERATURE ({'cards-only' if skip_network else 'live APIs'}) ...")
    for i, s in enumerate(stmts, 1):
        stats["total"] += 1
        screen_res = screen_statement(s["statement"])
        stats["screened"] += 1
        dse = screen_res["deep_structural_exclude"]
        if dse:
            stats["deep_excluded"] += 1

        # (a) EXACT card pre-check ALWAYS runs first (deterministic, no network,
        #     immune to biblio_gate's substring false-positive on short ids). A
        #     known closure is authoritative even for a deep-structural row, so
        #     the literature_status column stays accurate for the dashboard.
        card_status = _exact_card_status(conn, s["problem_id"])
        if card_status == "CLOSED":
            lit = {"status": "CLOSED",
                   "evidence": f"exact card match for {s['problem_id']}",
                   "sources": []}
        elif card_status == "AMBIGUOUS":
            lit = {"status": "AMBIGUOUS",
                   "evidence": f"exact card match for {s['problem_id']} (ambiguous)",
                   "sources": []}
        elif dse:
            # (b) No card, and class-screen already excluded it: skip the
            #     (cached) network call — it will never reach v_method1_ready
            #     regardless, and this keeps daily network volume to the
            #     genuinely-tractable set.
            lit = {"status": "UNKNOWN",
                   "evidence": "deep_structural_exclude=1; no card; literature not consulted",
                   "sources": []}
        else:
            # (c) Network gate WITHOUT problem_id — passing the short id to
            #     biblio_gate triggers its substring card matcher
            #     (erdos_1 ⊂ erdos_1051). We pass only statement + a
            #     name-form conjecture, which biblio_gate matches exactly.
            named = derive_named_conjecture(s["problem_id"], s["statement"])
            lit = literature_check(s["statement"], None, named, skip_network)
            if not skip_network and lit.get("sources"):
                net_calls += 1
        lit_status = lit.get("status", "UNKNOWN")
        stats[f"lit_{lit_status}"] = stats.get(f"lit_{lit_status}", 0) + 1

        score = tractability(screen_res, attempts_for(s["problem_id"], prior_counts))
        row = {
            "problem_id": s["problem_id"],
            "source_path": s["file_path"],
            "statement": s["statement"][:2000],
            "domain": s["domain"],
            "tier": screen_res["tier"],
            "snipe_signature": screen_res["snipe"],
            "deep_structural_exclude": dse,
            "literature_status": lit_status,
            "tractability_score": score,
            "prior_attempts": attempts_for(s["problem_id"], prior_counts),
            "terminal": 0,
            "argument_authored": 0,
        }
        enriched.append(row)
        if verbose and (i % 100 == 0 or i == len(stmts)):
            print(f"      .. {i}/{len(stmts)} screened "
                  f"({net_calls} live literature calls)")

    enriched.sort(key=lambda r: (-r["tractability_score"], r["prior_attempts"]))

    if dry_run:
        print("[4/4] RANK: --dry-run set; NOT writing candidate_queue.")
    else:
        print("[4/4] RANK + WRITE: INSERT-OR-REPLACE into candidate_queue ...")
        for row in enriched:
            upsert_candidate(conn, row)
            stats["written"] += 1
        conn.commit()

    # Final view read.
    try:
        stats["ready"] = conn.execute("SELECT COUNT(*) FROM v_method1_ready").fetchone()[0]
        cq_total = conn.execute("SELECT COUNT(*) FROM candidate_queue").fetchone()[0]
    except sqlite3.Error:
        cq_total = 0
    conn.close()

    print("\n=== INTAKE SUMMARY ===")
    print(f"  statements screened       : {stats['screened']}")
    print(f"  deep_structural_exclude=1 : {stats['deep_excluded']}")
    print(f"  literature CLEAR          : {stats['lit_CLEAR']}")
    print(f"  literature CLOSED         : {stats['lit_CLOSED']}")
    print(f"  literature AMBIGUOUS      : {stats['lit_AMBIGUOUS']}")
    print(f"  literature UNKNOWN        : {stats['lit_UNKNOWN']}")
    print(f"  live literature calls     : {net_calls}")
    print(f"  rows written              : {stats['written']}")
    print(f"  candidate_queue total     : {cq_total}")
    print(f"  v_method1_ready rows      : {stats['ready']}")
    stats["candidate_queue_total"] = cq_total
    stats["enriched"] = enriched
    return stats


def print_ready(db_path=None, top=25):
    db_path = Path(db_path) if db_path else DB_PATH
    if not db_path.exists():
        print(f"ERROR: DB not found at {db_path}", file=sys.stderr)
        return
    conn = sqlite3.connect(str(db_path))
    try:
        n = conn.execute("SELECT COUNT(*) FROM v_method1_ready").fetchone()[0]
    except sqlite3.Error as e:
        print(f"ERROR: {e}", file=sys.stderr)
        conn.close()
        return
    print(f"v_method1_ready: {n} rows (showing top {top})")
    print(f"{'problem_id':<28} {'snipe':<6} {'tier':<5} {'tract':<7} {'attempts':<9} domain")
    print("-" * 80)
    rows = conn.execute(
        "SELECT problem_id, snipe_signature, tier, tractability_score, "
        "prior_attempts, domain FROM v_method1_ready LIMIT ?", (top,)
    ).fetchall()
    for r in rows:
        pid, snipe, tier, tract, att, dom = r
        print(f"{(pid or '')[:27]:<28} {(snipe or '?'):<6} "
              f"{tier if tier is not None else '?':<5} "
              f"{tract if tract is not None else '?':<7} {att:<9} {dom or ''}")
    conn.close()


def main():
    ap = argparse.ArgumentParser(
        description="Daily Method-1 intake: source -> screen -> biblio_gate -> "
                    "rank -> candidate_queue (idempotent, additive).")
    ap.add_argument("--db", default=str(DB_PATH), help="tracking DB path")
    ap.add_argument("--dirs", nargs="*", default=None,
                    help="formal-conjectures subdirs to sweep (default: all)")
    ap.add_argument("--limit", type=int, default=None,
                    help="cap number of .lean files (testing)")
    ap.add_argument("--skip-network", action="store_true",
                    help="cards/kill-list only literature check (offline, fast); "
                         "no row will be CLEAR unless a card says so — fail-closed")
    ap.add_argument("--dry-run", action="store_true",
                    help="screen + rank but DO NOT write candidate_queue")
    ap.add_argument("--report", action="store_true",
                    help="just print the current v_method1_ready and exit")
    ap.add_argument("--top", type=int, default=25, help="rows to show in report")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()

    if args.report:
        print_ready(db_path=args.db, top=args.top)
        return

    run(db_path=args.db, dirs=args.dirs, limit=args.limit,
        skip_network=args.skip_network, dry_run=args.dry_run, verbose=args.verbose)

    if not args.dry_run:
        print()
        print_ready(db_path=args.db, top=args.top)


if __name__ == "__main__":
    main()
