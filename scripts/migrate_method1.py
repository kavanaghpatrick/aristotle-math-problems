#!/usr/bin/env python3
"""Schema migration: Method-1 / Recipe-B scale-up foundations.

This is the FOUNDATIONS migration for the Method-1 conveyor (per
`analysis/method1_scaleup_plan.md`). It is the single owner of the four DB
objects the conveyor needs:

    1. candidate_queue            (NEW TABLE) — class-tagged, literature-clean,
                                   ranked Method-1 targets. Extends the 32-row
                                   `candidate_problems` table with the conveyor
                                   columns (snipe_signature, tier,
                                   deep_structural_exclude, literature_status,
                                   tractability_score, terminal,
                                   argument_authored).
    2. named_conjecture_status    (NEW TABLE) — famous/named-conjecture
                                   CLOSED/OPEN cards (the cheap pre-2024 catch
                                   for biblio_gate). SEEDED from
                                   `analysis/literature_kill_list.csv` (~29 rows)
                                   plus a handful of famous-conjecture cards.
    3. v_method1_ready            (NEW VIEW) — the orchestrator's poll surface:
                                   literature CLEAR, not structurally excluded,
                                   not terminal, ranked by tractability.
    4. proof_queue.submission_uuid (NEW COLUMN) — links an in-flight Method-1
                                   attempt to the Aristotle `submissions.uuid`.

It ALSO ensures `submissions.cost_usd` (REAL) and
`submissions.mathematical_content_score` (INTEGER) exist (ADD COLUMN if missing;
both are present as of the May 30 lane migration, so this is normally a no-op).

SAFETY: ADDITIVE ONLY. Every DDL statement is `CREATE TABLE IF NOT EXISTS`,
`CREATE VIEW IF NOT EXISTS`, or guarded `ALTER TABLE ADD COLUMN`. There is NO
DROP and NO DELETE of any existing object or row. Re-running is idempotent: the
tables/columns are created once; the named-conjecture seed uses
`INSERT OR IGNORE` so it never clobbers a card a later stage has edited.

Status enum for `named_conjecture_status.status`:
    'CLOSED'    — resolved (solved / disproven / known in the literature)
    'OPEN'      — genuinely open (do NOT skip on this; it is a green light)
    'AMBIGUOUS' — status unclear / disputed → biblio_gate must HOLD, not pass

Kill-list mapping (analysis/literature_kill_list.csv `literature_status`):
    AI_CLOSED, RECENTLY_SOLVED, LITERATURE_CLOSED  -> 'CLOSED'
    AMBIGUOUS                                       -> 'AMBIGUOUS'
"""
import csv
import sqlite3
import sys
from datetime import datetime, timezone
from pathlib import Path

DB_PATH = Path(__file__).resolve().parent.parent / "submissions" / "tracking.db"
KILL_LIST_CSV = (
    Path(__file__).resolve().parent.parent / "analysis" / "literature_kill_list.csv"
)


# ---------------------------------------------------------------------------
# DDL
# ---------------------------------------------------------------------------

# candidate_queue: the conveyor's ranked target store. Column order/typing
# matches the integration contract in method1_scaleup_plan.md exactly.
CANDIDATE_QUEUE_SQL = """
CREATE TABLE IF NOT EXISTS candidate_queue (
    problem_id              TEXT PRIMARY KEY,
    source_path             TEXT,
    statement               TEXT,
    domain                  TEXT,
    tier                    INTEGER,
    snipe_signature         TEXT,
    deep_structural_exclude INTEGER DEFAULT 0,
    literature_status       TEXT,
    tractability_score      REAL,
    prior_attempts          INTEGER DEFAULT 0,
    terminal                INTEGER DEFAULT 0,
    argument_authored       INTEGER DEFAULT 0,
    created_at              TEXT,
    updated_at              TEXT
)
"""

# named_conjecture_status: cheap pre-2024 literature catch (biblio_gate cards).
NAMED_CONJECTURE_STATUS_SQL = """
CREATE TABLE IF NOT EXISTS named_conjecture_status (
    name     TEXT PRIMARY KEY,
    status   TEXT,
    citation TEXT,
    year     TEXT,
    notes    TEXT
)
"""

# v_method1_ready: orchestrator poll surface. Exactly the contract's predicate
# and ordering — CLEAR literature, not structurally excluded, not terminal,
# ranked by tractability desc then fewest prior attempts.
V_METHOD1_READY_SQL = """
CREATE VIEW IF NOT EXISTS v_method1_ready AS
SELECT *
  FROM candidate_queue
 WHERE literature_status = 'CLEAR'
   AND deep_structural_exclude = 0
   AND terminal = 0
 ORDER BY tractability_score DESC, prior_attempts ASC
"""

# Helpful (additive) indexes for the conveyor's hot queries.
INDEXES = [
    "CREATE INDEX IF NOT EXISTS idx_cq_literature ON candidate_queue(literature_status)",
    "CREATE INDEX IF NOT EXISTS idx_cq_tractability ON candidate_queue(tractability_score)",
    "CREATE INDEX IF NOT EXISTS idx_cq_terminal ON candidate_queue(terminal)",
    "CREATE INDEX IF NOT EXISTS idx_pq_submission_uuid ON proof_queue(submission_uuid)",
]


# Columns ensured present on `submissions` (ADD COLUMN if missing).
SUBMISSIONS_ENSURE_COLUMNS = [
    ("cost_usd", "REAL"),
    ("mathematical_content_score", "INTEGER"),
]


# ---------------------------------------------------------------------------
# Seed data for named_conjecture_status
# ---------------------------------------------------------------------------

# Map the kill-list's literature_status vocabulary onto the card status enum.
_KILL_STATUS_MAP = {
    "AI_CLOSED": "CLOSED",
    "RECENTLY_SOLVED": "CLOSED",
    "LITERATURE_CLOSED": "CLOSED",
    "AMBIGUOUS": "AMBIGUOUS",
}

# A handful of famous-conjecture cards. These are well-known status facts; each
# carries a directional citation and an honest note. OPEN cards are GREEN
# lights (biblio_gate may pass), CLOSED are kills, AMBIGUOUS forces a HOLD.
# Kept deliberately small — the kill-list is the bulk seed.
FAMOUS_CARDS = [
    # --- famously OPEN (green light for the conveyor; do NOT skip on these) ---
    (
        "Collatz conjecture",
        "OPEN",
        "Lagarias 2010, 'The 3x+1 problem: an annotated bibliography'",
        "1937",
        "Famously open. 3x+1 / Syracuse problem. Verified to ~2^68 but no proof.",
    ),
    (
        "Goldbach conjecture",
        "OPEN",
        "Wang (ed.) 2002, 'Goldbach Conjecture' (World Scientific)",
        "1742",
        "Every even integer > 2 is a sum of two primes. Open; ternary Goldbach "
        "proved (Helfgott 2013).",
    ),
    (
        "Twin prime conjecture",
        "OPEN",
        "Zhang 2014 Ann. Math. 179 (bounded gaps); Polymath8",
        "1849",
        "Infinitely many primes p with p+2 prime. Bounded-gap results exist; the "
        "gap-2 conjecture itself is open.",
    ),
    (
        "Riemann hypothesis",
        "OPEN",
        "Bombieri 2000, Clay Millennium Problem description",
        "1859",
        "Nontrivial zeros of zeta on the critical line. Open; Clay Millennium "
        "Prize problem.",
    ),
    (
        "abc conjecture",
        "AMBIGUOUS",
        "Mochizuki IUT (disputed); Scholze-Stix 2018 critique",
        "1985",
        "Mochizuki's IUT proof is published (PRIMS 2021) but disputed by part of "
        "the community. Treat as AMBIGUOUS -> HOLD.",
    ),
    (
        "Lehmer's totient problem",
        "OPEN",
        "Cohen-Hagis 1980 bounds; Ribenboim, 'The New Book of Prime Number Records'",
        "1932",
        "Does phi(n) | n-1 imply n prime? Open. Project-internal: HELD per "
        "structural-open feasibility filter (see MEMORY.md).",
    ),
    # --- famously CLOSED (kills) ---
    (
        "Fermat's Last Theorem",
        "CLOSED",
        "Wiles 1995 Ann. Math. 141; Taylor-Wiles 1995 Ann. Math. 141",
        "1995",
        "x^n+y^n=z^n has no positive-integer solution for n>2. Proved by Wiles "
        "(modularity of semistable elliptic curves).",
    ),
    (
        "Catalan's conjecture",
        "CLOSED",
        "Mihailescu 2004 J. Reine Angew. Math. 572",
        "2004",
        "8 and 9 are the only consecutive perfect powers (Mihailescu's theorem).",
    ),
    (
        "Poincare conjecture",
        "CLOSED",
        "Perelman 2002-2003 (arXiv:math/0211159 et seq.)",
        "2003",
        "Every simply connected closed 3-manifold is homeomorphic to S^3. Proved "
        "by Perelman via Ricci flow.",
    ),
    (
        "Feit-Thompson theorem",
        "CLOSED",
        "Feit-Thompson 1963 Pacific J. Math. 13",
        "1963",
        "Every finite group of odd order is solvable. The base theorem is closed; "
        "the project's slot720 targets a NUMBER-THEORETIC side-conjecture, not "
        "the group-theory theorem.",
    ),
    (
        "Four color theorem",
        "CLOSED",
        "Appel-Haken 1977 Illinois J. Math. 21; Gonthier 2008 formal proof",
        "1976",
        "Every planar map is 4-colorable. Computer-assisted proof; formalized in "
        "Coq by Gonthier.",
    ),
]


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def _load_kill_list_cards(csv_path: Path) -> list:
    """Parse literature_kill_list.csv into named_conjecture_status card tuples.

    Each kill-list row -> a CLOSED/AMBIGUOUS card keyed by the registry theorem
    name (falling back to problem_id). The Erdos number and source file are
    folded into the citation/notes so the card is self-describing.
    Returns list of (name, status, citation, year, notes).
    """
    if not csv_path.exists():
        return []
    cards = []
    with open(csv_path, newline="", encoding="utf-8") as fh:
        reader = csv.DictReader(fh)
        for row in reader:
            name = (row.get("registry_theorem") or row.get("problem_id") or "").strip()
            if not name:
                continue
            lit = (row.get("literature_status") or "").strip().upper()
            status = _KILL_STATUS_MAP.get(lit, "AMBIGUOUS")
            erdos_n = (row.get("erdos_n") or "").strip()
            evidence = (row.get("top_evidence") or "").strip()
            erdosprob = (row.get("erdosproblems_status") or "").strip()
            checked = (row.get("checked_at") or "").strip()
            # Citation = the strongest available evidence string.
            citation = evidence or f"erdosproblems.com #{erdos_n}"
            # Pull a 4-digit year out of the evidence if present (directional).
            year = ""
            for tok in evidence.replace("(", " ").replace(")", " ").split():
                if tok.isdigit() and len(tok) == 4 and tok.startswith(("19", "20")):
                    year = tok
                    break
            notes = (
                f"Erdos #{erdos_n}; kill-list literature_status={lit}; "
                f"erdosproblems={erdosprob or 'n/a'}; checked_at={checked or 'n/a'}; "
                f"source={row.get('registry_file', '').strip()}"
            )
            cards.append((name, status, citation, year, notes))
    return cards


# ---------------------------------------------------------------------------
# Migration
# ---------------------------------------------------------------------------

def migrate(db_path: Path = DB_PATH, kill_list: Path = KILL_LIST_CSV) -> dict:
    """Run the additive migration. Returns a result dict for reporting."""
    conn = sqlite3.connect(str(db_path))
    try:
        result = {
            "tables_created": [],
            "tables_present": [],
            "view_created": False,
            "proof_queue_col_added": None,
            "submissions_cols_added": [],
            "submissions_cols_present": [],
            "indexes_ensured": 0,
            "named_cards_seeded": 0,
            "named_cards_total": 0,
            "kill_list_rows_parsed": 0,
            "famous_cards": len(FAMOUS_CARDS),
            "candidate_queue_rows": 0,
            "v_method1_ready_rows": 0,
        }

        def _exists(name: str) -> bool:
            return (
                conn.execute(
                    "SELECT 1 FROM sqlite_master WHERE name = ?", (name,)
                ).fetchone()
                is not None
            )

        # ---- 1. candidate_queue ----
        had_cq = _exists("candidate_queue")
        conn.execute(CANDIDATE_QUEUE_SQL)
        (result["tables_present"] if had_cq else result["tables_created"]).append(
            "candidate_queue"
        )

        # ---- 2. named_conjecture_status ----
        had_ncs = _exists("named_conjecture_status")
        conn.execute(NAMED_CONJECTURE_STATUS_SQL)
        (result["tables_present"] if had_ncs else result["tables_created"]).append(
            "named_conjecture_status"
        )

        # ---- 3. proof_queue.submission_uuid (additive ALTER) ----
        pq_cols = {r[1] for r in conn.execute("PRAGMA table_info(proof_queue)")}
        if "submission_uuid" not in pq_cols:
            conn.execute("ALTER TABLE proof_queue ADD COLUMN submission_uuid TEXT")
            result["proof_queue_col_added"] = "submission_uuid"
        else:
            result["proof_queue_col_added"] = "(already present)"

        # ---- 4. submissions.cost_usd + mathematical_content_score (ensure) ----
        sub_cols = {r[1] for r in conn.execute("PRAGMA table_info(submissions)")}
        for name, sqltype in SUBMISSIONS_ENSURE_COLUMNS:
            if name in sub_cols:
                result["submissions_cols_present"].append(name)
            else:
                conn.execute(f"ALTER TABLE submissions ADD COLUMN {name} {sqltype}")
                result["submissions_cols_added"].append(name)

        # ---- 5. v_method1_ready view ----
        conn.execute(V_METHOD1_READY_SQL)
        result["view_created"] = _exists("v_method1_ready")

        # ---- 6. indexes (additive) ----
        for stmt in INDEXES:
            conn.execute(stmt)
        result["indexes_ensured"] = len(INDEXES)

        # ---- 7. Seed named_conjecture_status (INSERT OR IGNORE = non-clobbering) ----
        kill_cards = _load_kill_list_cards(kill_list)
        result["kill_list_rows_parsed"] = len(kill_cards)
        # Famous cards first so a famous name wins over a same-named kill row;
        # INSERT OR IGNORE keeps whichever lands first on a PK collision.
        all_cards = FAMOUS_CARDS + kill_cards
        before = conn.execute(
            "SELECT COUNT(*) FROM named_conjecture_status"
        ).fetchone()[0]
        ts = _now_iso()
        for name, status, citation, year, notes in all_cards:
            conn.execute(
                "INSERT OR IGNORE INTO named_conjecture_status "
                "(name, status, citation, year, notes) VALUES (?, ?, ?, ?, ?)",
                (name, status, citation, year, f"{notes} | seeded {ts}"),
            )
        after = conn.execute(
            "SELECT COUNT(*) FROM named_conjecture_status"
        ).fetchone()[0]
        result["named_cards_seeded"] = after - before
        result["named_cards_total"] = after

        # ---- 8. Post-migration sanity counts ----
        result["candidate_queue_rows"] = conn.execute(
            "SELECT COUNT(*) FROM candidate_queue"
        ).fetchone()[0]
        result["v_method1_ready_rows"] = conn.execute(
            "SELECT COUNT(*) FROM v_method1_ready"
        ).fetchone()[0]

        # ---- Assertions: every contracted object now exists ----
        for obj in ("candidate_queue", "named_conjecture_status", "v_method1_ready"):
            assert _exists(obj), f"post-migration object missing: {obj}"
        pq_cols = {r[1] for r in conn.execute("PRAGMA table_info(proof_queue)")}
        assert "submission_uuid" in pq_cols, "proof_queue.submission_uuid missing"
        sub_cols = {r[1] for r in conn.execute("PRAGMA table_info(submissions)")}
        for name, _ in SUBMISSIONS_ENSURE_COLUMNS:
            assert name in sub_cols, f"submissions.{name} missing"

        conn.commit()
    finally:
        conn.close()

    return result


def main() -> int:
    r = migrate()
    if r["tables_created"]:
        print(f"OK  created table(s): {', '.join(r['tables_created'])}")
    if r["tables_present"]:
        print(f"OK  table(s) already present (idempotent): {', '.join(r['tables_present'])}")
    print(f"OK  proof_queue.submission_uuid: {r['proof_queue_col_added']}")
    if r["submissions_cols_added"]:
        print(f"OK  submissions add column(s): {', '.join(r['submissions_cols_added'])}")
    if r["submissions_cols_present"]:
        print(
            "OK  submissions column(s) already present (idempotent): "
            f"{', '.join(r['submissions_cols_present'])}"
        )
    print(f"OK  view v_method1_ready: {'created/present' if r['view_created'] else 'MISSING'}")
    print(f"OK  indexes ensured: {r['indexes_ensured']}")
    print(
        f"    named_conjecture_status: parsed {r['kill_list_rows_parsed']} kill-list "
        f"+ {r['famous_cards']} famous cards; seeded {r['named_cards_seeded']} new "
        f"(total now {r['named_cards_total']})"
    )
    print(f"    candidate_queue rows: {r['candidate_queue_rows']}")
    print(f"    v_method1_ready rows: {r['v_method1_ready_rows']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
