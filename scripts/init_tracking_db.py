#!/usr/bin/env python3
"""
Initialize the submission tracking database.
Run once: python3 scripts/init_tracking_db.py
"""

import sqlite3
from pathlib import Path
from datetime import datetime

DB_PATH = Path(__file__).parent.parent / "submissions" / "tracking.db"

SCHEMA = """
-- Core submission tracking
CREATE TABLE IF NOT EXISTS submissions (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    uuid TEXT UNIQUE,
    filename TEXT NOT NULL,
    problem_id TEXT,
    pattern TEXT,  -- boris, scaffolded, pessimist, etc.

    -- Timestamps
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    submitted_at TEXT,
    completed_at TEXT,

    -- Status
    status TEXT DEFAULT 'draft',  -- draft, validated, submitted, running, completed, failed

    -- Validation results
    syntax_valid INTEGER,
    definition_audit_passed INTEGER,
    definition_issues TEXT,  -- JSON array of issues found

    -- Aristotle results
    aristotle_status TEXT,
    sorry_count INTEGER,
    proven_count INTEGER,
    output_file TEXT,

    -- Multi-agent audit
    grok_reviewed INTEGER DEFAULT 0,
    grok_issues TEXT,
    gemini_reviewed INTEGER DEFAULT 0,
    gemini_issues TEXT,

    -- Final verdict
    verified INTEGER,  -- NULL = pending, 0 = invalid, 1 = valid
    verification_notes TEXT
);

-- Definition audit history
CREATE TABLE IF NOT EXISTS definition_audits (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    submission_id INTEGER REFERENCES submissions(id),
    audit_date TEXT DEFAULT CURRENT_TIMESTAMP,

    -- Checks
    has_sinf_unrestricted INTEGER,
    has_sym2_issue INTEGER,
    has_set_finset_issue INTEGER,
    has_missing_decidable INTEGER,
    has_axiom_usage INTEGER,

    -- Details
    issues_json TEXT,

    FOREIGN KEY (submission_id) REFERENCES submissions(id)
);

-- Proven theorems extracted from outputs
CREATE TABLE IF NOT EXISTS proven_theorems (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    submission_id INTEGER REFERENCES submissions(id),
    theorem_name TEXT NOT NULL,
    theorem_type TEXT,  -- lemma, theorem, def
    statement TEXT,
    proof_complete INTEGER,  -- 1 = no sorry, 0 = has sorry

    -- Verification
    definition_correct INTEGER,  -- NULL = unchecked, 0 = buggy, 1 = correct
    manually_verified INTEGER DEFAULT 0,

    extracted_at TEXT DEFAULT CURRENT_TIMESTAMP,

    FOREIGN KEY (submission_id) REFERENCES submissions(id)
);

-- Known definition patterns (for audit)
CREATE TABLE IF NOT EXISTS definition_patterns (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    pattern_name TEXT UNIQUE NOT NULL,
    pattern_regex TEXT NOT NULL,
    is_buggy INTEGER NOT NULL,
    description TEXT,
    fix_suggestion TEXT
);

-- Audit log for traceability
CREATE TABLE IF NOT EXISTS audit_log (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    submission_id INTEGER,
    action TEXT NOT NULL,
    agent TEXT,  -- human, grok, gemini, script
    details TEXT,
    timestamp TEXT DEFAULT CURRENT_TIMESTAMP,

    FOREIGN KEY (submission_id) REFERENCES submissions(id)
);

-- Views for common queries
CREATE VIEW IF NOT EXISTS v_active_submissions AS
SELECT
    s.id, s.uuid, s.filename, s.problem_id, s.pattern,
    s.status, s.submitted_at,
    s.definition_audit_passed,
    s.verified
FROM submissions s
WHERE s.status IN ('submitted', 'running', 'validated')
ORDER BY s.created_at DESC;

CREATE VIEW IF NOT EXISTS v_verification_needed AS
SELECT
    s.id, s.uuid, s.filename, s.problem_id,
    s.sorry_count, s.proven_count,
    s.grok_reviewed, s.gemini_reviewed,
    s.verified
FROM submissions s
WHERE s.status = 'completed'
  AND s.verified IS NULL
  AND s.proven_count > 0
ORDER BY s.completed_at DESC;

CREATE VIEW IF NOT EXISTS v_valid_proven AS
SELECT
    pt.theorem_name, pt.theorem_type, pt.statement,
    s.filename, s.uuid
FROM proven_theorems pt
JOIN submissions s ON pt.submission_id = s.id
WHERE pt.proof_complete = 1
  AND pt.definition_correct = 1
  AND s.verified = 1
ORDER BY pt.extracted_at DESC;
"""

# Known buggy patterns
BUGGY_PATTERNS = [
    {
        "pattern_name": "sinf_unrestricted",
        "pattern_regex": r"sInf\s*\{[^}]*∃\s*E\s*:\s*Finset\s*\(Sym2",
        "is_buggy": 1,
        "description": "sInf over unrestricted Sym2, allows non-graph edges",
        "fix_suggestion": "Use G.edgeFinset.powerset.filter instead"
    },
    {
        "pattern_name": "sym2_covering",
        "pattern_regex": r"e\s*∈\s*t\.sym2|edge\s*∈\s*t\.sym2",
        "is_buggy": 0,  # Not buggy itself, but needs E ⊆ G.edgeFinset
        "description": "Using t.sym2 for covering - check E is restricted",
        "fix_suggestion": "Ensure E ⊆ G.edgeFinset in the covering definition"
    },
    {
        "pattern_name": "edgefinset_correct",
        "pattern_regex": r"G\.edgeFinset\.powerset",
        "is_buggy": 0,
        "description": "Correct: restricts to graph edges",
        "fix_suggestion": None
    },
    {
        "pattern_name": "set_without_decidable",
        "pattern_regex": r"\(G\.induce\s+\w+\)\.edgeFinset",
        "is_buggy": 0,  # Potentially buggy if S : Set V
        "description": "induce with edgeFinset - check DecidablePred",
        "fix_suggestion": "Use Finset V instead of Set V, or add DecidablePred"
    },
    {
        "pattern_name": "axiom_usage",
        "pattern_regex": r"^axiom\s+\w+",
        "is_buggy": 1,
        "description": "Axiom declarations rejected by Aristotle",
        "fix_suggestion": "Include full proofs as lemmas, not axioms"
    }
]


def init_database():
    """Initialize the database with schema and patterns."""
    DB_PATH.parent.mkdir(parents=True, exist_ok=True)

    conn = sqlite3.connect(DB_PATH)
    conn.executescript(SCHEMA)

    # Insert known patterns
    for pattern in BUGGY_PATTERNS:
        conn.execute("""
            INSERT OR REPLACE INTO definition_patterns
            (pattern_name, pattern_regex, is_buggy, description, fix_suggestion)
            VALUES (?, ?, ?, ?, ?)
        """, (
            pattern["pattern_name"],
            pattern["pattern_regex"],
            pattern["is_buggy"],
            pattern["description"],
            pattern["fix_suggestion"]
        ))

    conn.commit()
    conn.close()

    print(f"✓ Database initialized at: {DB_PATH}")
    print(f"✓ Loaded {len(BUGGY_PATTERNS)} definition patterns")


if __name__ == "__main__":
    init_database()
