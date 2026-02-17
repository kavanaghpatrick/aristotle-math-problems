-- Math-Forge Knowledge Database Schema
-- Separate from tracking.db: derived, reconstructible, independent evolution

PRAGMA journal_mode=WAL;
PRAGMA foreign_keys=ON;

-- ============================================================
-- DOMAINS: Mathematical classification taxonomy
-- ============================================================
CREATE TABLE IF NOT EXISTS domains (
    id TEXT PRIMARY KEY,
    name TEXT NOT NULL,
    description TEXT
);

INSERT OR IGNORE INTO domains (id, name, description) VALUES
('nt',             'Number Theory',   'Primes, divisibility, modular arithmetic, Diophantine'),
('algebra',        'Algebra',         'Groups, rings, fields, representation theory'),
('combinatorics',  'Combinatorics',   'Graphs, hypergraphs, extremal, Ramsey'),
('analysis',       'Analysis',        'Real/complex analysis, measure theory, functional');

-- ============================================================
-- FINDINGS: Core knowledge atoms
-- ============================================================
CREATE TABLE IF NOT EXISTS findings (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    finding_type TEXT NOT NULL CHECK(finding_type IN (
        'theorem', 'technique', 'failure', 'false_lemma',
        'computation', 'mathlib_api', 'insight'
    )),
    domain_id TEXT REFERENCES domains(id),
    title TEXT NOT NULL,
    description TEXT NOT NULL,
    problem_id TEXT,
    source_slot INTEGER,
    source_submission_uuid TEXT,
    source_file TEXT,
    theorem_name TEXT,
    theorem_statement TEXT,
    proof_technique TEXT,
    mathlib_imports TEXT,
    proof_lines INTEGER,
    counterexample TEXT,
    why_failed TEXT,
    avoid_pattern TEXT,
    confidence TEXT CHECK(confidence IN (
        'verified', 'high', 'medium', 'low', 'disproven'
    )) DEFAULT 'medium',
    created_at TEXT DEFAULT (datetime('now')),
    updated_at TEXT DEFAULT (datetime('now')),
    tags TEXT,
    notes TEXT,
    targets_open_gap INTEGER DEFAULT 0,
    gap_id TEXT
);

-- ============================================================
-- STRATEGIES: Problem-level approach tracking
-- ============================================================
CREATE TABLE IF NOT EXISTS strategies (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    problem_id TEXT NOT NULL,
    problem_name TEXT NOT NULL,
    domain_id TEXT REFERENCES domains(id),
    approach_name TEXT NOT NULL,
    approach_description TEXT,
    outcome TEXT NOT NULL CHECK(outcome IN (
        'proven', 'partial', 'failed', 'in_flight', 'untried'
    )),
    submission_slot INTEGER,
    submission_uuid TEXT,
    finding_ids TEXT,
    attempts INTEGER DEFAULT 1,
    last_attempted TEXT DEFAULT (datetime('now')),
    learned TEXT,
    created_at TEXT DEFAULT (datetime('now')),
    UNIQUE(problem_id, approach_name)
);

-- ============================================================
-- PROBLEMS: Problem-level summary
-- ============================================================
CREATE TABLE IF NOT EXISTS problems (
    id TEXT PRIMARY KEY,
    name TEXT NOT NULL,
    domain_id TEXT REFERENCES domains(id),
    status TEXT CHECK(status IN (
        'open', 'proven', 'partial', 'false', 'in_flight'
    )) DEFAULT 'open',
    submission_count INTEGER DEFAULT 0,
    proven_count INTEGER DEFAULT 0,
    failed_count INTEGER DEFAULT 0,
    statement TEXT,
    best_result TEXT,
    created_at TEXT DEFAULT (datetime('now')),
    updated_at TEXT DEFAULT (datetime('now'))
);

-- ============================================================
-- CACHE: Aristotle queue status cache
-- ============================================================
CREATE TABLE IF NOT EXISTS queue_cache (
    id INTEGER PRIMARY KEY CHECK(id = 1),
    cached_at TEXT NOT NULL,
    in_flight INTEGER DEFAULT 0,
    slots_open INTEGER DEFAULT 5,
    ready_to_fetch TEXT,
    recently_completed TEXT,
    top_near_miss TEXT,
    raw_json TEXT
);

-- ============================================================
-- FTS5: Full-text search over findings
-- ============================================================
CREATE VIRTUAL TABLE IF NOT EXISTS findings_fts USING fts5(
    title,
    description,
    problem_id UNINDEXED,
    theorem_name,
    theorem_statement,
    proof_technique,
    tags,
    why_failed,
    content=findings,
    content_rowid=id,
    tokenize='porter unicode61'
);

-- ============================================================
-- FTS5 SYNC TRIGGERS
-- ============================================================
CREATE TRIGGER IF NOT EXISTS findings_fts_insert AFTER INSERT ON findings BEGIN
    INSERT INTO findings_fts(rowid, title, description, theorem_name, theorem_statement, proof_technique, tags, why_failed)
    VALUES (new.id, new.title, new.description, new.theorem_name, new.theorem_statement, new.proof_technique, new.tags, new.why_failed);
END;

CREATE TRIGGER IF NOT EXISTS findings_fts_delete AFTER DELETE ON findings BEGIN
    INSERT INTO findings_fts(findings_fts, rowid, title, description, theorem_name, theorem_statement, proof_technique, tags, why_failed)
    VALUES ('delete', old.id, old.title, old.description, old.theorem_name, old.theorem_statement, old.proof_technique, old.tags, old.why_failed);
END;

CREATE TRIGGER IF NOT EXISTS findings_fts_update AFTER UPDATE ON findings BEGIN
    INSERT INTO findings_fts(findings_fts, rowid, title, description, theorem_name, theorem_statement, proof_technique, tags, why_failed)
    VALUES ('delete', old.id, old.title, old.description, old.theorem_name, old.theorem_statement, old.proof_technique, old.tags, old.why_failed);
    INSERT INTO findings_fts(rowid, title, description, theorem_name, theorem_statement, proof_technique, tags, why_failed)
    VALUES (new.id, new.title, new.description, new.theorem_name, new.theorem_statement, new.proof_technique, new.tags, new.why_failed);
END;

-- ============================================================
-- INDEXES
-- ============================================================
CREATE INDEX IF NOT EXISTS idx_findings_type ON findings(finding_type);
CREATE INDEX IF NOT EXISTS idx_findings_domain ON findings(domain_id);
CREATE INDEX IF NOT EXISTS idx_findings_problem ON findings(problem_id);
CREATE INDEX IF NOT EXISTS idx_findings_slot ON findings(source_slot);
CREATE INDEX IF NOT EXISTS idx_findings_confidence ON findings(confidence);
CREATE INDEX IF NOT EXISTS idx_findings_created ON findings(created_at);

CREATE INDEX IF NOT EXISTS idx_strategies_problem ON strategies(problem_id);
CREATE INDEX IF NOT EXISTS idx_strategies_outcome ON strategies(outcome);
CREATE INDEX IF NOT EXISTS idx_strategies_domain ON strategies(domain_id);

CREATE INDEX IF NOT EXISTS idx_problems_domain ON problems(domain_id);
CREATE INDEX IF NOT EXISTS idx_problems_status ON problems(status);

-- ============================================================
-- VIEWS
-- ============================================================
CREATE VIEW IF NOT EXISTS v_proven_techniques AS
SELECT
    proof_technique,
    domain_id,
    COUNT(*) as usage_count,
    GROUP_CONCAT(source_slot, ', ') as slots
FROM findings
WHERE finding_type = 'theorem' AND confidence = 'verified' AND proof_technique IS NOT NULL
GROUP BY proof_technique, domain_id
ORDER BY usage_count DESC;

CREATE VIEW IF NOT EXISTS v_failed_approaches AS
SELECT
    problem_id,
    title,
    why_failed,
    avoid_pattern,
    source_slot,
    created_at
FROM findings
WHERE finding_type IN ('failure', 'false_lemma')
ORDER BY created_at DESC;

CREATE VIEW IF NOT EXISTS v_problem_dashboard AS
SELECT
    p.id,
    p.name,
    p.domain_id,
    p.status,
    p.submission_count,
    p.proven_count,
    p.failed_count,
    (SELECT COUNT(*) FROM findings f WHERE f.problem_id = p.id AND f.finding_type = 'theorem') as theorem_count,
    (SELECT COUNT(*) FROM findings f WHERE f.problem_id = p.id AND f.finding_type = 'failure') as failure_count,
    (SELECT COUNT(*) FROM findings f WHERE f.problem_id = p.id AND f.finding_type = 'false_lemma') as false_lemma_count,
    (SELECT COUNT(*) FROM strategies s WHERE s.problem_id = p.id AND s.outcome = 'in_flight') as in_flight_count,
    (SELECT COUNT(*) FROM strategies s WHERE s.problem_id = p.id AND s.outcome = 'untried') as untried_count
FROM problems p;

CREATE VIEW IF NOT EXISTS v_near_miss_findings AS
SELECT
    f.id, f.title, f.problem_id, f.source_slot, f.notes
FROM findings f
WHERE f.finding_type = 'theorem'
  AND f.confidence = 'medium'
  AND f.notes LIKE '%sorry=1%'
ORDER BY f.created_at DESC;
