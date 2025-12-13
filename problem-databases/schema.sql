-- Unified Open Problems Database Schema
-- For Aristotle submission pipeline

-- Core problems table
CREATE TABLE IF NOT EXISTS problems (
    id INTEGER PRIMARY KEY AUTOINCREMENT,

    -- Identification
    source TEXT NOT NULL,              -- 'erdos', 'formal-conjectures', 'opg', 'wikipedia', 'oeis', 'polymath'
    source_id TEXT,                    -- ID within source (e.g., '124' for Erdős #124)
    name TEXT NOT NULL,                -- Problem name
    slug TEXT UNIQUE,                  -- URL-friendly identifier

    -- Status
    status TEXT DEFAULT 'open',        -- 'open', 'solved', 'disproved', 'partially_solved', 'unknown'
    status_date TEXT,                  -- When status was last verified

    -- Formalization
    has_lean4 BOOLEAN DEFAULT FALSE,
    lean_file_path TEXT,               -- Path to .lean file if exists
    lean_content TEXT,                 -- Full Lean 4 content
    formalization_quality TEXT,        -- 'complete', 'partial', 'statement_only', 'none'

    -- Classification
    domain TEXT,                       -- Primary domain
    subdomain TEXT,                    -- Subdomain
    ams_classification TEXT,           -- AMS subject classification

    -- Problem details
    statement TEXT,                    -- Natural language statement
    formal_statement TEXT,             -- Formal mathematical statement
    background TEXT,                   -- Context and history
    known_results TEXT,                -- What's already proven

    -- Tractability assessment
    tractability_score INTEGER,        -- 0-100
    search_space_estimate TEXT,        -- e.g., '2^20', 'infinite', 'polynomial'
    is_bounded BOOLEAN,                -- Has finite/bounded parameters
    is_computational BOOLEAN,          -- Can be attacked computationally
    recent_progress TEXT,              -- Recent developments

    -- Prize info
    prize_amount INTEGER,              -- In USD, 0 if none
    prize_offered_by TEXT,

    -- References
    original_reference TEXT,
    arxiv_ids TEXT,                    -- JSON array
    oeis_ids TEXT,                     -- JSON array
    mathscinet_ids TEXT,               -- JSON array
    urls TEXT,                         -- JSON array of relevant URLs

    -- Submission tracking
    submitted_to_aristotle BOOLEAN DEFAULT FALSE,
    aristotle_project_id TEXT,
    submission_date TEXT,
    result TEXT,                       -- 'success', 'failed', 'pending', 'timeout'

    -- Metadata
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    updated_at TEXT DEFAULT CURRENT_TIMESTAMP,
    notes TEXT
);

-- Tags table (many-to-many)
CREATE TABLE IF NOT EXISTS tags (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT UNIQUE NOT NULL,
    category TEXT                      -- 'domain', 'technique', 'difficulty', etc.
);

CREATE TABLE IF NOT EXISTS problem_tags (
    problem_id INTEGER REFERENCES problems(id),
    tag_id INTEGER REFERENCES tags(id),
    PRIMARY KEY (problem_id, tag_id)
);

-- Related problems
CREATE TABLE IF NOT EXISTS problem_relations (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    problem_id_1 INTEGER REFERENCES problems(id),
    problem_id_2 INTEGER REFERENCES problems(id),
    relation_type TEXT,                -- 'equivalent', 'generalizes', 'special_case', 'related'
    notes TEXT
);

-- Submission history
CREATE TABLE IF NOT EXISTS submissions (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    problem_id INTEGER REFERENCES problems(id),
    aristotle_project_id TEXT,
    submission_date TEXT,
    input_file TEXT,
    input_content TEXT,
    status TEXT,                       -- 'queued', 'in_progress', 'complete', 'failed'
    result_file TEXT,
    result_content TEXT,
    success BOOLEAN,
    error_message TEXT,
    duration_seconds INTEGER,
    notes TEXT
);

-- Sources metadata
CREATE TABLE IF NOT EXISTS sources (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT UNIQUE NOT NULL,
    url TEXT,
    description TEXT,
    last_scraped TEXT,
    problem_count INTEGER,
    notes TEXT
);

-- Views for common queries
CREATE VIEW IF NOT EXISTS open_with_lean AS
SELECT * FROM problems
WHERE status = 'open' AND has_lean4 = TRUE
ORDER BY tractability_score DESC;

CREATE VIEW IF NOT EXISTS ready_to_submit AS
SELECT * FROM problems
WHERE status = 'open'
  AND has_lean4 = TRUE
  AND submitted_to_aristotle = FALSE
  AND tractability_score >= 70
ORDER BY tractability_score DESC;

CREATE VIEW IF NOT EXISTS submission_stats AS
SELECT
    source,
    COUNT(*) as total,
    SUM(CASE WHEN status = 'open' THEN 1 ELSE 0 END) as open_count,
    SUM(CASE WHEN has_lean4 THEN 1 ELSE 0 END) as with_lean4,
    SUM(CASE WHEN submitted_to_aristotle THEN 1 ELSE 0 END) as submitted,
    AVG(tractability_score) as avg_tractability
FROM problems
GROUP BY source;

-- Indexes for performance
CREATE INDEX IF NOT EXISTS idx_problems_source ON problems(source);
CREATE INDEX IF NOT EXISTS idx_problems_status ON problems(status);
CREATE INDEX IF NOT EXISTS idx_problems_tractability ON problems(tractability_score DESC);
CREATE INDEX IF NOT EXISTS idx_problems_has_lean4 ON problems(has_lean4);
CREATE INDEX IF NOT EXISTS idx_problems_submitted ON problems(submitted_to_aristotle);
