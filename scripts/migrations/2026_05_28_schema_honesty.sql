-- 2026-05-28: schema-honesty migration
--
-- Adds:
--   - axiom_count, axiomatizes_prior_work, cost_usd, execution_seconds
--   - sketch provenance columns (set by informal-sketch pipeline when implemented)
--   - status_v2: collapses the 25-value status soup into 6 honest buckets
--
-- After this file runs, the python runner (scripts/migrations/run.py) verifies
-- that every row got a status_v2, then overwrites status with status_v2 and
-- drops the temporary column. The original status string is preserved in
-- `status_legacy` so we can roll back.
--
-- compiled_advance is OPT-IN: only /audit sets it, and only when
--   target_resolved=1 AND axiomatizes_prior_work=0 AND contribution_statement IS NOT NULL.
-- This migration never moves a row INTO compiled_advance — it only collapses
-- the noise.

BEGIN;

-- ── Honesty columns ──────────────────────────────────────────────────────────
ALTER TABLE submissions ADD COLUMN axiomatizes_prior_work INTEGER DEFAULT 0;
ALTER TABLE submissions ADD COLUMN axiom_count INTEGER DEFAULT 0;
ALTER TABLE submissions ADD COLUMN cost_usd REAL;
-- execution_seconds was declared in the original table but is NULL on every row;
-- leave it as-is (the column already exists; the audit pipeline will start populating it).

-- ── Sketch provenance (set by informal-sketch pipeline; NULL today) ──────────
ALTER TABLE submissions ADD COLUMN sketch_model_primary TEXT;
ALTER TABLE submissions ADD COLUMN sketch_model_secondary TEXT;
ALTER TABLE submissions ADD COLUMN sketch_hash TEXT;
ALTER TABLE submissions ADD COLUMN candidate_lemmas_json TEXT;
ALTER TABLE submissions ADD COLUMN prior_context_used TEXT;
ALTER TABLE submissions ADD COLUMN experiment_arm TEXT;

-- ── Status v2 collapse (25 values → 6) ───────────────────────────────────────
ALTER TABLE submissions ADD COLUMN status_legacy TEXT;
ALTER TABLE submissions ADD COLUMN status_v2 TEXT;

UPDATE submissions SET status_legacy = status;

UPDATE submissions SET status_v2 = CASE
  WHEN status IN ('submitted','queued','running','in_progress','pending',
                  'draft','ready')                                              THEN 'submitted'
  WHEN status IN ('failed','error','broken','invalid','timeout',
                  'tainted','missing','stale')                                  THEN 'compile_failed'
  WHEN status IN ('partial','incomplete','near_miss')                           THEN 'compiled_partial'
  WHEN status IN ('completed','compiled_clean','historical',
                  'known_result','review_complete')                             THEN 'compiled_no_advance'
  WHEN status IN ('disproven','disproved','likely_false')                       THEN 'disproven'
  ELSE 'compile_failed'
END;

COMMIT;
