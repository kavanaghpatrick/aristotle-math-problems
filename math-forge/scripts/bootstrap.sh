#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PLUGIN_ROOT="$(dirname "$SCRIPT_DIR")"
DB_PATH="$PLUGIN_ROOT/data/knowledge.db"

echo "[math-forge] Creating knowledge.db from schema..."
sqlite3 "$DB_PATH" < "$PLUGIN_ROOT/data/schema.sql"

if [ -f "$PLUGIN_ROOT/../submissions/tracking.db" ]; then
  echo "[math-forge] Migrating from tracking.db..."
  python3 "$SCRIPT_DIR/migrate_tracking.py" \
    --tracking-db "$PLUGIN_ROOT/../submissions/tracking.db" \
    --knowledge-db "$DB_PATH"
else
  echo "[math-forge] No tracking.db found, skipping migration"
fi

echo "[math-forge] Running stats..."
"$SCRIPT_DIR/mk" stats

echo "[math-forge] Bootstrap complete"
