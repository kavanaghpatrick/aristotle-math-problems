#!/bin/bash
# e944 existence campaign launcher (hunter). Runs existence_cegar.py across multiple n in parallel.
# Usage: ./run_campaign.sh "13 14 15 16" <budget_sec> [--sym]
set -uo pipefail
DIR=/Users/patrickkavanagh/math/analysis/e944/team
NS=${1:?need n-list in quotes}
BUDGET=${2:-1800}
SYM=${3:-}
echo "# campaign: n in [$NS], budget=${BUDGET}s sym=$SYM  $(date)"
pids=()
for n in $NS; do
  ( python3 "$DIR/existence_cegar.py" "$n" --time "$BUDGET" --max-iters 5000000 $SYM \
      > "$DIR/campaign_n${n}.out" 2>&1 ) &
  pids+=($!)
  echo "# launched n=$n pid $!"
done
for p in "${pids[@]}"; do wait "$p"; done
echo "# campaign batch done $(date)"
for n in $NS; do
  echo "=== n=$n ==="; grep -E "RESULT|WITNESS|FALSE_CANDIDATE" "$DIR/campaign_n${n}.out" | tail -3
done
