#!/bin/bash
# e944 parallel annealing witness campaign (hunter). Many (n, seed) workers across cores.
# Usage: ./run_anneal_campaign.sh <budget_sec>
set -uo pipefail
DIR=/Users/patrickkavanagh/math/analysis/e944/team
BUDGET=${1:-1800}
mkdir -p "$DIR/anneal_out"
echo "# anneal campaign budget=${BUDGET}s  $(date)"
pids=()
# 12 workers: n in {13,14,15} x 4 seeds each (sparsest/most-promising n first)
for n in 13 14 15; do
  for seed in 1 2 3 4; do
    ( python3 "$DIR/witness_anneal.py" "$n" --time "$BUDGET" --seed "$seed" \
        > "$DIR/anneal_out/n${n}_s${seed}.out" 2>&1 ) &
    pids+=($!)
  done
done
echo "# launched ${#pids[@]} workers"
for p in "${pids[@]}"; do wait "$p"; done
echo "# anneal campaign done $(date)"
echo "=== best energies ==="
grep -h "best_energy\|WITNESS" "$DIR"/anneal_out/*.out | sort | uniq -c
ls "$DIR"/WITNESS_n*.json 2>/dev/null && echo "WITNESS FILES EXIST ^^^"
