#!/bin/bash
# e944 IRREGULAR delta>=6 annealing campaign (hunter). Covers the regime skeptic's exhaustive
# 6-regular sweep does NOT: min-deg 6 with Delta up to n-5, non-regular.
set -uo pipefail
DIR=/Users/patrickkavanagh/math/analysis/e944/team
BUDGET=${1:-1800}
mkdir -p "$DIR/anneal_irr_out"
echo "# IRREGULAR anneal campaign budget=${BUDGET}s  $(date)"
pids=()
for n in 13 14 15 16; do
  for seed in 1 2 3; do
    ( python3 "$DIR/witness_anneal.py" "$n" --time "$BUDGET" --seed "$seed" \
        > "$DIR/anneal_irr_out/n${n}_s${seed}.out" 2>&1 ) &
    pids+=($!)
  done
done
echo "# launched ${#pids[@]} irregular workers (n=13..16 x 3 seeds)"
for p in "${pids[@]}"; do wait "$p"; done
echo "# IRREGULAR anneal campaign done $(date)"
grep -h "best_energy\|WITNESS" "$DIR"/anneal_irr_out/*.out 2>/dev/null
ls "$DIR"/WITNESS_n*.json 2>/dev/null && echo "WITNESS FILES EXIST ^^^"
