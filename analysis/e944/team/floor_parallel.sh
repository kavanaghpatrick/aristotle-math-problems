#!/bin/bash
# e944 parallel exhaustive floor (hunter).
# Splits geng enumeration across N shards via res/mod, runs floor_worker.py on each.
# Usage: ./floor_parallel.sh <n> <nshards>
set -euo pipefail
GENG=/opt/homebrew/Cellar/nauty/2.9.3/bin/geng
N=${1:?need n}
SHARDS=${2:-14}
DIR=/Users/patrickkavanagh/math/analysis/e944/team
OUT=$DIR/floor_n${N}_shards
mkdir -p "$OUT"

echo "# e944 floor n=$N across $SHARDS shards (geng -c -d3)  $(date)"
pids=()
for ((r=0; r<SHARDS; r++)); do
  # geng res/mod: enumerate the r-th class mod SHARDS
  ( $GENG -c -d3 "$N" "$r/$SHARDS" 2>/dev/null \
      | python3 "$DIR/floor_worker.py" \
      > "$OUT/shard_${r}.json" 2> "$OUT/shard_${r}.err" ) &
  pids+=($!)
done

# wait for all shards
fail=0
for p in "${pids[@]}"; do
  wait "$p" || fail=1
done

# aggregate
python3 - "$OUT" "$N" "$SHARDS" <<'PY'
import sys, json, glob, os
outdir, n, shards = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
total = 0; vc4 = 0; wits = []
for f in sorted(glob.glob(os.path.join(outdir, "shard_*.json"))):
    try:
        d = json.load(open(f))
    except Exception as e:
        print(f"!! could not read {f}: {e}")
        continue
    total += d["total"]; vc4 += d["vc4"]; wits += d["witnesses"]
print(json.dumps({"n": n, "shards": shards, "total_enumerated": total,
                  "vc4": vc4, "witnesses": wits}))
# surface any WITNESS_CANDIDATE lines from stderr
for f in sorted(glob.glob(os.path.join(outdir, "shard_*.err"))):
    s = open(f).read().strip()
    if "WITNESS" in s:
        print("!! WITNESS in", f, ":", s)
PY

echo "# done $(date)"
