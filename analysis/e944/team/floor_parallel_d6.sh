#!/bin/bash
# e944 parallel floor with min-degree-6 (CONDITIONAL on Prop 5.1: any (4,1)-witness has delta>=6).
# Usage: ./floor_parallel_d6.sh <n> <nshards>
set -euo pipefail
GENG=/opt/homebrew/Cellar/nauty/2.9.3/bin/geng
N=${1:?need n}
SHARDS=${2:-12}
DIR=/Users/patrickkavanagh/math/analysis/e944/team
OUT=$DIR/floor_d6_n${N}_shards
mkdir -p "$OUT"
echo "# e944 floor n=$N delta>=6 across $SHARDS shards  $(date)"
pids=()
for ((r=0; r<SHARDS; r++)); do
  ( $GENG -c -d6 "$N" "$r/$SHARDS" 2>/dev/null \
      | python3 "$DIR/floor_worker.py" \
      > "$OUT/shard_${r}.json" 2> "$OUT/shard_${r}.err" ) &
  pids+=($!)
done
fail=0
for p in "${pids[@]}"; do wait "$p" || fail=1; done
python3 - "$OUT" "$N" "$SHARDS" <<'PY'
import sys, json, glob, os
outdir, n, shards = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
total = vc4 = 0; wits = []
for f in sorted(glob.glob(os.path.join(outdir, "shard_*.json"))):
    try: d = json.load(open(f))
    except Exception as e:
        print(f"!! bad shard {f}: {e}"); continue
    total += d["total"]; vc4 += d["vc4"]; wits += d["witnesses"]
print(json.dumps({"n": n, "delta": ">=6", "shards": shards,
                  "total_enumerated": total, "vc4": vc4, "witnesses": wits}))
for f in sorted(glob.glob(os.path.join(outdir, "shard_*.err"))):
    s = open(f).read().strip()
    if "WITNESS" in s: print("!! WITNESS in", f, ":", s)
PY
echo "# done $(date)"
