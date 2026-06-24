#!/bin/bash
set -uo pipefail
GENG=/opt/homebrew/Cellar/nauty/2.9.3/bin/geng
DIR=/Users/patrickkavanagh/math/analysis/e944/team
N=12; D=7; SH=8
OUT=$DIR/floor_n12_d6D7_shards; mkdir -p "$OUT"
echo "# n=12 FULL delta>=6 (deg in [6,7], Delta<=n-5) across $SH shards $(date)"
pids=()
for ((r=0;r<SH;r++)); do
  ( nice -n 15 $GENG -c -d6 -D$D $N "$r/$SH" 2>/dev/null | nice -n 15 python3 "$DIR/floor_worker.py" \
     > "$OUT/shard_${r}.json" 2> "$OUT/shard_${r}.err" ) &
  pids+=($!)
done
for p in "${pids[@]}"; do wait "$p"; done
python3 - "$OUT" <<'PY'
import sys,json,glob,os
o=sys.argv[1]; tot=vc=0; w=[]
for f in sorted(glob.glob(os.path.join(o,"shard_*.json"))):
    try: d=json.load(open(f))
    except Exception as e: print("bad",f,e); continue
    tot+=d["total"]; vc+=d["vc4"]; w+=d["witnesses"]
print(json.dumps({"n":12,"regime":"delta>=6 (deg in [6,7])","total":tot,"vc4":vc,"witnesses":w}))
PY
echo "# done $(date)"
