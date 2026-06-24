#!/bin/bash
set -uo pipefail
GENG=/opt/homebrew/Cellar/nauty/2.9.3/bin/geng
DIR=/Users/patrickkavanagh/math/analysis/e944/team
OUT=$DIR/a3_n13_e40_D8_shards; mkdir -p "$OUT"
echo "# A3 COMPLETE |E|=40 slice: n=13 delta>=6 Delta<=8 (includes deg-8) parallel  $(date)"
pids=()
for ((r=0;r<10;r++)); do
  ( nice -n 12 $GENG -c -d6 -D8 13 40:40 "$r/10" 2>/dev/null | nice -n 12 python3 "$DIR/floor_worker.py" \
     > "$OUT/s${r}.json" 2> "$OUT/s${r}.err" ) &
  pids+=($!)
done
for p in "${pids[@]}"; do wait "$p"; done
python3 - "$OUT" <<'PY'
import sys,json,glob,os
o=sys.argv[1]; tot=vc=0; w=[]
for f in sorted(glob.glob(os.path.join(o,"s*.json"))):
    try: d=json.load(open(f)); tot+=d["total"]; vc+=d["vc4"]; w+=d["witnesses"]
    except Exception as e: print("bad",f,e)
print(json.dumps({"slice":"n=13 |E|=40 COMPLETE (D<=8)","total":tot,"vc4":vc,"witnesses":w}))
PY
echo "# done $(date)"
