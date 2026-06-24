#!/bin/bash
# e944 MARATHON v2 PARALLEL (hunter) — saturates all 14 cores with diverse proposal streams.
# CPU-driven (measured fastest), GPU engines (3^n + BHK) as cross-verifiers on hits only.
# Each worker = witness_anneal (irregular δ≥6 full-predicate stream) at a fixed (n, seed); 12 workers
# span n=14-18, plus 2 cores for count's min-conflict SA. ~44k full-predicate evals/s aggregate
# (measured) -> ~10^9+ candidates/day. Any 0-critical hit -> CANDIDATE_*.json -> gate routing.
#
# Run: nohup nice -n 19 ./marathon_v2_par.sh > /dev/null 2>&1 &
DIR=/Users/patrickkavanagh/math/analysis/e944/team
LOG=$DIR/search_n14plus.log
cd "$DIR" || exit 1
log() { echo "[$(date '+%Y-%m-%d %H:%M:%S')] $*" >> "$LOG"; }

route_candidates() {
  for cf in "$DIR"/CANDIDATE_*.json; do
    [ -e "$cf" ] || continue
    case "$cf" in *.routed) continue;; esac
    python3 - "$cf" <<'PY' >> "$LOG" 2>&1
import sys, json
sys.path.insert(0, "/Users/patrickkavanagh/math/analysis/e944/team")
from marathon_v2 import handle_candidate
d = json.load(open(sys.argv[1]))
handle_candidate(d.get("g6",""), [tuple(e) for e in d["edges"]], d["n"], d.get("src","anneal"))
PY
    mv "$cf" "$cf.routed" 2>/dev/null
  done
}

log "=== MARATHON v2 PARALLEL START PID $$ — 14 cores, n=14-18 proposal streams + count SA ==="
log "    measured coverage ~44k full-predicate evals/s aggregate -> ~10^9+ candidates/day"
round=0
while true; do
  round=$((round+1))
  pids=()
  # 12 annealer workers: n in {14,15,16,17,18} x seeds, weighted toward n=14-16 (predicted regime)
  i=0
  for ns in "14 1" "14 2" "15 1" "15 2" "15 3" "16 1" "16 2" "16 3" "17 1" "17 2" "18 1" "18 2"; do
    set -- $ns; n=$1; tag=$2
    seed=$(( round*101 + i*7 + tag ))
    ( nice -n 19 timeout 600 python3 "$DIR/witness_anneal.py" "$n" --time 560 --seed "$seed" \
        > "$DIR/mv2p_n${n}_${tag}.out" 2>&1 ) &
    pids+=($!)
    i=$((i+1))
  done
  # 2 cores: count's min-conflict SA (exact objective, n=12-18 internal)
  ( nice -n 19 timeout 600 python3 "$DIR/count_anneal_mindeg6.py" > "$DIR/mv2p_count.out" 2>&1 ) &
  pids+=($!)
  for p in "${pids[@]}"; do wait "$p"; done
  # aggregate round: report best per n + route any candidates
  for ns in 14 15 16 17 18; do
    best=$(grep -h "best_energy" "$DIR"/mv2p_n${ns}_*.out 2>/dev/null | grep -oE "best_energy[^ ]*=[0-9]+" | sort -t= -k2 -n | head -1)
    [ -n "$best" ] && log "round $round n=$ns best: $best"
  done
  grep -E "OVERALL BEST|WITNESS CANDIDATE" "$DIR"/mv2p_count.out 2>/dev/null | tail -2 >> "$LOG"
  route_candidates
  # route count's text candidates too
  python3 - <<'PY' >> "$LOG" 2>&1
import re, sys, os
sys.path.insert(0, "/Users/patrickkavanagh/math/analysis/e944/team")
from marathon_v2 import handle_candidate
p="/Users/patrickkavanagh/math/analysis/e944/team/mv2p_count.out"
if os.path.exists(p):
    txt=open(p).read()
    for m in re.finditer(r"WITNESS CANDIDATE.*?edges=(\[\(.*?\)\])", txt, re.S):
        try:
            edges=eval(m.group(1)); n=1+max(max(a,b) for a,b in edges)
            import networkx as nx
            G=nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges)
            g6=nx.to_graph6_bytes(G,header=False).decode().strip()
            handle_candidate(g6, edges, n, "count_SA")
        except Exception as e: print(f"[route count ERR] {e}")
PY
  if ls "$DIR"/WITNESS_n*.json >/dev/null 2>&1; then
    log "WITNESS FILE PRESENT — pausing for manual alert"; sleep 3600; fi
done
