#!/bin/bash
# e944 MARATHON v2 driver (hunter). Long-running, nice'd, CPU-driven (measured fastest), GPU engines
# as cross-verifiers on hits only.
#
# Per the bench: geng enumeration is INFEASIBLE at n=14-18 (even 6-regular n=14 times out to count),
# so the proposal stream is the ANNEALER (witness_anneal irregular δ≥6 + count's min-conflict SA),
# each proposal fully-checked by the CPU floor_worker predicate (the validated fast witness check).
# ANY 0-critical-edge survivor routes through marathon_v2.handle_candidate -> TRIPLE-VERIFY
# (checkers bt+sat + my 3^n GPU kernel + BHK, all must agree) -> skeptic adjudicator -> ALERT.
#
# Run: nohup nice -n 19 ./marathon_v2_run.sh > /dev/null 2>&1 &
DIR=/Users/patrickkavanagh/math/analysis/e944/team
LOG=$DIR/search_n14plus.log
cd "$DIR" || exit 1
log() { echo "[$(date '+%Y-%m-%d %H:%M:%S')] $*" >> "$LOG"; }

# After each annealer run, scan its output for a CANDIDATE/WITNESS file and route through the gate.
route_candidates() {
  local src="$1"
  # witness_anneal writes CANDIDATE_*.json / WITNESS_*.json on a 0-critical hit. Route any candidate.
  for cf in "$DIR"/CANDIDATE_*.json "$DIR"/CANDIDATE_rev_*.json "$DIR"/CANDIDATE_grow_*.json; do
    [ -e "$cf" ] || continue
    python3 - "$cf" "$src" <<'PY' >> "$LOG" 2>&1
import sys, json
sys.path.insert(0, "/Users/patrickkavanagh/math/analysis/e944/team")
from marathon_v2 import handle_candidate
d = json.load(open(sys.argv[1]))
handle_candidate(d.get("g6",""), [tuple(e) for e in d["edges"]], d["n"], sys.argv[2])
PY
    mv "$cf" "$cf.routed" 2>/dev/null
  done
}

log "=== MARATHON v2 START (CPU-driven, GPU cross-verify on hits) PID $$ ==="
log "    bench: geng infeasible n>=14; proposal stream = annealer; predicate = floor_worker (CPU)"
log "    gate on hit: checkers bt+sat + 3^n GPU kernel + BHK (all agree) -> skeptic adjudicate -> ALERT"
round=0
while true; do
  round=$((round+1))
  seed=$((round * 31 + 17))
  # PRIMARY BAND n=14-18, annealer proposal stream (irregular δ≥6), CPU floor_worker predicate inside.
  for n in 14 15 16 17 18; do
    log "round $round: witness_anneal n=$n seed=$seed (240s)"
    timeout 300 nice -n 19 python3 "$DIR/witness_anneal.py" "$n" --time 240 --seed "$seed" \
      > "$DIR/mv2_wa_n${n}.out" 2>&1
    tail -1 "$DIR/mv2_wa_n${n}.out" >> "$LOG"
    route_candidates "witness_anneal_n${n}"
    if ls "$DIR"/WITNESS_n*.json >/dev/null 2>&1; then
      log "WITNESS FILE PRESENT — pausing for manual alert"; sleep 3600; fi
  done
  # count's min-conflict SA sweep (n=12-18 internal, exact objective)
  log "round $round: count min-conflict SA sweep"
  timeout 900 nice -n 19 python3 "$DIR/count_anneal_mindeg6.py" > "$DIR/mv2_count.out" 2>&1
  grep -E "OVERALL BEST|WITNESS CANDIDATE" "$DIR/mv2_count.out" | tail -3 >> "$LOG"
  # count prints "WITNESS CANDIDATE ... edges=[...]" — extract & route
  python3 - <<'PY' >> "$LOG" 2>&1
import re, sys
sys.path.insert(0, "/Users/patrickkavanagh/math/analysis/e944/team")
from marathon_v2 import handle_candidate
txt = open("/Users/patrickkavanagh/math/analysis/e944/team/mv2_count.out").read()
for m in re.finditer(r"WITNESS CANDIDATE.*?edges=(\[\(.*?\)\])", txt, re.S):
    try:
        edges = eval(m.group(1)); n = 1 + max(max(a, b) for a, b in edges)
        import networkx as nx
        G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges)
        g6 = nx.to_graph6_bytes(G, header=False).decode().strip()
        handle_candidate(g6, edges, n, "count_min_conflict_SA")
    except Exception as e:
        print(f"[route count cand ERR] {e}")
PY
  if ls "$DIR"/WITNESS_n*.json >/dev/null 2>&1; then
    log "WITNESS FILE PRESENT — pausing for manual alert"; sleep 3600; fi
done
