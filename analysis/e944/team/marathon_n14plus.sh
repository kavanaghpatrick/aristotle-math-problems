#!/bin/bash
# e944 OVERNIGHT MARATHON existence sampler (hunter, team-lead order).
# Long-running, nice'd, CPU-only. Loops two best-targeted searches over n=14-16 with rotating seeds,
# logs status to search_n14plus.log, and routes ANY 0-critical-edge candidate through the full
# verification gate (checkers.py dual-verify + skeptic_adjudicate.py) BEFORE any witness claim.
#
# Run:  nohup nice -n 19 ./marathon_n14plus.sh > /dev/null 2>&1 &
DIR=/Users/patrickkavanagh/math/analysis/e944/team
LOG=$DIR/search_n14plus.log
cd "$DIR" || exit 1

log() { echo "[$(date '+%Y-%m-%d %H:%M:%S')] $*" >> "$LOG"; }

# Verification gate: given a graph6 string, run checkers + adjudicator; only declare WITNESS if all agree.
gate() {
  local g6="$1" src="$2"
  log "CANDIDATE from $src g6=$g6 — running verification gate"
  python3 - "$g6" "$src" <<'PY' >> "$LOG" 2>&1
import sys
sys.path.insert(0, "/Users/patrickkavanagh/math/analysis/e944/team")
import networkx as nx
from checkers import chi_bt, is_erdos944_k_r1, chromatic_number_sat, is_k_colorable_sat
g6, src = sys.argv[1], sys.argv[2]
G = nx.from_graph6_bytes(g6.encode()); n = G.number_of_nodes()
H = nx.convert_node_labels_to_integers(G)
edges = [(min(u,v),max(u,v)) for u,v in H.edges()]
ok_bt = is_erdos944_k_r1(edges, n, 4, chi_fn=chi_bt)          # instrument 1: backtracking
# instrument 2: SAT chi path
def sat_witness(edges,n):
    if is_k_colorable_sat(edges,n,3): return False
    if not is_k_colorable_sat(edges,n,4): return False
    for v in range(n):
        rm={}; nn=0
        for x in range(n):
            if x!=v: rm[x]=nn; nn+=1
        sub=[(rm[a],rm[b]) for (a,b) in edges if a!=v and b!=v]
        if not is_k_colorable_sat(sub,nn,3): return False
    for (a,b) in edges:
        sub=[e for e in edges if e!=(a,b)]
        if is_k_colorable_sat(sub,n,3): return False
    return True
ok_sat = sat_witness(edges,n)
print(f"GATE g6={g6} src={src} n={n} checkers_bt={ok_bt} checkers_sat={ok_sat}")
if ok_bt and ok_sat:
    import json
    json.dump({"n":n,"edges":edges,"g6":g6,"src":src},
              open(f"/Users/patrickkavanagh/math/analysis/e944/team/WITNESS_n{n}.json","w"))
    print(f"!!! WITNESS PASSES checkers (both paths) — saved WITNESS_n{n}.json. NOW run skeptic_adjudicate.py --g6 {g6} and ALERT team-lead+algebra+skeptic. !!!")
else:
    print("candidate REJECTED by verification gate — not a witness")
PY
  # if a WITNESS file now exists, also run skeptic's adjudicator and shout in the log
  for wf in "$DIR"/WITNESS_n*.json; do
    [ -e "$wf" ] || continue
    local wg6
    wg6=$(python3 -c "import json,sys;print(json.load(open('$wf')).get('g6',''))" 2>/dev/null)
    if [ -n "$wg6" ]; then
      log "RUNNING skeptic_adjudicate.py on $wf"
      python3 "$DIR/skeptic_adjudicate.py" --g6 "$wg6" >> "$LOG" 2>&1
      log "*** WITNESS FILE PRESENT: $wf — ALERT team-lead + algebra + skeptic IMMEDIATELY ***"
    fi
  done
}

# Scan a sampler's output file for candidate markers and route any through the gate.
scan_out() {
  local f="$1" src="$2"
  [ -f "$f" ] || return
  # count/witness_anneal candidate markers: "WITNESS CANDIDATE", g6= lines, CANDIDATE_*.json
  grep -hoE "g6=[A-Za-z0-9_?@~{}|^\`-]+" "$f" 2>/dev/null | sed 's/g6=//' | sort -u | while read -r g6; do
    [ -n "$g6" ] && gate "$g6" "$src"
  done
}

log "=== MARATHON START (nice'd, n=14-16, irregular δ≥6 + count min-conflict SA) PID $$ ==="
round=0
while true; do
  round=$((round+1))
  seed=$((round * 7 + 13))
  for n in 14 15 16; do
    log "round $round: witness_anneal n=$n seed=$seed (300s)"
    timeout 360 nice -n 19 python3 "$DIR/witness_anneal.py" "$n" --time 300 --seed "$seed" \
      > "$DIR/marathon_wa_n${n}.out" 2>&1
    tail -1 "$DIR/marathon_wa_n${n}.out" >> "$LOG"
    # witness_anneal writes CANDIDATE_*/WITNESS_* itself; also scan its g6 lines
    scan_out "$DIR/marathon_wa_n${n}.out" "witness_anneal_n${n}"
    if ls "$DIR"/WITNESS_n*.json >/dev/null 2>&1; then
      log "WITNESS FILE DETECTED — pausing marathon, manual alert required"; sleep 3600; fi
  done
  # count's min-conflict SA sweep (self-loops n=12..18 internally, 120k iters each)
  log "round $round: count min-conflict SA sweep"
  timeout 900 nice -n 19 python3 "$DIR/count_anneal_mindeg6.py" > "$DIR/marathon_count.out" 2>&1
  grep -E "OVERALL BEST|WITNESS CANDIDATE" "$DIR/marathon_count.out" | tail -3 >> "$LOG"
  scan_out "$DIR/marathon_count.out" "count_min_conflict_SA"
  if ls "$DIR"/WITNESS_n*.json >/dev/null 2>&1; then
    log "WITNESS FILE DETECTED — pausing marathon, manual alert required"; sleep 3600; fi
done
