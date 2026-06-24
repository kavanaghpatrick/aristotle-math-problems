#!/bin/bash
# Erdős 647 production sieve: report n in (10^10, 10^12].
# Seeded with running_max over m <= 10^10 = 10000000332 (from validation run, A087280-confirmed).
# nice'd background CPU; logs to sieve.log. Single sequential process (running-max dependency).
set -e
cd "$(dirname "$0")"
SEED=10000000332
LO=10000000000        # 10^10  (report floor; start = LO+1)
HI=1000000000000      # 10^12
SEG=16777216          # 16M segment (~200MB RSS)
LOG=sieve.log

echo "=== Erdős 647 production sieve START $(date -u +%Y-%m-%dT%H:%M:%SZ) ===" >> "$LOG"
echo "range report n in ($LO, $HI], seed running_max=$SEED, seg=$SEG" >> "$LOG"
echo "predicate: max_{m<n}(m+tau(m)) <= n+2 ; empty => failed_approaches + memo (PREREGISTRATION.md)" >> "$LOG"
nice -n 15 ./target/release/e647_sieve "$LO" "$HI" --seg "$SEG" --seed-runmax "$SEED" --start $((LO+1)) >> "$LOG" 2>&1
echo "=== Erdős 647 production sieve DONE $(date -u +%Y-%m-%dT%H:%M:%SZ) exit=$? ===" >> "$LOG"
