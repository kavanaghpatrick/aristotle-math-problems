"""
Check-window soundness for the 647 sieve.
Predicate: n is a witness iff for ALL m in [0,n): m + tau(m) <= n+2.
Equivalently: max_{m<n}(m + tau(m)) <= n+2.

KEY: a violation m+tau(m) > n+2 with m < n means tau(m) > n+2 - m = (n-m)+2.
For m far below n (n-m large), this needs tau(m) huge. tau(m) is bounded by TAU_MAX(N)
for m < N. So only m in [n - (TAU_MAX-2), n) can possibly violate => CHECK WINDOW.

We need TAU_MAX(N) = max tau(m) for m <= N, for N up to 10^12 (and headroom to 6.7e12).
Largest tau below N is achieved at highly composite numbers (HCNs). 
NOTE: hcn_tau_near_max is a BANNED false lemma -- we do NOT use an HCN list as a PROOF shortcut.
But for SIZING the window (an engineering parameter, re-validated by the running max), we may
look up the known max tau. The sieve itself recomputes the true running max; the window is just
'how far back to look', and we make it CONSERVATIVE + self-checking.
"""
# Known record divisor counts (max tau for n <= 10^k), from the HCN sequence (A002182/A066150).
# These are ENGINEERING bounds for window sizing, re-verified live by the sieve's running max.
known_maxtau = {
    10**9:  1344,
    10**10: 2304,
    10**11: 4032,
    10**12: 6720,
    10**13: 10752,
}
print("Max tau(m) for m <= N (HCN records, for window SIZING only — sieve re-verifies live):")
for N,t in known_maxtau.items():
    print(f"  N=10^{len(str(N))-1}: max tau = {t}  => check window needs >= {t} back")

# At N=10^12 max tau = 6720. So a violating m must have n-m+2 < tau(m) <= 6720 => n-m < 6718.
# Window [n-6718, n) suffices at 10^12. With headroom to 6.7e12 (max tau ~10752): window ~10750.
# We use a SAFE window W = 12000 across the whole run (covers up to ~1.5e13). Self-checking:
# the sieve asserts max tau seen in each segment < W-2; if ever violated, halt (window too small).
W = 12000
print(f"\nChosen check window W = {W} (covers max tau up to {W-2}, safe to ~1.5e13).")
print("Self-check tripwire: if any segment's max tau >= W-2, HALT (window too small) -- prevents")
print("a false 'witness' from a too-short window. This makes the window sound, not just heuristic.")

# Cost estimate: to decide each candidate n, we need tau(m) for m in [n-W, n). But we sieve
# tau over the WHOLE range anyway (segmented), maintaining a running max of m+tau(m). The
# witness test at n is just: running_max(m<n) <= n+2. So no separate window cost -- the running
# max over the full sieve IS the predicate. Window only matters for the CERTIFICATE on a hit.
print("""
SIEVE STRUCTURE (the actual algorithm):
  Segmented sieve of tau(m) over [25, 10^12] in blocks of size B (e.g. 10^8).
  Maintain running_max = max over all m seen so far of (m + tau(m)).
  For each n at a segment boundary: n is a witness iff running_max(m < n) <= n+2.
  Since running_max is monotone nondecreasing, once running_max > n+2 for the current n,
  ALL larger n up to the next running_max jump are also disqualified -- but we must check
  each n because n+2 grows by 1 each step. Concretely: n is a witness iff
  running_max_so_far <= n+2, evaluated at every n. The witnesses are exactly the n where
  the running max 'catches up'. This is O(N log log N) total (sieve cost), single pass.
""")
# How many ops? tau-sieve over N=10^12: ~N log log N ~ 10^12 * 3.3 ~ 3.3e12 increments.
import math
N=10**12
print(f"Total sieve work ~ N*sum(1/p) ~ {N*math.log(math.log(N)):.2e} increments (~{N*3.3/1e12:.1f}e12).")
print("Screen report estimate: 1-3e13 ops to 10^12, 'days on M-series Rust'. Consistent.")
