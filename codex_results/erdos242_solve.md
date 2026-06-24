**Reality Check**
- The Erdős–Straus conjecture is still open, so I can’t give a proof that covers *all* primes `p ≡ 1 (mod 24)`; what I *can* do is build a systematic search, run it at scale, and extract repeatable (provable) constructions from what it finds.

**Code**
- Search script: `experiments/erdos_straus/search.py:1` (implements the identity `(Ay-B)(Az-B)=B^2` search; tries “Type I” first, then a general divisor-witness method).
- Write-up of the algebra + explicit families: `experiments/erdos_straus/README.md:1`.

Run:
- `python3 experiments/erdos_straus/search.py --limit 10000000 --amax 200 --show 0`  (see `experiments/erdos_straus/README.md:113`)

**What I Ran (Results)**
- For primes `p ≡ 1 (mod 24)` with `p ≤ 10,000,000`: **82,887 / 82,887 solved** using the “near-quarter” form `x=(p+a)/4` with `a≤200`; the **maximum `a` actually needed was `107`**.
- The `a` distribution is dominated by tiny values: `a=3` (47,137 primes), `a=7` (28,606), `a=11` (4,463), then rapidly decays.

**Patterns (Structure)**
1) **“Near-quarter” denominator**  
   - Almost always the smallest denominator is `x=(p+a)/4` with very small `a≡3 (mod 4)` (so `x` is just above `p/4`).

2) **Type I family (very explicit, provable)**  
   If `a=d+e` with `d|x` and `e|x`, then
   - `4/p = 1/x + 1/(p x / d) + 1/(p x / e)`.  
   This is the dominant structured pattern the search finds (e.g. `(a;d,e)=(7;2,5)`).

   Example (found by Type I):
   - `4/73 = 1/20 + 1/730 + 1/292`.

3) **Divisor-witness family (general, provable once a witness exists)**  
   With `A=4x-p` and `B=px`, if you find `u | B^2` with
   - `A | (B+u)` and `A | (B + B^2/u)`,
   then `y=(B+u)/A`, `z=(B+B^2/u)/A` works. This is what the script systematically searches.

   Two especially clean subfamilies that show up a lot (and are proved in `experiments/erdos_straus/README.md:67`):
   - **`u=p`** works whenever `a | (x+1)`, giving `y=p(x+1)/a`, `z=px(x+1)/a`.
   - **`a=3` characterization:** for `p≡1 (mod24)`, `a=3` works **iff** `x=(p+3)/4` has a prime factor `q≡2 (mod3)`; then  
     `y=(px+q)/3`, `z=(px/q)*y`.

**Unified “Algorithm” (what’s actually implemented)**
- For each prime `p≡1 (mod24)`, try small `a=3,7,11,…` up to `amax`; set `x=(p+a)/4`.
- First try the **Type I** shortcut (`a=d+e` with `d|x,e|x`); if that fails, use the **divisor-witness** search on divisors of `(px)^2`.  
This found solutions for all primes in-range up to `10^7` with `amax=200`, and empirically never needed `a>107`.

**Limit**
- What’s proved here is: *each construction is correct when its congruence/divisibility hypotheses hold*. What remains open (and I did not prove) is: *that such hypotheses can always be met for every prime `p≡1 (mod24)`*.