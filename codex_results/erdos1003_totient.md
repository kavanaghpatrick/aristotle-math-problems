**Code**
- Search script: [scripts/erdos1003_search.py](/Users/patrickkavanagh/math/scripts/erdos1003_search.py)
- Main run:
  - `python3 scripts/erdos1003_search.py --limit 10000000 --show 0 --skip-crt`

**Exact hits up to 10^7**
- Count: `142`
- Values:
```text
1, 3, 15, 104, 164, 194, 255, 495, 584, 975, 2204, 2625, 2834, 3255, 3705,
5186, 5187, 10604, 11715, 13365, 18315, 22935, 25545, 32864, 38804, 39524,
46215, 48704, 49215, 49335, 56864, 57584, 57645, 64004, 65535, 73124, 105524,
107864, 123824, 131144, 164175, 184635, 198315, 214334, 215775, 256274, 286995,
307395, 319275, 347324, 388245, 397485, 407924, 415275, 454124, 491535, 524432,
525986, 546272, 568815, 589407, 679496, 686985, 840255, 914175, 936494, 952575,
983775, 1025504, 1091684, 1231424, 1259642, 1276904, 1390724, 1405845, 1574727,
1659585, 1759874, 1788254, 1925564, 2123583, 2200694, 2388044, 2521694, 2539004,
2619705, 2648204, 2759925, 2792144, 2822715, 2847584, 3104744, 3137355, 3170936,
3240614, 3289934, 3653564, 3693525, 3794834, 3877184, 3988424, 4002405, 4034744,
4163355, 4328804, 4447064, 4498935, 4626195, 4695704, 5003744, 5110664, 5198024,
5295884, 5466824, 5577825, 5683184, 5710088, 5781434, 5861583, 6235215, 6245546,
6312915, 6315308, 6372794, 6444615, 6475455, 6986888, 7033256, 7098104, 7303334,
7378371, 7823205, 7939244, 8018144, 8111024, 8338394, 8380448, 8385975, 8448255,
8698095, 9512144, 9718904
```

**Growth in the computed range**
- `<= 10`: `2`
- `<= 10^2`: `3`
- `<= 10^3`: `10`
- `<= 10^4`: `17`
- `<= 10^5`: `36`
- `<= 10^6`: `68`
- `<= 10^7`: `142`

Empirically the count keeps growing, but this computation alone does not point to a clean density law.

**Structure visible in the data**
1. Nontrivial values are always even.
   For `n >= 2`, both `phi(n)` and `phi(n+1)` are even, so any equality is between even numbers.

2. There is one striking exact subfamily in-range:
   - `3 = 2^2 - 1`
   - `15 = 2^4 - 1`
   - `255 = 2^8 - 1`
   - `65535 = 2^16 - 1`

   These are the cases `n+1 = 2^(2^k)`. Write the Fermat numbers as `F_j = 2^(2^j) + 1`. The identity
   ```text
   F_0 F_1 ... F_(k-1) = F_k - 2 = 2^(2^k) - 1
   ```
   gives
   ```text
   n = F_0 F_1 ... F_(k-1),   n+1 = 2^(2^k).
   ```
   If each `F_j` for `j < k` is prime, then
   ```text
   phi(n) = Π (F_j - 1) = Π 2^(2^j) = 2^(2^k - 1) = phi(n+1).
   ```
   Unconditionally this explains the four visible hits above, since only `F_0,...,F_4` are known to be prime. This is the cleanest exact family found in the search, but it is not an infinite family unless infinitely many initial Fermat numbers are prime, which is not known and is widely doubted.

3. Apart from the Fermat-pattern hits, most solutions are mixed-composite.
   In the `<= 10^7` sample:
   - `omega(n)` is usually `3` or `4`.
   - `omega(n+1)` is usually `3`, `4`, or `5`.
   - The only consecutive pair of hits is `(5186, 5187)`.

   So the data does not suggest a simple arithmetic progression or a single low-complexity template.

**CRT construction attempt**
Try the simplest CRT setup:
```text
n = A u,   n+1 = B v,
```
with `gcd(A,B)=1` fixed and `u,v` prime.

CRT forces `n` into one class modulo `AB`, so
```text
u = u0 + t B,   v = v0 + t A
```
for a single integer parameter `t`.

If `gcd(A,u)=gcd(B,v)=1`, then
```text
phi(n)   = phi(A)(u-1),
phi(n+1) = phi(B)(v-1).
```
Hence `phi(n)=phi(n+1)` becomes
```text
(B phi(A) - A phi(B)) t = phi(B)(v0-1) - phi(A)(u0-1).
```
This is linear in `t`, so for fixed `A,B` there is at most one candidate unless
```text
B phi(A) = A phi(B).
```
But
```text
phi(m)/m = Π_{p|m} (1 - 1/p),
```
so `B phi(A) = A phi(B)` means `A` and `B` have the same set of prime divisors. Since `gcd(A,B)=1`, that can only happen in the trivial case `A=B=1`.

So this CRT strategy can recover isolated examples, but it cannot produce an infinite family.

Examples it does recover:
- `104 = 8 * 13`, `105 = 15 * 7`, and `phi(104)=phi(105)=48`
- `164 = 4 * 41`, `165 = 15 * 11`, and `phi(164)=phi(165)=80`
- `194 = 2 * 97`, `195 = 15 * 13`, and `phi(194)=phi(195)=96`

This is why the obvious "fix some kernels and let the remaining primes vary by CRT" idea stalls immediately: the totient equality is too rigid.

**Bottom line**
- Exhaustive search to `10^7` finds `142` solutions.
- The data supports the known belief that solutions are sparse.
- The only especially clean exact family visible in the data is the finite Fermat-number pattern above.
- The first natural CRT-based family with fixed kernels and one moving prime on each side provably gives only sporadic solutions, not infinitely many.
