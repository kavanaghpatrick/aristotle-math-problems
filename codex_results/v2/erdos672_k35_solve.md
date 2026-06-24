**Barrier at `k=35`**

What breaks at `k=35` is not the underlying Diophantine reduction. The Bennett-Bruin-Gyory-Hajdu method rewrites
\[
n+id=a_i x_i^\ell
\]
with the `a_i` supported on small primes, then manufactures finitely many ternary equations of signatures `(\ell,\ell,\ell)` and `(\ell,\ell,2)` and attacks those with Frey curves, modularity, and local sieves. That is the core 2006 method.

The 2009 Gyory-Hajdu-Pinter paper pushes the same framework to `4 <= k <= 34` by algorithmically choosing index sets and running a much larger computational elimination. Their abstract is explicit: they believe the method could likely go further, but they stopped because of computational time. They even report runtimes growing from hours at `k=31` to about a week at `k=33,34`. So the `k=35` obstruction is a case-explosion/runtime barrier in the modular-sieve search over many ternary equations, not a theorem saying the method fundamentally fails there. A second practical issue is that for some exponents, especially `\ell=5`, the general modular machinery gives much less automatic information, so more equations have to be handled one by one.

Sources:
- Bennett et al. 2006: https://webspace.maths.qmul.ac.uk/j.e.cream/files/2006Powersfromproductsofconsecutiveterms.pdf
- Gyory-Hajdu-Pinter 2009: https://shrek.unideb.hu/~pinter/pub_algebra_numbertheory/perfectpowers.pdf

**Code**

I added [erdos672_small_verify.py](/Users/patrickkavanagh/math/scripts/erdos672_small_verify.py). It does exact bounded verification by factoring each AP term and checking whether the combined prime-exponent vector has gcd divisible by `l`. No floating-point perfect-power test is used.

Useful commands:
```bash
python3 scripts/erdos672_small_verify.py check --n 1 --d 24 --k 3 --l 2
python3 scripts/erdos672_small_verify.py search --min-k 4 --max-k 8 --max-d 40 --max-term 200 --min-l 2 --max-l 8
python3 scripts/erdos672_small_verify.py search --min-k 35 --max-k 35 --max-d 10 --max-term 500 --min-l 2 --max-l 8
```

**What it verified**

The script compiled cleanly with `python3 -m py_compile`.

Runs:
- `k=3, l=2, n=1, d=24`: verified `1*25*49 = 1225 = 35^2`.
- Bounded search `4 <= k <= 8`, `d <= 40`, `n+(k-1)d <= 200`, `2 <= l <= 8`: no hits.
- Bounded search `k=35`, `d <= 10`, `n+34d <= 500`, `2 <= l <= 8`: no hits.

One extra sanity hit in the `k=3` range:
- `18*25*32 = 14400 = 120^2`.

If you want, I can extend the script with progress reporting and a faster residue sieve so we can push the `k=35` search bound much higher.