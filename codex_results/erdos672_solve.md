**Code**
- `scripts/erdos672_search.py:1` does (i) exhaustive search over positive `n,d` with `n+3d <= max_term`, `gcd(n,d)=1`, checking `n(n+d)(n+2d)(n+3d)=y^3`, and (ii) modular “obstruction” checks.
- Run:
  - `python scripts/erdos672_search.py search --max-term 50000 --mod-filter 819`
  - `python scripts/erdos672_search.py modcheck --search-up-to 5000`

**Computations (ran)**
- Exhaustive search:
  - `n+3d <= 20000` (66,656,667 `(n,d)` pairs): no solutions found.
  - `n+3d <= 50000` (416,641,667 `(n,d)` pairs): no solutions found.
- Modular obstructions:
  - `m=7,8,9,13` all allow (e.g. `(n,d)≡(1,2) (mod 7)` gives product `≡0`; `(1,3) (mod 9)` gives `≡1`; `(1,2) (mod 13)` gives `≡1`).
  - In fact **no modulus `m <= 5000`** gives a pure congruence obstruction (script found none).

**Algebraic structure**
- Correct difference-of-squares factorization:
  - `n(n+d)(n+2d)(n+3d) = (n^2+3nd)(n^2+3nd+2d^2) = (n^2+3nd+d^2)^2 - d^4`.
  - Let `Y := n^2+3nd+d^2` and `X := y`. Then `Y^2 = X^3 + d^4` (an elliptic curve with `j=0`).
- Let `A := n(n+3d)` and `B := (n+d)(n+2d)`. Then `AB=y^3` and `B-A=2d^2`.
  - With `gcd(n,d)=1`, one checks `gcd(A,B)=1` if `d` even, and `gcd(A,B)=2` if `d` odd.
  - Consequences:
    - `d` even ⇒ `A=a^3`, `B=b^3`, so `b^3-a^3 = 2d^2`.
    - `d` odd ⇒ `A=2^α a^3`, `B=2^β b^3` with `a,b` odd, `min(α,β)=1`, and `α+β ≡ 0 (mod 3)`.

**Mod-prime facts (why small-modulus killing looks unlikely)**
- For any prime `p>=5`, `p` can divide at most one of `n,n+d,n+2d,n+3d` (differences are `d,2d,3d`), so in any genuine solution each term’s `p`-adic valuation must already be `≡0 (mod 3)`.
- Equivalently each term has shape `2^{e_i} 3^{f_i} u_i^3`; after stripping cube factors, the cube-free part divides `36`.

**Proof-strategy direction (Fermat/descent style)**
- Write `t_i:=n+id = s_i u_i^3` with `s_i ∈ {1,2,3,4,6,9,12,18,36}` (cube-free 2–3 part). The AP relations give two signature-(3,3,3) equations:
  - `s_0 u_0^3 + s_2 u_2^3 = 2 s_1 u_1^3`,
  - `s_1 u_1^3 + s_3 u_3^3 = 2 s_2 u_2^3`.
  Each fixed coefficient pattern is an elliptic curve (still `j=0`), suggesting: enumerate the finitely many `(s_0,s_1,s_2,s_3)` patterns and attack via 3-descent in `ℤ[ω]` / integral-point computations plus `gcd(n,d)=1`.
- In the `d` even branch, descent can start from `(b-a)(b^2+ab+a^2)=2d^2` (gcd of the two factors is `1` or `3`), reducing to a small number of conic/elliptic subproblems.

If you want, I can extend `scripts/erdos672_search.py:1` to explicitly exploit the “cube-free part divides 36” reduction (enumerate `s_i` patterns and search in `u_i`), which should let you push far beyond the `n+3d<=50000` brute-force regime.