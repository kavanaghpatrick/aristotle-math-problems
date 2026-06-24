ABC gives the finiteness immediately, but point 3 needs one correction: your `abc` quality does not go to infinity. The radical bound only gives a quality bounded below by `2-o(1)`, and that is already enough.

**`2^n+1`**
- Let `c=2^n+1`. If `c` is powerful, then `rad(c) <= c^{1/2}`.
- Hence `rad(1·2^n·(-c)) = 2 rad(c) <= 2c^{1/2}`.
- `abc` then gives `c <<_eps rad(...)^{1+eps} <<_eps c^{(1+eps)/2}`.
- For any fixed `eps<1`, this fails for large `n`. So `abc` implies only finitely many `n`.

**Valuations / Wieferich**
- Point 2 needs refinement. If `p|2^n+1`, let `d` be minimal with `p|2^d+1`. Then `d|n`, `n/d` is odd, and
  `v_p(2^n+1)=v_p(2^d+1)+v_p(n/d)`.
- So exponent `>=2` can come from two different sources:
  - a genuine lift `v_p(2^d+1)>=2`;
  - or just the quotient `p|n/d`.
- Example: `2^3+1=3^2`, but `3` is not Wieferich; here `d=1`, so `v_3(2^3+1)=1+v_3(3)=2`.
- Concrete local consequence: if `n` is odd and `2^n+1` is powerful, then `3|n`, since `v_3(2^n+1)=1+v_3(n)`.
- The rigid obstruction is only at the primitive level. If `p` is a primitive divisor of `2^n+1` (`ord_p(2)=2n`) and `p^2|2^n+1`, then `p` is a base-2 Wieferich prime: `2^{p-1} ≡ 1 (mod p^2)`.
- By Zsigmondy, this applies for every `n>3` (the exceptional plus-case is `2^3+1=9`). So any powerful `2^n+1` with `n>3` forces at least one primitive base-2 Wieferich prime `p ≡ 1 (mod 2n)`; in fact every primitive divisor of `Φ_{2n}(2)` must be Wieferich.

**What is known unconditionally**
- No unconditional finiteness theorem is known for powerful values of `2^n+1`.
- Perfect powers are much easier: `2^n+1 = y^m`, `m>1`, has only `2^3+1=3^2` by Catalan-Mihăilescu.
- Stewart / Stewart-Tijdeman style results give primitive divisors and very large prime factors of recurrence terms. That is not enough here.
- Exact missing ingredient: a theorem that for all large `n`, `Φ_{2n}(2)` has some prime divisor with valuation exactly `1`.
- So the gap is `p`-adic, not size-theoretic. Large prime factors do not rule out squarefullness.

**Granville-Langevin**
- I do not see a direct payoff here from the standard polynomial-values form of that conjectural circle. `2^n+1` is not a polynomial in `n`.
- The direct `abc` argument is cleaner.
- Another conditional route: finitely many base-2 Wieferich primes would already imply finitely many powerful `2^n+1`.

**`n!+1`**
- Elementary Euclid-style constraints: if `p|n!+1`, then `p>n`. So if `n!+1` is powerful, all its prime divisors are `>n` and occur with exponent at least `2`.
- That alone is far from enough: there are small examples such as `4!+1=25`, `5!+1=121`, `7!+1=5041`.
- Unconditionally, this variant is already solved. Cushing-Pascoe proved that for each fixed `k`, only finitely many factorials differ by `k` from a powerful number. Taking `k=1` gives finitely many `n` with `n!+1` powerful.

**Sources**
- [Cushing, “Powerful numbers near factorials”](https://arxiv.org/abs/2005.07321)
- [Stewart, “On prime factors of terms of binary recurrence sequences”](https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/onprimef.pdf)

**Next Steps**
1. Formalize the primitive-divisor/Wieferich reduction as a clean lemma-proposition proof.
2. Write the `abc` argument as a one-page note with the precise `quality -> 2` correction.
3. Push the unconditional side by isolating what would follow from any non-Wieferich primitive divisor theorem for `Φ_{2n}(2)`.