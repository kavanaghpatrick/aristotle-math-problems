**Status**

As of **March 13, 2026**, this is still **open**. So the statement

\[
\sum_{n=2}^\infty \frac{1}{n!-1}\ \text{is irrational}
\]

has **not** been proved or disproved. Erdős raised it as Problem 68, and the special case \(t=-1\) sits inside his broader conjecture on \(\sum 1/(n!+t)\).

**What we can prove**

Let

\[
S:=\sum_{n=2}^\infty \frac{1}{n!-1}, \qquad t_n:=\frac{1}{n!-1}.
\]

1. **The series converges extremely fast.**

For \(n\ge 2\),

\[
\frac1{n!} < \frac1{n!-1} \le \frac{2}{n!}.
\]

So \(S\) converges absolutely, and if

\[
R_N:=\sum_{n>N}\frac1{n!-1},
\]

then

\[
R_N < 2\sum_{n>N}\frac1{n!}.
\]

Now for \(N\ge 1\),

\[
\sum_{n>N}\frac1{n!}
= \sum_{k=1}^\infty \frac1{(N+k)!}
\le \frac1{N!}\sum_{k=1}^\infty \frac1{(N+1)^k}
= \frac1{N\,N!}.
\]

Hence the rigorous tail bound

\[
\boxed{R_N < \frac{2}{N\,N!}}.
\]

2. **There is a useful geometric expansion.**

Since \(n!>1\),

\[
\frac{1}{n!-1}
= \frac{1/n!}{1-1/n!}
= \sum_{m=1}^\infty \frac{1}{(n!)^m}.
\]

Therefore

\[
S=\sum_{n=2}^\infty\sum_{m=1}^\infty \frac{1}{(n!)^m}.
\]

In particular,

\[
S=\sum_{n=2}^\infty \frac1{n!}
+\sum_{n=2}^\infty \frac{1}{n!(n!-1)}
=(e-2)+\sum_{n=2}^\infty \frac{1}{n!(n!-1)}.
\]

So \(S\) is \(e-2\) plus a positive correction term. This is suggestive, but it does **not** prove irrationality, because a positive real can still cancel irrationality in principle.

3. **Why standard Cantor/factorial-series arguments do not immediately apply.**

Classical irrationality proofs for series with rapidly growing denominators often rely on a divisibility chain such as \(q_n\mid q_{n+1}\). Here the natural denominators are

\[
q_n=n!-1,
\]

and they behave in the opposite way. In fact,

\[
\gcd(n!-1,(n+1)!-1)=1.
\]

Proof:

\[
(n+1)!-1-(n+1)(n!-1)=n,
\]

so any common divisor divides both \(n!-1\) and \(n\). But if \(d\mid n\), then \(n!\equiv 0\pmod d\), so \(n!-1\equiv -1\pmod d\), impossible unless \(d=1\).

So consecutive denominators are coprime. That kills the usual Cantor-series mechanism.

4. **Why the obvious “multiply by a denominator” strategy fails.**

For \(e=\sum 1/n!\), multiplying by \(N!\) makes the head integral and the tail tiny. Here neither natural choice works:

- Multiply by \(N!\): the tail is tiny, but the head \(\sum_{n\le N} N!/(n!-1)\) is not integral.
- Multiply by \(\prod_{n\le N}(n!-1)\): the head becomes integral, but the multiplier is so huge that the tail is no longer small enough to force a contradiction.

That is the core obstruction.

5. **Why Mahler-type methods are not currently available.**

Mahler’s method typically needs a function satisfying a functional equation like \(F(z^k)=R(z,F(z))\). A natural candidate here would be

\[
F(z)=\sum_{n=2}^\infty \frac1{n!-z},
\]

with \(F(1)=S\), but no useful Mahler-type functional equation is known for this \(F\). So the standard Mahler machine does not currently bite on this constant.

**Numerics**

Using exact rational partial sums and the bound above:

- \(S_{10}=1.253498728387292084008424952\ldots\), with error \(<5.52\times 10^{-8}\)
- \(S_{20}=1.253498755699953471622857957\ldots\), with error \(<4.11\times 10^{-20}\)

High-precision computation gives

\[
\boxed{
S \approx 1.2534987556999534716433609379057989403692322083320134
}
\]

The continued fraction begins

\[
[1;3,1,17,8,1,4,3,2,2,\dots]
\]

and the convergents look numerically generic; nothing like an obvious hidden rational relation appears. That is evidence, not proof.

**Python**

```python
from math import factorial
from fractions import Fraction
from decimal import Decimal, getcontext

def partial_sum_exact(N: int) -> Fraction:
    s = Fraction(0, 1)
    for n in range(2, N + 1):
        s += Fraction(1, factorial(n) - 1)
    return s

def partial_sum_decimal(N: int, prec: int = 80) -> Decimal:
    getcontext().prec = prec
    s = partial_sum_exact(N)
    return Decimal(s.numerator) / Decimal(s.denominator)

def tail_bound(N: int) -> Decimal:
    # Rigorous: sum_{n>N} 1/(n!-1) < 2/(N*N!)
    getcontext().prec = 80
    return Decimal(2) / (Decimal(N) * Decimal(factorial(N)))

def high_precision_value(terms: int = 60, prec: int = 120) -> Decimal:
    getcontext().prec = prec
    s = Decimal(0)
    for n in range(2, terms + 1):
        s += Decimal(1) / (Decimal(factorial(n)) - 1)
    return s

def continued_fraction_decimal(x: Decimal, steps: int = 20):
    cf = []
    y = x
    for _ in range(steps):
        a = int(y)
        cf.append(a)
        frac = y - a
        if frac == 0:
            break
        y = 1 / frac
    return cf

if __name__ == "__main__":
    for N in [5, 10, 15, 20]:
        sN = partial_sum_decimal(N, prec=60)
        err = tail_bound(N)
        print(f"N={N}")
        print("  S_N    =", sN)
        print("  error <", err)

    S = high_precision_value(terms=60, prec=100)
    print("\nApproximate value of S:")
    print(S)

    print("\nContinued fraction prefix:")
    print(continued_fraction_decimal(S, steps=20))
```

**Bottom line**

The claim is neither proved nor disproved at present. What we can show is:

1. the series converges very rapidly,
2. it has a clean factorial-power expansion,
3. the standard factorial-series and Mahler-style tools do not directly apply,
4. the main obstruction is arithmetic: \(n!-1\) lacks the divisibility structure those methods need.

**Sources**

- Erdős, *Some old and new problems in various branches of number theory* (1988): https://www.renyi.hu/~p_erdos/1988-22.pdf
- Erdős Problems, Problem 68: https://www.erdosproblems.com/68

If you want, I can go one step further and write up a more research-style note exploring possible p-adic or modular approaches and exactly where they break.