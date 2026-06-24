1. For positive integers,
\[
\operatorname{rad}(m)=\prod_{p\mid m} p,
\]
so `rad(m)` records exactly the set of primes dividing `m`. Hence
\[
\operatorname{rad}(a)=\operatorname{rad}(b)
\iff
\{p:p\mid a\}=\{p:p\mid b\}.
\]

2. Therefore your key lemma is correct, in a stronger form:

\[
\gcd(a,b)=1 \text{ and } \operatorname{rad}(a)=\operatorname{rad}(b)
\implies a=b=1.
\]

Proof: if `a>1`, pick a prime `p|a`. Then `p|rad(a)=rad(b)`, so `p|b`, contradicting `gcd(a,b)=1`. Thus `a=1`, and then `rad(b)=rad(a)=1`, so `b=1`.

3. So there is no positive integer `n` with
\[
\operatorname{rad}(n)=\operatorname{rad}(n+1),
\]
hence certainly no positive `n` with
\[
\operatorname{rad}(n)=\operatorname{rad}(n+1)=\operatorname{rad}(n+2).
\]

4. `n=1` is not an exception:
\[
(\operatorname{rad}(1),\operatorname{rad}(2),\operatorname{rad}(3))=(1,2,3).
\]

5. So the statement you wrote down has an immediate negative answer.

6. But this is not Erdős Problem 850. As listed in the current Erdős problems database, the problem is:

Do there exist distinct positive integers `x ≠ y` such that
\[
\operatorname{rad}(x+i)=\operatorname{rad}(y+i)\quad\text{for }i=0,1,2?
\]

Equivalently, `x` and `y` have the same prime divisors, also `x+1` and `y+1`, and also `x+2` and `y+2`. This compares two different 3-blocks, not three consecutive integers to each other.

7. So the coprimality obstruction does not apply to Erdős 850. It is not about `rad(n)=rad(n+1)=rad(n+2)`, not about `rad(n(n+1)(n+2))` being small, and not about the largest prime factor `P(n)`. For the 2-term version there are many examples; for the 3-term version, the database lists it as open as of March 13, 2026. It also notes a conditional negative result under a strong ABC-type hypothesis.

Sources: [Erdős Problem #850](https://www.erdosproblems.com/850), [OEIS A343101](https://oeis.org/A343101).