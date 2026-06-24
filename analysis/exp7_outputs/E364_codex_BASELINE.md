This problem is open. I cannot prove the stated assertion unconditionally, and a proof would settle a known Erdős problem. Here is a small unconditional restriction that follows directly from the definition.

**Claim.** If three consecutive powerful numbers `n, n+1, n+2` exist, then `n` is odd, `n+1` is divisible by `4`, and
\[
n \equiv 7,27,\text{ or }35 \pmod{36}.
\]

**Proof.** A powerful even number must be divisible by `4`, since the prime `2` must occur with exponent at least `2`.

Suppose first that `n` is even. Then both `n` and `n+2` are even. Since both are assumed powerful, both must be divisible by `4`. But two integers differing by `2` cannot both be divisible by `4`. Contradiction. Hence `n` must be odd.

Therefore `n+1` is even, and since it is powerful, `4 | n+1`. Thus
\[
n \equiv 3 \pmod 4.
\]

Now use the prime `3`. Among `n, n+1, n+2`, exactly one is divisible by `3`. If that integer is powerful, it must actually be divisible by `9`.

There are three cases:

- If `3 | n`, then `9 | n`, so `n ≡ 0 mod 9`.
- If `3 | n+1`, then `9 | n+1`, so `n ≡ 8 mod 9`.
- If `3 | n+2`, then `9 | n+2`, so `n ≡ 7 mod 9`.

Combining these with `n ≡ 3 mod 4`, we get
\[
n \equiv 27,35,7 \pmod{36},
\]
respectively. This proves the claim.

More generally, for every prime `p`, a counterexample must satisfy:
\[
n+i \equiv 0 \pmod p \implies n+i \equiv 0 \pmod {p^2}
\]
for `i = 0,1,2`. Equivalently, modulo `p^2`, `n` may not lie in the residue classes `0,-1,-2 mod p` unless it lies in the corresponding class modulo `p^2`.

What remains open is the global step: proving that these local congruence restrictions, for all primes simultaneously, cannot be satisfied by three consecutive integers. No unconditional argument is known that rules this out in full.