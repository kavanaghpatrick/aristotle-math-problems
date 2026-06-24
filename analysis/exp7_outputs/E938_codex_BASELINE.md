This problem appears open in its stated form. I do not know a direct proof of finiteness, and a proof would need to control gaps between powerful numbers in a much sharper way than current elementary methods allow.

Here is a small unconditional result that can be proved directly.

**Claim.** There are no three consecutive powerful numbers in arithmetic progression with common difference `1`.

**Proof.** Suppose `n, n+1, n+2` are all powerful. Among three consecutive integers, exactly one is congruent to `2 mod 4`. Call it `m`.

But no powerful number is congruent to `2 mod 4`. Indeed, if `m` is even and powerful, then the prime `2` divides `m`, so by definition `2^2 = 4` must divide `m`. Thus every even powerful number is divisible by `4`, hence is congruent to `0 mod 4`, never `2 mod 4`.

This contradicts the existence of the term `m`. Therefore no three consecutive integers can all be powerful, so no consecutive powerful-number arithmetic progression has common difference `1`. ∎

A slightly broader unconditional observation is also immediate: if `x, x+d, x+2d` are powerful and `d` is odd, then the parities are alternating. The even term or terms must all be divisible by `4`, which forces congruence restrictions modulo `4`, but these restrictions alone do not rule out all odd `d`.

What remains open is the full Erdős 938 question:

Whether there are only finitely many triples

```text
n_k, n_{k+1}, n_{k+2}
```

that are consecutive in the ordered sequence of powerful numbers and satisfy

```text
n_{k+1} - n_k = n_{k+2} - n_{k+1}.
```

The hard part is not merely producing or excluding three powerful numbers in arithmetic progression. Powerful numbers can occur in arithmetic progressions. The extra condition is that no other powerful number lies between the first and second or between the second and third. Proving finiteness would require strong control over local spacing patterns of powerful numbers, not just over individual Diophantine equations.