Yes. This problem is already settled: there are no odd unitary perfect numbers.

Using your factorization,
\[
\sigma^*(n)=\prod_{i=1}^k (1+p_i^{a_i})=2n
\]
for
\[
n=\prod_{i=1}^k p_i^{a_i}
\]
with all \(p_i\) odd.

Now take \(2\)-adic valuations:
\[
1=v_2(2n)=v_2(\sigma^*(n))=\sum_{i=1}^k v_2(1+p_i^{a_i}).
\]

For an odd prime \(p\),
\[
v_2(1+p^a)=
\begin{cases}
1, & a \text{ even},\\
v_2(p+1), & a \text{ odd},
\end{cases}
\]
so every summand is at least \(1\). Therefore the sum can equal \(1\) only if \(k=1\).

So an odd unitary perfect number would have to be a single prime power \(n=p^a\). But then
\[
\sigma^*(p^a)=1+p^a,
\]
and unitary perfectness would force
\[
1+p^a=2p^a,
\]
i.e.
\[
1=p^a,
\]
impossible.

So the \(2\)-adic constraint does not just give a lower bound on the number of prime factors. It collapses the odd case to one prime-power component and then gives an immediate contradiction.

Point 6 is therefore based on a different problem or a misremembered citation. For unitary perfect numbers, the odd case was already ruled out by Subbarao and Warren in 1966. If you instead mean a sixth unitary perfect number, Wall proved in 1988 that any new unitary perfect number must have at least nine odd components; I did not find a later published improvement to that bound in the sources I checked.

Sources: [Subbarao-Warren 1966](https://doi.org/10.4153/CMB-1966-018-4), [Wall 1988](https://www.fq.math.ca/Scanned/26-4/wall.pdf)