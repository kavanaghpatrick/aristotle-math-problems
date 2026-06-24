**Overview**

Assuming the standard distinct-moduli interpretation, the density route does **not** settle Erdős Problem 273. The key reason is simple:  
\[
\sum_{p\ge 5}\frac1{p-1}
\]
does **not** converge. It diverges.

Also: if “covering system” did **not** mean distinct moduli here, the problem would be trivial, since the four classes mod \(4\) already cover \(\mathbb Z\).

**Main points**

- Parity split is valid, but normalize it carefully.
- If \(a \pmod m\) has \(m\) even, it lies entirely in one parity class.
- So a distinct cover by moduli \(m=p-1\) splits into two disjoint covers of \(\mathbb Z\):
  \[
  \left\{\frac a2 \pmod{m/2}\right\}\quad\text{and}\quad \left\{\frac{a-1}2 \pmod{m/2}\right\}.
  \]
- Thus each parity class is a distinct covering system with moduli in
  \[
  \left\{\frac{p-1}{2}: p\ge 5 \text{ prime}\right\}=\{2,3,5,6,8,9,11,14,15,\dots\}.
  \]

- Density consequence:
  - On one parity class, a congruence mod \(m\) has relative density \(2/m\).
  - Therefore each parity class needs
    \[
    \sum \frac{2}{m}\ge 1.
    \]
  - Equivalently, in the original moduli, each parity class needs
    \[
    \sum \frac1m \ge \frac12.
    \]
  - So total necessary mass is \(\sum 1/m\ge 1\), not \(2\), unless you are already working with the halved moduli.

- Your proposed reciprocal sum does **not** converge to \(0.77\).
- In fact
  \[
  \frac1{p-1}=\frac1p+\frac1{p(p-1)}.
  \]
- Hence
  \[
  \sum_{p\ge 5}\frac1{p-1}
  =
  \sum_{p\ge 5}\frac1p
  +
  \sum_{p\ge 5}\frac1{p(p-1)}.
  \]
- The second series converges, but \(\sum_p 1/p\) diverges. So \(\sum_{p\ge5}1/(p-1)\) diverges.

- Direct computation already beats \(1\):
  \[
  \frac14+\frac16+\frac1{10}+\frac1{12}+\frac1{16}+\frac1{18}+\frac1{22}+\frac1{28}
  +\frac1{30}+\frac1{36}+\frac1{40}+\frac1{42}+\frac1{46}+\frac1{52}+\frac1{58}+\frac1{60}+\frac1{66}+\frac1{70}
  \approx 1.01346.
  \]
- So density alone cannot prove impossibility.

**What this means**

- The “if the total reciprocal mass is \(<1\), then impossible” criterion does not apply, because the total available mass is actually infinite.
- So Problem 273 is **not** settled by this line.
- As far as I could verify, it remains open; Erdős Problems still listed it open on **October 1, 2025**.

**Relevant techniques**

- Hough–Nielsen restricted-divisibility sieve:
  every distinct cover has a modulus divisible by \(2\) or \(3\). Relevant after parity-halving, applied to each half-cover separately.
- Balister–Bollobás–Morris–Sahasrabudhe–Tiba distortion/uncovered-density method:
  strongest current general sieve framework here. They also prove a stronger lcm condition: for a distinct cover with lcm \(Q\), one must have \(2\mid Q\) or \(9\mid Q\) or \(15\mid Q\).
- Filaseta–Ford–Konyagin–Pomerance–Yu:
  very relevant background on density of uncovered sets and reciprocal-sum bounds, but not enough by itself here because the admissible set \(\{p-1\}\) is sparse and the minimum modulus is fixed at \(4\).
- Compression / antichain / Schinzel-type divisibility arguments:
  likely useful because after parity reduction you are really asking whether the thin set \(\{(p-1)/2\}\) can be partitioned into two distinct covers.
- Square-free odd-covering results:
  only indirectly relevant, since \(p-1\) moduli are typically not square-free.

**Sources**

- Erdős Problem 273 status: https://www.erdosproblems.com/273
- Hough–Nielsen, *Covering systems with restricted divisibility* (Duke, 2019): https://www.math.stonybrook.edu/~rdhough/covering_restricted.pdf
- Balister–Bollobás–Morris–Sahasrabudhe–Tiba, *On the Erdős covering problem: the density of the uncovered set* (Invent., 2022): https://par.nsf.gov/servlets/purl/10339936
- Balister–Bollobás–Morris–Sahasrabudhe–Tiba, *The Erdős–Selfridge problem with square-free moduli* (ANT, 2021): https://doi.org/10.2140/ant.2021.15.609
- Filaseta–Ford–Konyagin–Pomerance–Yu, *Sieving by large integers and covering systems of congruences* (JAMS, 2007): https://www.ford126.web.illinois.edu/wwwpapers/coverings.pdf

**Next steps**

1. Reformulate the problem as: can \(\{(p-1)/2\}\) be partitioned into two disjoint sets, each supporting a distinct cover of \(\mathbb Z\)?
2. Apply Hough–Nielsen / BBMST necessary lcm-divisibility conditions to each parity half, especially the half that does not get modulus \(2\) (coming from original modulus \(4\)).
3. Look for a stronger obstruction than density: local lcm constraints, compression on divisibility posets, or incompatibility of small moduli assignments across the two parity halves.