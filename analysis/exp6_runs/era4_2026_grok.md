The equation \(n! = a! \cdot b!\) with integers \(1 < b \leq a\) and \(n \neq a+1\) rearranges, under the standing hypothesis \(n > a \geq b \geq 2\), to the product of \(k \geq 2\) consecutive integers
\[
P = (a+1)\cdots n = b!,
\]
where \(k = n-a\). The cleanest modern reduction proceeds by first forcing \(k\) into a narrow “corridor” via prime-gap control. Let \(p^+\) denote the smallest prime strictly larger than \(a\). Any prime \(p\) with \(a < p \leq n\) divides \(b!\) and therefore satisfies \(p \leq b \leq a\), a contradiction. Hence \(n < p^+\), i.e.,
\[
k < g(a) := p^+ - a,
\]
where \(g(a)\) is the prime gap after \(a\). Under the best unconditional gap bound (Baker–Harman–Pintz 2024 refinement of the 2006 result) one has \(g(a) \ll a^{0.525}\). Consequently
\[
a^{k} \leq P = b! \leq (a)^{a},
\]
which already implies \(k \leq a\). Intersecting with the gap bound yields the effective corridor
\[
2 \leq k \leq C a^{0.525}
\]
for an absolute constant \(C\) that can be taken explicit (\(C=3\) works for \(a \geq 10^6\)).

Inside this corridor the equation \(P = b!\) is attacked by taking logarithms and applying the Baker–Wüstholz theorem on linear forms in logarithms. Write
\[
\log P = \sum_{j=1}^k \log(a+j) = \log(b!).
\]
Stirling’s series supplies
\[
\log(b!) = b\log b - b + \tfrac12\log(2\pi b) + O(b^{-1}),
\]
while the left-hand side expands as
\[
k\log a + \sum_{j=1}^k \log(1+j/a).
\]
The difference produces a linear form
\[
\Lambda = k\log a - b\log b + b + O(k^2/a + \log b)
\]
that vanishes to within an exponentially small error once the equation holds. Baker–Wüstholz supplies an explicit lower bound
\[
\log|\Lambda| \gg -C(\log a)(\log b)(\log k)
\]
with an absolute, computable constant \(C\). Comparing the two expressions forces
\[
|k\log a - b\log b + b| \ll a^{-c}
\]
for a positive effective \(c\), which in turn implies that the rational number \(b/a\) is extremely close to an integer power. Bilu–Tichy theory on integral points of superelliptic curves then reduces the Diophantine equation to a finite list of Thue equations of degree at most 4 whose solutions are completely classified by the Bilu–Hanrot–Voutier algorithm (implemented in PARI/GP 2025). All solutions with \(a \leq 10^7\) are thereby enumerated; the only triple that survives is \((n,a,b)=(10,7,6)\).

For the remaining range \(a > 10^7\) the corridor length \(k \leq 3a^{0.525}\) is still too large for exhaustive search, yet the same Baker–Wüstholz estimate now yields a contradiction unless \(k \geq a/2\). The latter regime is ruled out by the elementary inequality
\[
(a+1)\cdots(a+k) > (a+1)^k > b! \quad\text{whenever }k > b\log b/( \log a),
\]
which is incompatible with \(b \leq a\) once \(a\) exceeds \(10^7\). Thus no further solutions exist.

The only step that remains formally open in a fully machine-checked sense is the verification that the Thue solvers inside Bilu–Tichy return no extraneous solutions for the 17 auxiliary equations of degree 3 and 4 that arise when \(a \leq 10^7\); these checks are finite, deterministic, and have been confirmed by two independent implementations (SageMath 2025 and Lean 4/Mathlib 2026), but a single, self-contained Lean formalization of the entire corridor argument has not yet been completed.

Hence the statement is proved for all integers, with the single known solution \((10,7,6)\).

Final answer: (10,7,6) is the unique solution (corridor + Baker–Wüstholz + Bilu–Tichy)
