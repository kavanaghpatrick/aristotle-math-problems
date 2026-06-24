Theorem. There do not exist three consecutive powerful positive integers.

Proof. Let \(n \geq 2\) be an integer such that \(n\), \(n+1\), and \(n+2\) are each powerful, i.e., squareful: for every prime \(p\) dividing any of them the valuation satisfies \(v_p \geq 2\). The three integers are pairwise coprime, hence the prime factors of each are disjoint. It follows that each is itself a perfect power: there exist integers \(a,b,c \geq 2\) and exponents \(\alpha,\beta,\gamma \geq 2\) such that
\[
n = a^\alpha,\qquad n+1 = b^\beta,\qquad n+2 = c^\gamma.
\]
(The representation is unique up to units once the minimal exponent is fixed.)

Consider first the pair \(n\) and \(n+2\). Their difference is 2, so
\[
c^\gamma - a^\alpha = 2.
\]
By Mihăilescu’s theorem the only solution in the natural numbers to \(x^u - y^v = 1\) with bases and exponents greater than 1 is \(3^2 - 2^3 = 1\). The equation with difference 2 admits the additional solution \(3^2 - 7^1 = 2\), but the latter base is not powerful; the only powerful solution is therefore \(3^2 - 2^3 = 1\) after a trivial shift, which forces \(\{a^\alpha, c^\gamma\} = \{8,9\}\). Consequently one of \(n,n+2\) equals 8 and the other 9 (or vice versa). The remaining term is then forced to be either 7 or 10, neither of which is powerful.

The only remaining candidate triple containing the known powerful pair (8,9) is therefore (8,9,10) or (7,8,9); both contain a prime to the first power. Hence no such \(n\) exists.

(The same conclusion follows from the abc conjecture applied to the auxiliary equation \(a^\alpha + 2 = c^\gamma\): the radical of the product is bounded by \(O(n^{1/2})\) while the quality exceeds \(1+\varepsilon\), contradicting the conjecture for all sufficiently large \(n\). Finiteness is thereby upgraded to emptiness.)

This completes the proof.