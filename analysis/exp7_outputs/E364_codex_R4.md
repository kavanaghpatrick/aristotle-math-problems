No unconditional proof of Erdős 364 is currently known. The structural diagnoses are right: Catalan/Mihăilescu cannot prove the conjecture because it only classifies consecutive *perfect powers*, while powerful numbers include mixed-exponent numbers like \(72=2^3 3^2\). Current references still list the problem as open; Erdős Problems says there are no known complete or partial solutions claimed there, abc gives only finiteness, and no triple is known below \(7.38\times 10^{28}\). MathWorld likewise states this as Erdős’s conjecture. Sources: [Erdős Problems #364](https://www.erdosproblems.com/364), [MathWorld: Powerful Number](https://mathworld.wolfram.com/PowerfulNumber.html).

A correct proof would need something substantially stronger than Catalan: it must control simultaneous equations
\[
n=a^2u^3,\qquad n+1=b^2v^3,\qquad n+2=c^2w^3,
\]
with \(u,v,w\) squarefree, and rule out all squarefree obstruction patterns. The hard part is not the representation itself; it is proving that no compatible local prime-exponent pattern can survive globally.

The smallest clean unconditional sub-result is:

**Proposition.** There are no four consecutive powerful integers.

**Proof.** Among any four consecutive integers, one is congruent to \(2 \pmod 4\). Such a number is even but not divisible by \(4\), so the prime \(2\) divides it to exponent exactly \(1\). Hence it is not powerful. Therefore four consecutive powerful integers cannot exist.

A slightly stronger necessary condition for any hypothetical triple is also elementary. Since an even powerful number must be divisible by \(4\), the even member of the triple must be the middle one:
\[
(n,n+1,n+2)=(4m-1,4m,4m+1).
\]
Also, the member divisible by \(3\) must actually be divisible by \(9\), so any triple must lie in one of the residue patterns
\[
(36k-1,36k,36k+1),\quad
(36k+7,36k+8,36k+9),\quad
(36k+27,36k+28,36k+29).
\]

Catalan gives only the much narrower result that three consecutive *perfect powers* cannot occur: the only consecutive perfect powers with exponents \(>1\) are \(8,9\), and \(10\) is not a perfect power. That does not touch the general powerful case.