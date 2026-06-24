1. **Open status (as of March 13, 2026): still open.**  
The statement in your prompt is the **conjecture**, not a theorem. Erdős Problem #364 still lists it as open (last edited Dec 20, 2025), and both recent papers in *Integers* (Chan 2025, She 2025) explicitly treat it as open.

2. **Strongest known results.**  
- There are infinitely many **pairs** of consecutive powerful numbers (classical Pell-equation constructions; already discussed by Erdős/Mahler, Golomb, Sentance, etc.).  
- Triple problem remains open, but there are strong **restricted nonexistence** results:
  - Chan (2025): no triple of form  
    \[
    x^3-1=p^3y^2,\quad x^3,\quad x^3+1=q^3z^2
    \]
    with primes \(p,q\).  
  - She (2025): no triple of form  
    \[
    x^3-1=p^2a^3,\quad x^3,\quad x^3+1=q^2b^3
    \]
    with primes \(p,q\).  
- **ABC-conditional:** only finitely many such triples (classical consequence; cited in modern accounts and Granville’s related work).  
- **Computational checks:** no example for \(n<10^{22}\) (OEIS A060355 based check). A larger bound \(n\le 73840550964522899559001927226\) is reported in the Erdős Problem #364 discussion, tied to A076445 data; treat this as computational/report-level, not a published theorem.

3. **Can the ABC route be made unconditional for triples?**  
No known method does this.  
Inference (from abc framework + identity below): abc gives **finiteness**, not directly **emptiness**. Current unconditional tools only solve special subfamilies (like the cube-centered forms above), not the full variable-exponent squarefull condition.

4. **Exact structural constraints if \(n,n+1,n+2\) are all powerful.**  
Assume such \(n\) exists.
- \(n\) must be odd.  
  Reason: if \(n\) were even, one of \(n,n+2\) is \(2\bmod 4\), impossible for a positive even powerful number (must be divisible by \(4\)).  
- So triple is necessarily
  \[
  (4m-1,\;4m,\;4m+1).
  \]
- \(\gcd(n,n+1)=\gcd(n+1,n+2)=\gcd(n,n+2)=1\).  
- \(n\) and \(n+2\) are odd coprime powerful numbers at distance 2.
- Write \(n+i=a_i^2b_i^3\) (\(b_i\) squarefree): then \(\mathrm{rad}(n+i)\le (n+i)^{1/2}\) for each \(i\).

5. **Parity / congruence constraints.**  
- From above: \(n\equiv 3\pmod 4\).  
- Exactly one of \(n,n+1,n+2\) is divisible by 3; that one must actually be divisible by \(9\) (since it is powerful).  
- Combining with \(n\equiv 3\pmod 4\), one gets
  \[
  n\equiv 7,\ 27,\ 35 \pmod{36}.
  \]
This matches known congruence filters in the literature.

6. **Is there a plausible unconditional path, or is this ABC-hard?**  
Current evidence points to “ABC-hard-ish” for a global result.  
Key identity:
\[
(n+1)^2-n(n+2)=1.
\]
Inference: applying abc to \(n(n+2)+1=(n+1)^2\) plus squarefull bounds on radicals yields finiteness quickly under abc, but no unconditional analogue is strong enough to force nonexistence. So far, progress is via highly structured subcases (Chan/She), not a full unconditional mechanism.

**Sources**  
- Erdős Problem #364: https://www.erdosproblems.com/364  
- Discussion thread (#364, computational comment): https://www.erdosproblems.com/forum/thread/364  
- Chan (Integers 25 (2025) A7): https://math.colgate.edu/~integers/z7/z7.pdf  
- She (Integers 25 (2025) A103): https://math.colgate.edu/~integers/z103/z103.pdf  
- OEIS A060355: https://oeis.org/A060355  
- OEIS A076445: https://oeis.org/A076445  
- Mollin–Walsh bibliographic entry (On powerful numbers, 1986): https://ideas.repec.org/a/hin/jijmms/812820.html