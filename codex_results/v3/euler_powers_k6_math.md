As of **March 13, 2026**, the rigorous status is:

1. **Is \(k\ge 6\) open?**  
Yes. Euler’s one-sided claim is disproved for \(k=4,5\), but for \(k\ge 6\) no counterexample is known.  
- \(k=5\) counterexample: Lander–Parkin (1966).  
- \(k=4\) counterexample family: Elkies (1988), with infinitely many solutions.

2. **Best computational search range for \(k=6,7,8\)**  
For
\[
a_1^k+\cdots+a_{k-1}^k=b^k:
\]
- **\(k=6\)**: best explicit published lower bound I can verify is **no solution with \(b\le 730000\)** (reported from Resta–Meyrignac, p. 1054).  
- **\(k=7\)**: no solution known to \(7.1.6\); first known one-sided solution is at \(7.1.7\): \(568^7=\sum_{i=1}^7 a_i^7\).  
- **\(k=8\)**: no solution known to \(8.1.7\); first known one-sided solution is at \(8.1.8\): \(1409^8=\sum_{i=1}^8 a_i^8\).  

So \(k=6,7,8\) Euler cases are still unresolved.

3. **Theoretical reasons to believe it for \(k\ge 6\)?**  
No theorem currently forces it. Evidence is mostly:
- heavy computational non-discovery;
- sparsity heuristics in the critical variable range;
- strong congruence constraints (especially for \(k=6\), see item 6).  
But none is a proof.

4. **Connection to Waring / Vinogradov / circle method**  
- Waring studies representations \(n=x_1^k+\cdots+x_s^k\) for large \(n\), with \(s\) usually much larger than \(k-1\).  
- Hardy–Littlewood circle method gives asymptotics for sufficiently large \(s\).  
- Vinogradov mean value estimates (efficient congruencing/decoupling: Wooley; Bourgain–Demeter–Guth) dramatically improve those thresholds.  
- But Euler’s case uses \(s=k-1\), a very sparse regime; current circle-method technology does **not** resolve this one-sided equation.

5. **Lander–Parkin–Selfridge (LPS) conjecture(s)**  
LPS (1967): for nontrivial
\[
\sum_{i=1}^n a_i^k=\sum_{j=1}^m b_j^k,
\]
one should have \(m+n\ge k\).  
Special case \(m=1\): \(a_1^k+\cdots+a_n^k=b^k\Rightarrow n\ge k-1\).  
So LPS is weaker than Euler’s original \(n\ge k\), and is still open.

6. **Why \(k=6\) may be especially hard (near-miss structure)**  
- No known \(6.1.6\) (sum of six sixth powers equals a sixth power).  
- First known one-sided case is \(6.1.7\):  
  \[
  1141^6=74^6+234^6+402^6+474^6+702^6+894^6+1077^6.
  \]
- Congruence rigidity for a hypothetical \(6.1.5\):  
  - mod \(7\): sixth powers are \(0,1\), so among five summands at least four must be divisible by \(7\) in any primitive solution;  
  - mod \(9\): similarly, at least four must be divisible by \(3\).  
This makes primitive candidates highly constrained and sparse.

## Sources
- Lander–Parkin counterexample (1966): https://www.ams.org/bull/1966-72-06/S0002-9904-1966-11654-3/  
- Lander–Parkin–Selfridge survey/conjecture (1967): https://www.ams.org/journals/mcom/1967-21-099/home.html  
- Elkies \(A^4+B^4+C^4=D^4\) (1988): https://www.ams.org/mcom/1988-51-184/S0025-5718-1988-0930224-9/  
- Resta–Meyrignac (2003): https://doi.org/10.1090/S0025-5718-02-01445-X  
- MathWorld status pages:  
  - 6th powers: https://mathworld.wolfram.com/DiophantineEquation6thPowers.html  
  - 7th powers: https://mathworld.wolfram.com/DiophantineEquation7thPowers.html  
  - 8th powers: https://mathworld.wolfram.com/DiophantineEquation8thPowers.html  
- OEIS note with \(b>730000\) citation trail: https://oeis.org/A007666  
- Rizos page pointing to EulerNet as definitive live status repository: https://www.cs.man.ac.uk/~rizos/EqualSums/  
- Circle method / Waring / VMVT context:  
  - Boklan (Hardy–Littlewood threshold discussion): https://www.cambridge.org/core/services/aop-cambridge-core/content/view/891A4A232E4CC1BABD78EB6850BF3BD2/S0025579300007439a.pdf/div-class-title-the-asymptotic-formula-in-waring-s-problem-div.pdf  
  - Wooley (2012): https://doi.org/10.4007/annals.2012.175.3.12  
  - Bourgain–Demeter–Guth (2016): https://doi.org/10.4007/annals.2016.184.2.7  
  - Vaughan–Wooley, sixth powers (1994): https://doi.org/10.1215/S0012-7094-94-07626-6  

I could not retrieve a current machine-readable EulerNet records table in this session, so I cannot certify a newer explicit numeric cutoff than the published \(k=6\) bound above for the \(k=7,8\) Euler one-sided cases.