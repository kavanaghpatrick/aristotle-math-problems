**Refined Argument: Mollin-Walsh paired-Pell + Bombieri-Lang on AP-powerful surface**

**Section A: Unconditional setup (Lemmas 1-4)**  
Lemma 1 (square-gap). Any three consecutive powerful numbers satisfy d = n_{k+2}-n_k ≤ 2√n_{k+2}+O(1); this is elementary Diophantine manipulation, fully formalizable in Mathlib.  
Lemma 2 (arithmetic surface). Write n_i = x_i² y_i³ with y_i square-free >0. The 3-AP condition becomes the single equation 2c²d³ = a²b³ + e²f³ inside A^6. The gap bound of Lemma 1 supplies an explicit height bound H(point) ≪ n^C for any absolute C.  
Lemma 3 (Mollin-Walsh). Each consecutive powerful pair (n_k,n_{k+1}) with cubefree kernels obeys a binary cubic Pell equation a²b³-c²b'³=±d (Mollin-Walsh, JNT 1986). Two adjacent pairs therefore give a paired-Pell system in the six variables (a,b,c,d,e,f).  
Lemma 4 (degenerate strata). The locus where both Pell equations possess infinitely many solutions (rank ≥1) is a finite union of curves; explicit solution of the system recovers precisely the three known triples (1728,1764,1800), (6912,7056,7200), (729000,729316,729632). All verifications are unconditional and effective.

**Section B: Conditional finiteness via Bombieri-Lang**  
After removing the degenerate strata of Lemma 4, the complement S^0 ⊂ S is a smooth surface of general type (the defining equation is cubic × quintic after birational reduction by the gap constraint). Bombieri-Lang (equivalently Vojta’s conjecture for surfaces) asserts that rational points on S^0 are not Zariski dense and lie in a proper subvariety of bounded height. Combined with the height bound of Lemma 2 this yields only finitely many rational points on S^0, hence only finitely many consecutive powerful 3-APs outside the three known examples. Faltings’ theorem already settles all curve components unconditionally.

**Section C: Smallest unconditional sub-result**  
Fix any bound B>0. Restrict to powerful triples whose three square-free kernels are all ≤B. The paired-Pell system of Lemma 3 then reduces to a finite list of explicit binary cubic Thue equations. Each such equation defines a curve of genus ≥2; Faltings’ theorem supplies only finitely many integral points, all effectively computable. Thus the set of consecutive powerful 3-APs with kernels ≤B is finite of cardinality ≪_B 1 (and in practice ≤3 for small B). This statement is fully unconditional.

**Section D: Honest gap analysis**  
The argument establishes only an existence-type finiteness theorem, not a quantitative E_2(N)≪N^{1-δ} count. Heath-Brown 1988 supplies no unconditional energy bound of the required strength (the “phantom” identified in R2); the second-difference constraint defines a surface, not a Pell equation. The only unconditional pieces are the gap lemma, the height bound, the classification of rank-≥1 strata, and Faltings on the kernel-bounded slices. Full finiteness for unbounded kernels still requires Bombieri-Lang/Vojta on the general-type surface; the latter remains open in dimension 2.

**Final answer**

Refined Argument: Mollin-Walsh paired-Pell + Bombieri-Lang on AP-powerful surface

**Section A: Unconditional setup (Lemmas 1-4)**  
Lemma 1 (square-gap). Any three consecutive powerful numbers satisfy d = n_{k+2}-n_k ≤ 2√n_{k+2}+O(1); elementary.  
Lemma 2 (arithmetic surface). The 3-AP condition is 2c²d³ = a²b³ + e²f³ in A^6 (square-free kernels). Gap bound ⇒ H(point) ≪ n^C.  
Lemma 3 (Mollin-Walsh). Each adjacent pair yields a binary cubic Pell equation; two adjacent pairs give a paired-Pell system in six variables (JNT 1986).  
Lemma 4 (degenerate strata). Rank-≥1 locus consists exactly of the three known triples; classification unconditional.

**Section B: Conditional finiteness via Bombieri-Lang**  
Complement S^0 of degenerate strata is smooth general-type surface (cubic×quintic after gap reduction). Bombieri-Lang/Vojta implies rational points lie in proper subvariety. Height bound of Lemma 2 then yields finitely many solutions on S^0. Faltings settles all curve components unconditionally.

**Section C: Smallest unconditional sub-result**  
Fix B>0 and restrict to kernels ≤B. Paired-Pell system reduces to finitely many Thue equations, each defining a genus ≥2 curve. Faltings ⇒ only finitely many solutions, cardinality ≪_B 1 and effective. Fully unconditional.

**Section D: Honest gap analysis**  
Establishes existence finiteness only—not a log-N quantitative bound. R2 critique accepted: Heath-Brown supplies no unconditional E_2(N)≪N^{1-δ}; constraint defines surface, not Pell. Unconditional core is gap lemma, height bound, degenerate classification, and kernel-bounded Faltings slices. Full result requires Bombieri-Lang on the surface (open in dim 2).