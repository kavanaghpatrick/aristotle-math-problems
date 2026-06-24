1. **Open status (verified):**  
The problem is still open.  
- Cushing–Pascoe (2016) list it explicitly: “When is \(2^n+1\) powerful?” ([arXiv:1611.01192](https://arxiv.org/abs/1611.01192)).  
- CrowdMath (2020) says the specific case \((a,b,m)=(2,1,0)\), i.e. \(2^n+1\), is unresolved and notes only \(n=3\) is known ([arXiv:2005.07321](https://arxiv.org/abs/2005.07321)).  
- Erdős Problems site marks Problem 936 as open (last edited Oct 29, 2025): [erdosproblems.com/936](https://www.erdosproblems.com/936).

2. **Known powerful values of \(2^n+1\):**  
Only \(n=3\) is known:
\[
2^3+1=9=3^2.
\]
No published additional \(n\) is known in the sources above.  
I also ran an independent exact factorization check for \(1\le n\le 180\) (SymPy `factorint`), and only \(n=3\) appeared.

3. **Computational verification range:**  
- **Published literature:** I could not find a peer-reviewed paper giving a large exhaustive bound of the form “verified for all \(n\le N\)” for this exact powerfulness question.  
- **Related computations:** there are computations about square factors in \(2^n+1\) tied to Wieferich behavior (e.g. [OEIS A272361](https://oeis.org/A272361)), but that is weaker than full powerfulness.  
- **Independent check here:** exact exhaustive check up to \(n=180\): only \(n=3\).

4. **Why ABC implies finiteness (with quality exponent):**  
Let
\[
c_n=2^n+1,\quad a_n=2^n,\quad b_n=1,\quad a_n+b_n=c_n.
\]
If \(c_n\) is powerful, then every prime exponent in \(c_n\) is \(\ge2\), so
\[
c_n \ge \operatorname{rad}(c_n)^2.
\]
Hence
\[
\operatorname{rad}(a_nb_nc_n)=\operatorname{rad}(2^n\cdot1\cdot c_n)=2\,\operatorname{rad}(c_n)\le 2\,c_n^{1/2}.
\]
So the ABC quality is
\[
q_n:=\frac{\log c_n}{\log \operatorname{rad}(a_nb_nc_n)}
\ge
\frac{\log c_n}{\log(2c_n^{1/2})}
=
\frac{2}{1+\frac{2\log2}{\log c_n}}
\to 2.
\]
Thus for any fixed \(\varepsilon<1\), all sufficiently large such triples satisfy
\[
q_n>1+\varepsilon
\quad\Longleftrightarrow\quad
c_n>\operatorname{rad}(a_nb_nc_n)^{1+\varepsilon}.
\]
ABC says for each \(\varepsilon>0\), only finitely many coprime triples have this. Therefore only finitely many \(n\) can make \(2^n+1\) powerful.

5. **Unconditional partial results (rigorous):**  
Write \(n=2^s m\) with \(m\) odd, and \(F_s:=2^{2^s}+1\).  
For odd prime \(p\mid F_s\), LTE gives
\[
v_p(2^n+1)=v_p(F_s)+v_p(m).
\]
So if \(v_p(F_s)=1\) and \(p\nmid m\), then \(v_p(2^n+1)=1\), impossible for powerfulness.

Concrete consequences:
- \(s=0,\ p=3\): \(v_3(2^n+1)=1+v_3(n)\) for odd \(n\). So odd \(n\) with \(3\nmid n\) are ruled out.
- \(s=1,\ p=5\): if \(n\equiv2\pmod4\) and \(5\nmid(n/2)\), ruled out.
- \(s=2,\ p=17\): if \(n\equiv4\pmod8\) and \(17\nmid(n/4)\), ruled out.
- Similarly with \(p=257,65537\) (for \(s=3,4\)).  
Also \(F_5=641\cdot6700417\), \(F_6=274177\cdot67280421310721\), so those \(p\) give further unconditional exclusions.

A density consequence (from \(s=0,\dots,6\)): possible powerful \(n\) have upper density at most
\[
\sum_{s=0}^6 \frac{1}{2^{s+1}p_s}+\frac1{128}
=0.2321001798\ldots,
\]
with \(p_s=(3,5,17,257,65537,641,274177)\).  
So at least \(0.7678998202\ldots\) of integers are unconditionally ruled out.

6. **Connections:**
- **Wieferich primes:** If \(p^2\mid 2^n+1\) and \(p\nmid n\), then lifting of order is “non-generic” (\(\operatorname{ord}_{p^2}(2)=\operatorname{ord}_p(2)\)); this is a Wieferich-type phenomenon. For classical base-2 Wieferich primes, only \(1093,3511\) are known (peer-reviewed bound at least to \(6.7\times10^{15}\): Dorais–Klyve 2011, [JIS paper](https://cs.uwaterloo.ca/journals/JIS/VOL14/Dorais/dorais7.html)).
- **Fermat numbers:** \(n=2^k\) gives \(2^n+1=F_k\). Powerful \(F_k\) would require every prime factor repeated; repeated factors are tied to Wieferich-type lifting.
- **Catalan/Mihăilescu:** If \(2^n+1\) is a perfect power \(y^m\) (\(m>1\)), then \(y^m-2^n=1\), and Mihăilescu implies only \(3^2-2^3=1\). So the only perfect-power case is \(n=3\) ([DOI](https://doi.org/10.1515/crll.2004.048)).

7. **Why \(2^n+1\) strongly resists being powerful (structure):**  
- Cyclotomic decomposition gives many independent prime sources.  
- Each source typically contributes primes with exponent \(1\) unless a specific lifting condition holds (Wieferich-type).  
- For \(n=2^s m\), even the fixed Fermat factor \(F_s\) forces divisibility constraints on \(m\).  
- Primitive divisor theory for Lucas/Lehmer sequences supports continual appearance of new primes (Bilu–Hanrot–Voutier, [DOI](https://doi.org/10.1515/crll.2001.078)).  

So the obstruction is structural: powerfulness requires many simultaneous rare liftings.

**Sources used:**  
- https://www.erdosproblems.com/936  
- https://arxiv.org/abs/1611.01192  
- https://arxiv.org/abs/2005.07321  
- https://cs.uwaterloo.ca/journals/JIS/VOL14/Dorais/dorais7.html  
- https://oeis.org/A272361  
- https://doi.org/10.1515/crll.2004.048  
- https://doi.org/10.1515/crll.2001.078

I could not locate a peer-reviewed exhaustive “checked up to \(N\)” bound for this exact problem beyond small direct computations and related (but weaker) Wieferich/squarefactor computations.