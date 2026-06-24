# Summary of changes for run 9cf2032b-2f8a-4c33-912c-fc15cbcc79ec
## Erdős Problem 938 — Formalization Report

**Problem:** Are there only finitely many 3-term arithmetic progressions formed by three consecutive powerful numbers?

**Status: OPEN.** This is a genuinely open problem in number theory. No unconditional finiteness proof is known. Chan (2022, arXiv:2210.00281) proves finiteness only under the ABC conjecture.

### What was accomplished

The file `RequestProject/Main.lean` contains:

1. **Definitions:**
   - `Nat.Powerful`: A natural number n ≥ 1 where every prime divisor p satisfies p² ∣ n
   - `Set.IsAPOfLength`: A set forms an arithmetic progression of given length

2. **Proved auxiliary lemmas (all sorry-free, verified axioms):**
   - `Nat.Powerful.one`: 1 is powerful
   - `Nat.Powerful.sq`: Every perfect square ≥ 1 is powerful
   - `Nat.Powerful.mul`: The product of two powerful numbers is powerful
   - `Nat.Powerful.infinite`: There are infinitely many powerful numbers
   - `powerful_1728`, `powerful_1764`, `powerful_1800`: Verified that these specific numbers are powerful
   - `three_ap_example`: The triple (1728, 1764, 1800) is a verified 3-AP of powerful numbers with common difference 36, demonstrating such progressions exist

3. **Main conjecture (left as `sorry`):**
   ```lean
   theorem erdos_938 :
       {P : Finset ℕ | Set.IsAPOfLength (P : Set ℕ) 3 ∧ ∃ k,
         P = {Nat.nth Nat.Powerful k, Nat.nth Nat.Powerful (k+1),
              Nat.nth Nat.Powerful (k+2)}}.Finite := by sorry
   ```

### Analysis of proof approaches (documented in module docstring)

1. **CM elliptic curve approach (FALSIFIED):** The curve E_d : y² = x(x+d)(x+2d) has j-invariant 1728 and CM by ℤ[i]. However, the product n(n+d)(n+2d) of three powerful numbers in AP need not be a perfect square. The formalized counterexample (1728, 1764, 1800) has product with odd exponents on 2 and 3, killing this approach.

2. **Pell-system approach (INCOMPLETE):** Using Golomb's parametrization n = a²b³, the AP condition becomes a Diophantine system. Heath-Brown (1988) gives infinitely many consecutive powerful pairs via Pell equations, but extending to triples requires new uniform bounds not in the literature.

3. **ABC conditional (Chan 2022):** Under ABC, d ≫ n^{1/2−ε} for any 3-AP of powerful numbers, forcing finiteness when combined with consecutive gap bounds. This is the strongest known result but is conditional.

The main theorem remains open and is left with `sorry`.