# Summary of changes
## Singmaster's Conjecture — Open Problem

**Status: The main conjecture remains `sorry`'d because it is a genuinely open problem in combinatorics.**

### What was done

The file `RequestProject/Singmaster.lean` contains:

1. **The main theorem statement** (`singmaster`) — left as `sorry` because Singmaster's conjecture is an open problem with no known proof. The best known upper bound on the number of times an integer appears in Pascal's triangle is O(log t / (log log t)²), which grows with t — no constant bound has been proven.

2. **Comprehensive documentation** explaining:
   - The conjecture and its history (Singmaster, 1971)
   - Known results (3003 appears 8 times; infinitely many numbers appear 6 times)
   - The best known upper bound (Kane, 2007)
   - A detailed explanation of *why* a constant bound cannot currently be formalized — the O(log t) barrier from elementary methods

3. **Three proven partial results** that capture the provable components of the analysis:
   - `choose_strictMono_left`: For fixed k ≥ 1, n ↦ C(n+k, k) is strictly increasing (so at most one n per k)
   - `choose_ge_of_interior`: C(n,k) ≥ n for all interior entries (1 ≤ k ≤ n-1, n ≥ 2)
   - `choose_eq_bound`: All solutions to C(n,k) = t > 1 satisfy n ≤ t and k ≤ t (justifying the finite search space)

### Why the conjecture cannot be resolved

The core difficulty: for each k from 1 to ~log₂(t), there is at most one n with C(n,k) = t. This gives an O(log t) bound on representations. Proving this count is bounded by a *universal constant* requires showing that for large t, only O(1) of the ~log₂(t) candidate k values simultaneously yield solutions — precisely what no one has been able to prove.