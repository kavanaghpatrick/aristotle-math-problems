# Rigorous abc-conditional finiteness for Erdős 938
## Claude's analysis (mathematical core)

### Setup
Let A = {n_1 < n_2 < ...} be the powerful numbers. We want to show, conditional on abc:
**Theorem (abc-conditional).** The set of indices k such that (n_k, n_{k+1}, n_{k+2}) is an arithmetic progression is finite.

### Key inputs
1. **Powerful structure:** n powerful ⟺ n = a²b³, a ≥ 1, b ≥ 1 squarefree. Hence rad(n) | ab, so rad(n) ≤ ab ≤ √(a²b²) · √(b/b²·b²) — wait, more carefully: n = a²b³ gives rad(n) | rad(ab), and ab ≤ √(a²b³) · √(b) → not tight. Let me redo.
   
   n = a²b³, b squarefree. rad(n) = rad(a²b³) = rad(ab) = rad(a)·rad(b)/gcd-overlap = rad(a) · b if gcd(a,b)... actually rad(ab) divides ab. So rad(n) ≤ ab. Now ab = √(a²b²) ≤ √(a²b³) = √n iff b ≥ 1. So **rad(n) ≤ √n** when n is powerful. ✓

2. **Consecutive squares are powerful**: m² powerful. Gap between consecutive squares m², (m+1)² is 2m+1. So for any interval [N, N+L] with L ≥ 2√N + 1, there's a square inside.

3. **Consecutiveness in A:** If (n_k, n_{k+1}, n_{k+2}) ∈ A and form an AP with difference d, then no other powerful integer lies in (n_k, n_{k+2}). In particular, no square does, **except possibly n_{k+1} itself**. Hence either:
   (i) n_{k+1} is a square sitting between n_k and n_{k+2}, or
   (ii) no square is in (n_k, n_{k+2}), giving 2d = n_{k+2} - n_k ≤ 2√(n_k) + 1 - 1 (the spacing of squares around n_k), so d ≤ √(n_k) + O(1).

### Application of abc
Consider the additive relation n_{k+1} = n_k + d. Let g = gcd(n_k, d). Then n_{k+1} = n_k + d ≡ 0 (mod g) iff g | n_{k+1} too. Since g | n_k and g | d, g | n_{k+1}. So set a = n_k/g, b = d/g, c = n_{k+1}/g. We have a + b = c with gcd(a, b) = 1, hence pairwise coprime (gcd(a,c) | gcd(a, a+b) = gcd(a,b) = 1).

**abc-conjecture (strong form):** For every ε > 0, there's K_ε with c < K_ε · rad(abc)^{1+ε}.

Now rad(abc) = rad(a)·rad(b)·rad(c) (pairwise coprime ⟹ rad is multiplicative). And:
- rad(a) = rad(n_k/g). **Crucial:** rad(n_k/g) | rad(n_k), and rad(n_k) ≤ √n_k.
- rad(c) = rad(n_{k+1}/g) ≤ rad(n_{k+1}) ≤ √n_{k+1}.
- rad(b) = rad(d/g) ≤ d/g.

So:
  rad(abc) ≤ √n_k · √n_{k+1} · (d/g) · (correction).
Wait — also rad(a) = rad(n_k)/rad(g)? No, rad(n_k/g) divides rad(n_k), not equal. So rad(a) ≤ rad(n_k) ≤ √n_k. Good.

Hence rad(abc) ≤ √(n_k · n_{k+1}) · (d/g) = (n_k/g) · (something)... let me be precise.

n_{k+1} = n_k + d ≤ n_k + 2√n_k (from consecutive constraint, d ≤ 2√n_k + 1). So √n_{k+1} ≤ √(n_k + 2√n_k + 1) ≤ √n_k + 1 ≤ 2√n_k.

Thus rad(abc) ≤ √n_k · 2√n_k · d/g = 2 n_k d / g.

Now abc says c < K_ε · (rad abc)^{1+ε}, i.e., n_{k+1}/g < K_ε · (2 n_k d / g)^{1+ε}.

Multiply both sides by g:
  n_{k+1} < K_ε · g · (2 n_k d / g)^{1+ε} = K_ε · 2^{1+ε} · n_k^{1+ε} · d^{1+ε} · g^{-ε}.

Since n_{k+1} ≥ n_k:
  n_k < K_ε · 2^{1+ε} · n_k^{1+ε} · d^{1+ε} · g^{-ε}.
  1 < K_ε · 2^{1+ε} · n_k^{ε} · d^{1+ε} · g^{-ε}.
  g^ε < K_ε · 2^{1+ε} · n_k^ε · d^{1+ε}.

This gives a LOWER bound on g/something — not directly a contradiction! In fact for ε small, the right side is bounded by const · n_k^ε · (2√n_k)^{1+ε} = const · n_k^{ε + (1+ε)/2} = const · n_k^{1/2 + 3ε/2}.

So we get g < (const · n_k^{1/2 + 3ε/2})^{1/ε}, which is a weak ε-dependent bound only when g is large.

### The crux: this gives a relation, not finiteness yet.

The actual play is to use BOTH n_k AND n_{k+2} = n_k + 2d powerful. Apply abc separately to n_k + 2d = n_{k+2}.

Better approach (Chan 2022 actual proof skeleton): use the THREE relations:
  n_{k+1} - n_k = d
  n_{k+2} - n_{k+1} = d
  n_{k+2} - n_k = 2d
and the fact that all three n_i are powerful.

Chan's setup: write n_i = a_i² b_i³. Use abc on the triple (n_k, 2d, n_{k+2}): n_k + 2d = n_{k+2}. After reduction by gcd, we get a coprime triple. Chan shows rad(a_k b_k a_{k+2} b_{k+2} (2d)/D) bounds things. The key insight is that rad(n_i) ≤ a_i b_i and the abc upper bound forces rad(abc) large, hence either a_i b_i large or d large. Since powerful structure forces a_i b_i ≤ √n_i, we get d ≫ N^{1/2-ε}.

### Where the argument actually closes (this is the deep step):
The 3-AP relation gives an algebraic identity:
  n_{k+1}² - n_k · n_{k+2} = d².
(Since n_{k+2} - 2n_{k+1} + n_k = 0, we have n_{k+1}² - n_k n_{k+2} = (n_k + d)² - n_k(n_k + 2d) = d².)

So **d² = n_{k+1}² - n_k n_{k+2}**.

Now n_k, n_{k+1}, n_{k+2} are all powerful. Their pairwise products... The identity d² = n_{k+1}² - n_k n_{k+2} can be rewritten as 
  n_{k+1}² = n_k n_{k+2} + d².
Apply abc to the triple (n_k n_{k+2}, d², n_{k+1}²) — these satisfy A + B = C with all three "nearly powerful" (n_{k+1}² is automatically powerful; n_k n_{k+2} is a product of two powerful numbers = powerful; d² is a square = powerful).

After reduction by gcd, we have three powerful coprime integers with A + B = C. By abc:
  C ≤ K_ε · rad(ABC)^{1+ε} ≤ K_ε · √A · √B · √C^{1+ε} · ... ≤ K_ε · (ABC)^{(1+ε)/2}.

But A + B = C and A, B, C ≍ N² (since n_{k+1}² ≍ N²). So:
  N² ≍ C ≤ K_ε · (N² · N² · N²)^{(1+ε)/2} = K_ε · N^{3(1+ε)}.
This is a trivial bound (N² < N³ obviously). Not useful directly.

The reduction by gcd is where the action is. Let g = gcd(n_k n_{k+2}, d², n_{k+1}²). Then the reduced triple has size ~ N²/g. The rad of each is ≤ √(its value) (using powerful). So:
  N²/g ≤ K_ε · (√(N²/g))^3 · const = K_ε · N^3 / g^{3/2}.
  N²/g ≤ K_ε · N^3 / g^{3/2}.
  g^{1/2} ≤ K_ε · N.
  g ≤ K_ε · N².
Not a useful bound (g ≤ N² is trivially true). The issue: we lose too much in the rad bound.

**The actual obstruction (this is what Chan 2022 dances around):** the bound rad(n) ≤ √n is far from tight; for typical powerful n, rad(n) ≈ n^{1/2-o(1)}. Hence what's needed is rad(n) ≤ √n / X(n) for some growing function — which is FALSE in general (powerful numbers can have a = b = 1, then n = 1; or a large, b = 1, then n = a², rad = a = √n).

### Chan's actual finishing move
Chan 2022 Thm 2 says: **assuming abc, d ≫_ε N^{1/2-ε} for any powerful 3-AP**, not just consecutive ones. To close E938 (consecutive case), one ALSO needs d ≤ 2√N + O(1) (from consecutiveness). Combined: N^{1/2-ε} ≤ d ≤ 2√N + 1. These ARE compatible — they only force d = N^{1/2-o(1)}, not a contradiction.

**So the abc-conditional approach via Chan alone does NOT close E938.** The gap is precisely: Chan's bound is one-sided (lower), and the consecutive constraint is also one-sided (upper). They're compatible.

### What would close it
Need an additional constraint that, combined with Chan's lower bound and the consecutive upper bound, gives a contradiction. Candidates:
- A density argument showing the count of d in [N^{1/2-ε}, 2√N] satisfying the AP condition is o(1).
- A 2nd-moment abc-conditional bound: the SUM of d over solutions is bounded.
- Combine with Erdős-Mollin-Walsh (no 3 consecutive integers powerful) which IS abc-conditional itself.

### Strongest honest abc-conditional statement we can submit
"Under abc, the common difference d of any consecutive powerful 3-AP (n_k, n_{k+1}, n_{k+2}) is bounded: N^{1/2-ε} ≤ d ≤ 2√N + 1. The set of solutions with d outside [N^{1/2-ε}, 2√N + 1] is finite."

This is a real, formalizable conditional theorem, even if it doesn't immediately give E938's full finiteness. It captures Chan + the consecutive constraint cleanly.

### The proper conditional theorem to formalize
**Theorem (abc-conditional intermediate).** Assuming the abc conjecture, for any ε > 0 there exists K_ε such that for every consecutive powerful 3-AP (n_k, n_{k+1}, n_{k+2}) with N := n_k ≥ K_ε:
  N^{1/2-ε} < d < 2√N + 2,
where d = n_{k+1} - n_k.

**Proof (assuming abc):**
- Lower bound: Chan 2022 Thm 2.
- Upper bound: consecutive squares argument (Mathlib-formalizable).
- For N < K_ε, finitely many cases.

This is the rigorous deliverable.
