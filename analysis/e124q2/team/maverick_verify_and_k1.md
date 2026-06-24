# maverick: verification log + worked k=1 instance for D={3,4,5}

## (A) VERIFIED load-bearing claims (immune-system duty)

### A1. sumset's scaling lemma `S(d,k) = d^k · B_d` — CONFIRMED ✓
Independently recomputed S(d,k) by brute subset-sum and compared to `d^k · B_d`
for all d∈{3,4,5,7}, k∈{0,1,2,3}, values ≤ 5000. Exact set equality in all 16 cases.
The lemma is correct and the Lean form `x ∈ S d k ↔ d^k ∣ x ∧ x/d^k ∈ B_d` is the right
statement. **sumset's reduction stands.**

### A2. gcd(D)=1 necessity for k≥1 — CONFIRMED ✓ (re-derived)
If p | gcd(D) then p^k | every element of every d^k·B_d, hence p^k | every sumset
element; a cofinite set cannot lie inside p^k·ℕ. Clean, correct. (sumset's argument.)

### A3. "does NOT reduce to k=0 by scaling" — CONFIRMED ✓
∑ d^k·B_d is a genuinely new object because the scale factors d^k differ across d.
The k=0 theorem does not give k≥1 for free.

## (B) WORKED INSTANCE: D={3,4,5}, computed cofiniteness

Admissibility: ∑1/(d−1) = 1/2+1/3+1/4 = 13/12 ≥ 1 ✓; gcd(3,4,5)=1 ✓.

Sumset ∑_{d∈{3,4,5}} d^k·B_d computed exactly via bitset OR-convolution.

| k | largest gap n₀(k) | #gaps | N tested | cofinite? |
|---|------------------|-------|----------|-----------|
| 1 | **79**           | 11    | 5×10⁶    | YES (gaps: 1,2,6,10,11,15,22,26,63,74,79) |
| 2 | 77,613           | 1,128 | 5×10⁶    | YES |
| 3 | 4,330,731        | 45,704| 5×10⁶    | YES |
| 4 | 69,013,348       | 1.78M | 8×10⁷    | YES (last 100k all reachable) |
| 5 | > 8×10⁷          | —     | 8×10⁷    | threshold beyond tested range |

**k=1 is fully settled empirically: every n ≥ 80 is a_3 + a_4 + a_5 with a_d ∈ d·B_d.**

## (C) Key structural observation: n₀(k) grows ~geometrically

n₀(k): 79 → 77,613 → 4.33M → 69M. The threshold blows up with k (each set is
sparsified by factor d^k). Cofiniteness still holds for every finite k — this is exactly
the BEGL96 content: the threshold n₀(k) < ∞ for all k, even though n₀(k)→∞ as k→∞.

**This is why a naive "bounded N check" can NEVER prove the conjecture** — n₀(k) is
unbounded in k, so the proof must be structural/uniform in k, not a finite verification.

## (D) Open issue I'm now attacking
WHY is n₀(k) finite for every k? Need the covering mechanism that is uniform in k.
Candidate: a CRT/covering-system argument coupling the residues mod d^k across d∈D,
made possible precisely by gcd(D)=1. See maverick_mechanism.md (in progress).
