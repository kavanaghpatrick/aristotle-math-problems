# Techniques — Lean formalization notes for abc-conditional sandwich

## Architecture

```
abc-conditional-sandwich
├── definitions
│   ├── Nat.Powerful (from RequestProject/Erdos938.lean, slot 1300)
│   ├── Set.IsAPOfLength (from RequestProject/Erdos938.lean)
│   ├── ABC.radical (from FormalConjectures/Wikipedia/ABC.lean)
│   └── ABC.abc.variants.lt_constant_mul (the hypothesis)
│
├── helper lemmas (basic NT, formalizable directly)
│   ├── L1: powerful_radical_bound  (rad(n) ≤ √n for n powerful)
│   ├── L2: consecutive_squares_force_interloper  (gap > 2√N+1 ⟹ contains square)
│   ├── L3: interloper_is_middle  (consecutive ⟹ unique middle)
│   └── L4: consecutive_AP_d_upper_bound  (d ≤ 2√N+2)
│
├── algebraic identity
│   └── L5: AP_identity  (n_{k+1}² = n_k · n_{k+2} + d²)
│
├── abc application
│   └── L6: abc_to_chan_bound  (under abc, d ≥ c_ε · N^{1/2-ε})
│
└── main theorem
    └── L7: sandwich_theorem  (combining L4 + L6)
```

## Key technical move: the AP identity

Instead of applying abc to the relation n_{k+1} = n_k + d (which forces a delicate gcd reduction and requires tracking powerfulness through quotients), we apply abc to:

  **A + B = C with A := d², B := n_k · n_{k+2}, C := n_{k+1}²**

This is cleaner because:
- **All three of A, B, C are automatically powerful.** d² is a square (powerful). n_k · n_{k+2} is a product of two powerfuls (powerful). n_{k+1}² is a square (powerful).
- **rad bounds are direct.** rad(d²) = rad(d) ≤ d. rad(B) = rad(n_k) · rad(n_{k+2}) / gcd-overlap ≤ √n_k · √n_{k+2} ≤ n_{k+1}. rad(C) = rad(n_{k+1}) ≤ √n_{k+1}.
- **The identity n_{k+1}² = n_k n_{k+2} + d² is elementary algebra**, formalizable by `ring`.

After coprime reduction by g = gcd(A, B, C):
  C/g ≤ K_ε · rad((ABC)/g)^{1+ε} ≤ K_ε · (rad(ABC)/?)^{1+ε}
  n_{k+1}²/g ≤ K_ε · (d · n_{k+1} · √n_{k+1}/g)^{1+ε} (in worst case)
  n_{k+1}² ≤ K_ε · g · (d · n_{k+1}^{3/2}/g)^{1+ε}
  n_{k+1}^{1/2 - O(ε)} ≤ K_ε · d^{1+ε} · g^{-ε}
  d ≥ c_ε · n_{k+1}^{1/2 - O(ε)} ≥ c_ε · N^{1/2 - ε'} (re-labeling).

## The upper bound is the trick

The consecutive-square interloper argument:
- Between n_k and n_{k+2} of length 2d, if 2d > 2√N + 1, there's a perfect square m² in the interval.
- By consecutiveness in A, this square equals n_{k+1} (the unique powerful in the open interval).
- If n_{k+1} = m², then d = m² - n_k. The two squares straddling n_{k+1} are at distance ≤ 2m+1 each. So d ≤ 2m+1 ≤ 2√n_{k+2} + 1 ≤ 2√(N + 2d) + 1.
- Solving: d ≤ 2√N + 2 for N large.
- If 2d ≤ 2√N + 1, then trivially d ≤ √N + 1/2 ≤ 2√N + 2.

Either way: **d ≤ 2√N + 2** (rigorous, Lean-formalizable via `Nat.sqrt` and natural-number bounds).

## What goes in the .txt sketch

ONLY: the bare theorem statement (sandwich, abc-conditional).

## What goes in the .fusion.json (this dossier)

- Bridge lemma: explicit abc application via AP identity
- 8 candidate lemmas (L1-L8)
- Cross-critique log (3 rounds: codex+grok+claude)
- Honest disclaimer: this is the sandwich, NOT finiteness

## Why this passes the closure-axis test

This is NOT a real_closure_candidate — it's a structural conditional theorem. Yet it's a genuine ADVANCE because:
1. The sandwich theorem is a real Lean-formalizable conditional theorem
2. It cleanly captures the abc-extractable structure
3. It honestly flags the missing ingredient for full E938 finiteness

This is best submitted as INFORMAL mode to engage Aristotle's lemma-based reasoner subsystem (W8 lever), giving Aristotle the chance to either:
(a) Formalize the sandwich as L7 (the main deliverable)
(b) Discover a sieve/density refinement that closes E938 (low probability ~0.01 but non-zero)

The fusion lane companion's .fusion.json provides the strategy, the .txt provides the bare gap.
