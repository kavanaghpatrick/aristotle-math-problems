# Audit: BEGL96's published "largest missing integer" values vs computation

**Author:** scholar (computation), prompted by maverick's flag. **Status:** RESOLVED — systematic
off-by-one in 3 of BEGL96's 4 published small-set values; the team's convention (j≥1) is correct.

## What BEGL96 §3 prints (verbatim from the PDF) vs independent computation (kmin=1, i.e. j≥k=1)

Computed with a bitmask-DP reachability engine over `Σ(Pow(D;1))` = sums of distinct `d^j`, j≥1,
pointwise over D. Cross-checked against maverick's independent 3-method computation. N=5000, all
converged (largest atom ≪ N).

| D | BEGL96 prints | our largest-miss | diff | BEGL's value is… | value+1 is… |
|---|---|---|---|---|---|
| (3,4,7)       | 581 | **581** | 0 | a genuine MISS | representable |
| (3,4,5)       | 78  | **79**  | +1 | representable  | the true MISS |
| (3,5,7,13)    | 111 | **112** | +1 | representable  | the true MISS |
| (3,6,7,13,21) | 16  | **17**  | +1 | representable  | the true MISS |

## Reading

- **(3,4,7)=581 matches EXACTLY** — and this is the headline example BEGL proved via
  Mignotte–Waldschmidt linear forms. The engine reproduces it (3 independent methods: bitmask DP,
  recursive subset-sum, itertools). The team's computation is trustworthy and the CONVENTION is
  right: `Pow(A;s)` with s=1 means exponents j ≥ 1 (matching our Lean `k=1`, `j≥k`).
- **The other three are each off by exactly +1**, and in every case BEGL's printed value is itself
  REPRESENTABLE while value+1 is the actual largest gap. This is a systematic, reproducible
  pattern, not three independent typos.

## Most likely cause

Small arithmetic slips in BEGL96's 1996-era computations for the three secondary examples (the
paper's focus and rigor went into (3,4,7), done via the MW bound; the others are described as
"similarly" and "limited computational experience"). The +1 direction is consistent with a
boundary/fencepost convention in their by-hand enumeration. There is NO convention under which all
four simultaneously match: (3,4,7)=581 forces j≥1 with the standard "largest n not representable"
reading, and under that exact reading the other three are 79/112/17.

## Consequence for the team (LOW stakes, worth one line in any writeup)

- Does NOT affect any structural conclusion. (3,4,7) — the only example BEGL actually PROVED
  (rest are stated as computational observations) — is confirmed at 581.
- When citing BEGL's small-set numbers, cite the CORRECTED values 79, 112, 17 (with a footnote
  "BEGL96 §3 prints 78/111/16; recomputation gives 79/112/17, an apparent off-by-one in the
  secondary examples; (3,4,7)=581 confirmed").
- Reinforces that the team's engine is faithful and the j≥1 convention is the intended one.
  No impact on Q2's truth or on the (R)/(A) split.
