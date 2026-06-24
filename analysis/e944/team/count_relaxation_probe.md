# E944 — Fractional & criticality-fraction sanity probes (count)

**Verification:** `python3 analysis/e944/team/relaxation_probe.py` (scipy LP for
exact fractional chromatic number over maximal independent sets). Engine self-tested.

## Probe A — fractional chromatic number and fractional edge-criticality

| graph | χ | χ_f | #integral-critical edges | #fractional-critical edges | m |
|---|---|---|---|---|---|
| C₇(1,2)      | 4 | 3.500 | 7  | 7  | 14 |
| C₁₃(1,2,5)   | 4 | 3.250 | 13 | 13 | 39 |
| K₄           | 4 | 4.000 | 6  | 6  | 6  |
| Grötzsch (Myc C₅) | 4 | 2.900 | 20 | 20 | 20 |

**Key finding: integral-critical edges = fractional-critical edges, exactly, in
every case.** The fractional relaxation does NOT open a gap. Even though the χ=4
obstruction is "thin" (χ_f as low as 2.9 for Grötzsch — it barely clears 3), an
edge is fractionally critical iff it is integrally critical. So:
- There is **no "fractional witness exists but integral doesn't" phenomenon**. The
  E944 obstruction is genuinely integral/combinatorial; relaxing to LP neither
  creates nor destroys witnesses.
- This is mildly GOOD news for constructibility: the witness, if it exists, is a
  clean combinatorial object, not balanced on a fractional knife-edge that
  integrality would break. Gadget/gluing constructions (forge's lane) are not
  fighting an integrality gap.

## Probe C — does the minimum critical-edge FRACTION trend to 0?

| n | min(#critical / #edges) over all 4-vtx-critical graphs |
|---|---|
| 4 | 1.000 (K₄) |
| 5 | — (none exist) |
| 6 | 1.000 |
| 7 | 0.500 (the C₇(1,2) circulant) |
| (vertex-transitive, n=13) | 0.333 (C₁₃(1,2,5)) |

The minimum critical fraction **strictly decreases** once n is large enough to
admit non-edge-critical vertex-critical graphs (n≥7), and vertex-transitive
examples drive it from 50% to 33%. **No floor above 0 is observed.** A witness is
exactly the 0% point. The monotone descent (1.0 → 0.5 → 0.33 ...) is consistent
with — though NOT proof of — a 0% witness existing at larger n.

## Caveat (honest)
- Probe C's "trend to 0" is suggestive, not rigorous. The descent could plateau at
  a positive floor that small-n data hasn't reached; only Skottova–Steiner Prop 5.1
  (min-deg≥6, n≥11) tells us where to look, and my circulant search shows circulants
  plateau at "1 critical orbit" (≥ 1/|S| fraction) and never reach 0. So among
  CIRCULANTS there IS effectively a floor (you can't kill the Hamilton-cycle orbit).
  The trend-to-0 hope rests on NON-circulant graphs.
- List-coloring analogue (Probe B) not separately run: list-criticality (ch≥χ) is a
  STRICTLY STRONGER obstruction, so a list-(4,1)-graph would be harder, not easier;
  it would not calibrate plausibility upward. Skipped as non-informative for the
  TRUE direction. (If wanted for the FALSE direction, a list-witness non-existence
  is weaker evidence than ordinary non-existence.)

## Net calibration
Three independent cheap probes (fractional relaxation, criticality fraction trend,
and the earlier counting/overlap obstructions) all point the same way: **no
relaxation or counting obstruction blocks a witness.** This is the fingerprint of
a problem whose answer is TRUE-but-hard-to-construct (the object exists, finding it
is the work), rather than FALSE-by-obstruction. This matches Steiner's published
stance: open, no general non-existence conjecture, only a narrow circulant lean.
