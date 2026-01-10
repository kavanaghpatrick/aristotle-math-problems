# PATH_4 slot263 - Partial Proof Summary

## ACTUALLY PROVEN (no sorry):

### path4_cover_card_le_8_of_packing ✅
- **Requires**: (hM : isTrianglePacking G M)
- **Statement**: (path4_cover G cfg).card ≤ 8

### Supporting lemmas:
- `cover_hits_sharing_A`: Triangles sharing ≥2 vertices with A are covered
- `cover_hits_sharing_D`: Triangles sharing ≥2 vertices with D are covered
- `path4_counterexample`: Proof that without packing, can have >8 edges

## NOT PROVEN (sorry):

### tau_le_8_path4 ❌
- The main theorem depends on `path4_cover_card_le_8` (negated version)
- Need to use `path4_cover_card_le_8_of_packing` instead

## FALSE LEMMA:

### path4_cover_card_le_8 (without packing) ❌
- **Counterexample**: A={0,3,4,5} has 4 elements (not a triangle!)
- **Fix**: Use `path4_cover_card_le_8_of_packing` with packing hypothesis
