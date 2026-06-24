# Summary of changes for run fef4266f-4167-44f0-be9b-ad01669961ff
## Erdős 364 — mod-44100 closure for consecutive powerful triples

Successfully formalized and proved `erdos_364_mod44100` in `RequestProject/Main.lean`.

### What was proved

If n, n+1, and n+2 are all powerful numbers (every prime dividing them also has its square dividing them), then:
1. n ≡ 3 (mod 4)
2. n mod 9 ∈ {0, 7, 8}
3. n mod 25 ∈ {0,1,2,6,7,11,12,16,17,21,22,23,24}
4. n mod 49 ∈ {0,1,2,3,4,8,9,10,11,15,16,17,18,22,23,24,25,29,30,31,32,36,37,38,39,43,44,45,46,47,48}

### Proof structure

The proof decomposes into three layers:

**Layer 1 — Obstruction lemmas (13 lemmas):** For each prime p ∈ {2,3,5,7} and each residue r mod p² that is divisible by p but not p², prove that no powerful number can have that residue. For example, if x ≡ 5 (mod 25) then 5∣x but 25∤x, contradicting powerfulness. These are: `not_powerful_of_mod4_eq2`, `not_powerful_of_mod9_eq{3,6}`, `not_powerful_of_mod25_eq{5,10,15,20}`, `not_powerful_of_mod49_eq{7,14,21,28,35,42}`.

**Layer 2 — Component lemmas (4 lemmas):** For each modulus (4, 9, 25, 49), case-split on n's residue and show that any residue outside the allowed set forces one of n, n+1, n+2 to hit a forbidden residue from Layer 1. These are `powerful_triple_mod4`, `powerful_triple_mod9`, `powerful_triple_mod25`, `powerful_triple_mod49`.

**Layer 3 — Main theorem:** Simple conjunction of the four component lemmas.

### Verification

- Builds cleanly with no `sorry`, no warnings, no errors.
- Uses only standard axioms: `propext`, `Classical.choice`, `Quot.sound`.
- The mod-25 and mod-49 conditions appear to be new formalizations not found in prior literature (Beckon 2019 covered only mod 36).