Added [scripts/erdos406_search.py](/Users/patrickkavanagh/math/scripts/erdos406_search.py) and [docs/erdos406_baker_note.md](/Users/patrickkavanagh/math/docs/erdos406_baker_note.md).

The script searches `2^n` by maintaining its ternary digits directly and doubling in base 3 each step. I ran it through `n = 20000` and found only:
- `n = 0`: `2^0 = 1`, ternary `1`
- `n = 2`: `2^2 = 4`, ternary `11`
- `n = 8`: `2^8 = 256`, ternary `100111`

There were no other hits for `0 <= n <= 20000`. I also cross-checked the script against a direct brute-force base-conversion check for `n <= 200`, and the hit lists matched exactly.

On the math side: Baker/S-unit methods do give finiteness for each fixed number `r` of nonzero ternary digits in
`2^n = 3^{a_1} + ... + 3^{a_r}`.
What they do not currently give is a uniform bound on `r`, so they do not settle Erdos 406 itself. That is the key distinction captured in the note. Current status still appears to be open; a useful modern reference is Robert Saye’s paper and the Erdos Problems page:
- https://cs.uwaterloo.ca/journals/JIS/VOL25/Saye/saye3.pdf
- https://www.erdosproblems.com/forum/thread/406

Run it with:
```bash
python3 scripts/erdos406_search.py --max-n 20000
```

If you want, I can extend the note into a fuller proof sketch for the fixed-weight Baker argument, or push the computation much further with a more optimized representation.