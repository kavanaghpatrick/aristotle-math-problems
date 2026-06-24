"""
WHY does the Jensen/Skottova-Steiner circulant collapse at k=4?

The distance set has three pieces. Track the WIDTH (number of integers) of each
base interval as a function of k (for fixed m), and find the exact k at which each
goes negative/empty.

D1 = {1,3,...,2m-1}        -- width m, INDEPENDENT of k. Always present.
D2 (k even) = [2m, (k-4)m+2]   width = (k-4)m+2 - 2m + 1 = (k-6)m+3
D3 (k even) = [(k+2)m-1, (2k-4)m+1]  width = (2k-4)m+1 - ((k+2)m-1) + 1 = (k-6)m+3
D2 (k odd)  = [2m, (k-3)m+1]   width = (k-3)m+1 - 2m + 1 = (k-5)m+2
"""

def widths(k, m):
    d1 = m  # |{1,3,...,2m-1}|
    if k % 2 == 0:
        d2 = (k - 6) * m + 3
        d3 = (k - 6) * m + 3
    else:
        d2 = (k - 5) * m + 2
        d3 = 0
    return d1, max(d2, 0), max(d3, 0), d2, d3  # last two are RAW (can be <=0)


print("Width of each distance-interval base, as a function of k (m=3 fixed):")
print(f"{'k':>3} {'parity':>6} {'|D1|':>5} {'|D2|raw':>8} {'|D3|raw':>8}  note")
for k in range(4, 11):
    m = 3
    d1, d2c, d3c, d2raw, d3raw = widths(k, m)
    note = ""
    if k % 2 == 0:
        if d2raw <= 0:
            note = "D2,D3 EMPTY -> only odd distances -> chi<=3"
    else:
        if d2raw <= 0:
            note = "D2 EMPTY -> only odd distances -> chi<=3"
    print(f"{k:>3} {'even' if k%2==0 else 'odd':>6} {d1:>5} {d2raw:>8} {d3raw:>8}  {note}")

print()
print("EXACT threshold (the inequality that defines the wall):")
print("  k EVEN: D2 nonempty  <=>  (k-6)m+3 >= 1  <=>  (k-6)m >= -2.")
print("          For m>=3: need k-6 >= 0 roughly, i.e. k>=6. m=1,2 edge cases:")
for m in (1, 2, 3, 4, 5):
    # smallest even k with (k-6)m+3>=1
    k = 4
    while (k - 6) * m + 3 < 1:
        k += 2
    print(f"          m={m}: smallest even k with D2 nonempty = {k}  "
          f"((k-6)*{m}+3 = {(k-6)*m+3})")
print("  k ODD : D2 nonempty  <=>  (k-5)m+2 >= 1  <=>  (k-5)m >= -1.")
for m in (1, 2, 3, 4, 5):
    k = 5
    while (k - 5) * m + 2 < 1:
        k += 2
    print(f"          m={m}: smallest odd k with D2 nonempty = {k}  "
          f"((k-5)*{m}+2 = {(k-5)*m+2})")

print()
print("CONCLUSION:")
print("  k=5 (odd):  D2 width = (5-5)m+2 = 2 > 0  -> D2 = {2m, 2m+1}, present. WORKS.")
print("  k=4 (even): D2 width = (4-6)m+3 = -2m+3.  >0 only for m=1; <=0 for all m>=2.")
print("              D3 width identical = -2m+3. Same collapse.")
print("  => At k=4, for ANY m>=2 the only surviving distances are the odd")
print("     numbers D1={1,3,..,2m-1}. The graph cannot reach chromatic number 4.")
print("  The construction's '+1 chromatic boost' lives ENTIRELY in D2/D3 (the")
print("  even/long distances), and those vanish below k=5 (odd) / k=6 (even).")
