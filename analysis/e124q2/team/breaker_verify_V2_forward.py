import numpy as np
# maverick's V2/581 MIRAGE claim: the FORWARD reachable-residue state count GROWS as 3^s, not bounded.
# Definition to verify: # of distinct residues mod 3^s reachable as subset-sums of atoms < 3^s,
# for (3,4,7) k=1. maverick's sequence: 1,7,20,81,217,727 -> 3^s.
# This is the forward reachable set of the transfer process (vs the Myhill-Nerode count of the
# already-known-finite miss set, which presumes finiteness).
D=(3,4,7); k=1
def reachable_residues_mod(D,k,s):
    """# distinct residues mod 3^s reachable as subset-sums of atoms {d^j: d in D, j>=k, d^j < 3^s}."""
    M=3**s
    atoms=[]
    for d in D:
        j=k
        while d**j < M: atoms.append(d**j); j+=1   # atoms STRICTLY < 3^s
    # reachable residues mod M via subset-sum (each atom once)
    reach=np.zeros(M,dtype=bool); reach[0]=True
    for a in atoms:
        ar=a%M
        # reach |= roll(reach, ar)  (subset-sum: add atom a's residue)
        reach = reach | np.roll(reach, ar)
    return int(reach.sum())
print("Forward reachable-residue count mod 3^s using atoms < 3^s, (3,4,7) k=1:")
print(f"{'s':>3}{'3^s':>10}{'#reachable':>12}{'maverick':>10}")
mav=[1,7,20,81,217,727]
for s in range(1,8):
    c=reachable_residues_mod(D,k,s)
    m=mav[s-1] if s-1<len(mav) else None
    match = "MATCH" if (m is not None and c==m) else ("" if m is None else "DIFFER")
    print(f"{s:>3}{3**s:>10}{c:>12}{str(m):>10}  {match}")
print("\n=> if the sequence GROWS (toward 3^s), the forward transfer state is UNBOUNDED => V2 matrix")
print("   is NOT finite forward => the '37 states' is a Myhill-Nerode count presuming finiteness => MIRAGE.")

# Extend: does it stay FULL (3^s) after s=7, confirming residue-coverage but UNBOUNDED state count?
print("\nExtension s=7..10 (does it stay = 3^s = full coverage?):")
for s in range(7,11):
    c=reachable_residues_mod(D,k,s)
    print(f"  s={s}: 3^s={3**s}, #reachable={c}, full={c==3**s}, fraction={c/3**s:.4f}")
