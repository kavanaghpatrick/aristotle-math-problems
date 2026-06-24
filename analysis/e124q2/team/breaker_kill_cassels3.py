import numpy as np
def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    for p in at: rep[p:]|=rep[:N+1-p].copy()
    return rep
def repset_vals(D,k,N): return atoms_repset(D,k,N)
# INV-cassels-3 (UNSCALE): claim h hole, b*h in R => h in R via inverse IFS map x->b*x. 
# (i) SOUNDNESS KILL: does b*h in R actually IMPLY h in R? The claimed lift: take a rep of b*h, "divide
# out base b". But b*h in R means b*h = sum_{d} a_d (a_d in d^k B_d). For h to be representable we'd need
# b*h's representation to have a base-b-divisible structure. TEST: among holes h with b*h in R, how many
# have h ALSO in R? (h is a HOLE, so h NOT in R by definition!) => the implication "b*h in R => h in R"
# is FALSE by construction (h is a hole). Let me verify the logic carefully.
D=(3,4,7); k=1; N=3_000_000
full=repset_vals(D,k,N)
holes=[int(x) for x in np.flatnonzero(~full)]
print(f"(3,4,7) k=1: {len(holes)} holes (max {max(holes)})")
# For each hole h, check which b in D have b*h in R:
print("\nINV-cassels-3 SOUNDNESS: for each hole h, is b*h in R for some b? And does that 'imply' h in R?")
print("(h is a HOLE => h NOT in R. So if b*h in R, the claimed implication b*h in R => h in R is VIOLATED.)")
violations=0; cohits=0
for h in holes:
    for b in D:
        if b*h<=N and full[b*h]:
            cohits+=1
            # the implication says h should be in R; but h is a hole => VIOLATION of soundness
            violations+=1
            break
print(f"  holes h with b*h in R for some b: {cohits}/{len(holes)}")
print(f"  => these are SOUNDNESS VIOLATIONS: b*h in R but h is a HOLE (not in R). count={violations}")
print(f"\n  CONCLUSION: 'b*h in R => h in R' is FALSE — {violations}/{len(holes)} holes h have b*h in R yet h not in R.")
print("  The co-presence cassels saw (36/37) is exactly the SET OF COUNTEREXAMPLES to the deflation rule.")
# double-check one explicitly
h=holes[-1]  # largest hole 581
for b in D:
    if b*h<=N:
        print(f"  e.g. h={h} (hole, not in R: {not full[h]}), b={b}: b*h={b*h} in R? {bool(full[b*h])}")
