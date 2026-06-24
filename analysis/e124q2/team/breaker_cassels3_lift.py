import numpy as np
def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    for p in at: rep[p:]|=rep[:N+1-p].copy()
    return rep
def Sd_vals(d,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    j=k
    while d**j<=N: p=d**j; rep[p:]|=rep[:N+1-p].copy(); j+=1
    return set(int(x) for x in np.flatnonzero(rep))
# The STRONGEST possible deflation: b*h = sum_d a_d. Try to construct a rep of h by "dividing out b".
# For the IFS map x->b*x on base-b: b*(b^k B_b) = b^{k+1} B_b, and b * (d^k B_d) for d!=b has NO clean
# base-b structure. So the only deflatable part is the base-b summand. Test: does ANY rep of b*h have
# the form where deflation yields a valid rep of h? Exhaustively: h in R iff h = a3+a4+a7. We KNOW h=581
# is NOT (it's a hole). The deflation can't create what doesn't exist. Confirm no lift exists:
D=(3,4,7); k=1; N=3_000_000
full=atoms_repset(D,k,N)
S3=Sd_vals(3,k,N); S4=Sd_vals(4,k,N); S7=Sd_vals(7,k,N)
h=581
# is there ANY a3,a4,a7 with a3+a4+a7=h? (this is just "h in R", which is False)
found=False
for a3 in sorted(S3):
    if a3>h: break
    for a4 in sorted(S4):
        if a3+a4>h: break
        if (h-a3-a4) in S7: found=True; break
    if found: break
print(f"h=581: any direct rep a3+a4+a7=581? {found} (=> h in R? {bool(full[h])})")
print("The deflation rule b*h in R => h in R would FALSELY certify h=581 representable (b*h IS in R for all b),")
print("but no rep of h exists. So the rule is UNSOUND — co-presence of b*h does NOT lift to a rep of h.")
print("\nWHY no valid lift: b*h = sum a_d. To deflate to h, need each a_d = b*(something in d^k B_d). But")
print("b*(d^k B_d) = d^k B_d only when b's factor is absorbed by base d — impossible for d coprime to b.")
print("E.g. 3*581=1743 in R, but its rep (e.g. using base-4,7 atoms) has terms NOT divisible by 3, so you")
print("cannot divide the whole rep by 3 to get a rep of 581. The IFS inverse map is not well-defined on the sumset.")
