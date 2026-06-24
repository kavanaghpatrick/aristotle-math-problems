import numpy as np
# Local coverage check for two-prime-power families: does gcd=1 still give full residue coverage
# mod powers of 2 and 3, despite all bases being 2^a or 3^b? (modular's lemma predicts YES.)
def Sdk_mod(d,k,M,depth=200):
    """residues of d^k * B_d mod M: subset-sum closure of {d^j mod M : j>=k}."""
    res={0}; seen=set()
    j=k
    powers=[]
    for _ in range(depth):
        powers.append(pow(d,j,M)); j+=1
    # subset-sum closure (submonoid)
    cur={0}
    for p in set(powers):
        cur |= {(x+p)%M for x in cur}
    # iterate to closure
    for _ in range(40):
        nxt=set(cur)
        for p in set(powers):
            nxt |= {(x+p)%M for x in cur}
        if nxt==cur: break
        cur=nxt
    return cur
def sumset_mod(D,k,M):
    res={0}
    for d in D:
        S=Sdk_mod(d,k,M)
        res={(a+b)%M for a in res for b in S}
    return res
fams=[(3,4,8,9),(3,4,8,32),(3,4,8,27),(3,4,9,16),(3,4,9,27,81)]
print("Local residue coverage mod 2^a, 3^a for two-prime families (full=no obstruction):")
for D in fams:
    line=f"  D={str(D):<18}"
    full=True
    for M in [8,16,32,64,9,27,81,243, 64*81]:
        for k in [1,2,3]:
            cov=sumset_mod(D,k,M)
            if len(cov)!=M: full=False; line+=f" MISS(mod{M},k{k}:{len(cov)}/{M})"
    line += " ALL FULL" if full else ""
    print(line)
