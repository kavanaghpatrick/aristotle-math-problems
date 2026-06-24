"""
FIXED: near-coincidences 3^p ~ 4^q.  p*log3 ~ q*log4  =>  p/q ~ log4/log3 = theta.
So p/q are convergents of theta (p=3-exponent, q=4-exponent), p>q.
Dominant: 3^5=243 ~ 4^4=256.  Convergents p/q of theta: 1/1,4/3,5/4,24/19,29/23,...
WAIT: 5/4 means p=5,q=4 (3^5 vs 4^4). YES. Earlier I printed num/den backwards.
"""
import math
theta = math.log(3)/math.log(4)   # = 0.7925; q/p ~ this. p/q ~ log4/log3=1.2619
# convergents of log4/log3 give p/q with p the 3-exponent
t = math.log(4)/math.log(3)  # 1.2619
def cf(x,n):
    a=[]
    for _ in range(n):
        ai=math.floor(x); a.append(ai); x-=ai
        if abs(x)<1e-13: break
        x=1/x
    return a
def convergents(a):
    h=[0,1]; k=[1,0]; out=[]
    for ai in a:
        h.append(ai*h[-1]+h[-2]); k.append(ai*k[-1]+k[-2]); out.append((h[-1],k[-1]))
    return out
A=cf(t,15); C=convergents(A)
print("CF(log4/log3)=",A)
print(f"{'p(3-exp)':>9} {'q(4-exp)':>9} {'|3^p-4^q|':>26} {'rel=/3^p':>13} {'-log_3 rel':>11} {'beta_p':>8}")
# beta_p := -log_3(rel) / p  is the 'irrationality-type' exponent in the bound rel >= 3^{-beta*p}... 
# Actually express |3^p-4^q| >= 3^{p - E(p)}, E(p)=-log_3(rel). We want E(p) growth.
rows=[]
for (p,q) in C:
    if p>200: break
    if p<1: continue
    P=3**p; Q=4**q; d=abs(P-Q)
    if d==0: 
        print(f"{p:>9} {q:>9} {'0 (impossible unless trivial)':>26}")
        continue
    rel=d/P
    Elog=-math.log(rel)/math.log(3)   # E(p): |3^p-4^q| = 3^{p-E}
    rows.append((p,q,d,rel,Elog))
    print(f"{p:>9} {q:>9} {d:>26} {rel:>13.4e} {Elog:>11.4f} {Elog/p if p else 0:>8.4f}")

print("\nKey: |3^p - 4^q| = 3^{p - E(p)}.  E(p) = 'loss exponent'.")
print("If E(p) = O((log p)^2) (MW shape) the spacing is 3^p / 3^{O((log p)^2)} -- nearly full size.")
print("E(p) values above are TINY (sub-1 to ~5) -- the spacing is essentially 3^p at every convergent.")
