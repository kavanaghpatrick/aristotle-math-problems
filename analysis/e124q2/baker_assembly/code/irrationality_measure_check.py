"""
VERIFIER pre-load: what does an irrationality measure of theta=log3/log4 give,
and is it the RIGHT object for bounding |3^p - 4^q|?

CATEGORY CHECK. The gap |3^p - 4^q|. Write 4^q = 3^p * (4^q/3^p). With L = q*ln4 - p*ln3 (a linear
form in two logs), 4^q/3^p = exp(L), so |3^p - 4^q| = 3^p * |exp(L) - 1| ~ 3^p * |L| for small L.
So bounding |3^p-4^q| from below  <=>  bounding |L| = |q ln4 - p ln3| from below
  <=> bounding |q/p - ln3/ln4| from below  (divide by p ln4)
  = |q/p - theta|,  theta = ln3/ln4.
THIS is where an irrationality measure of theta enters:
  irrationality measure mu(theta): |theta - h/k| > c/k^mu  for all h/k.
With h=q, k=p: |theta - q/p| > c/p^mu  =>  |L| > c*ln4/p^(mu-1)  =>  |3^p-4^q| > 3^p * c*ln4/p^(mu-1).
That is a POLYNOMIAL-in-p relative bound: rel gap > C/p^(mu-1).
COMPARE to MW's exp(-C(ln p)^2): polynomial/p^(mu-1) is MUCH STRONGER (bigger) than exp(-C(ln p)^2)
for large p? Check: p^-(mu-1) vs exp(-C(ln p)^2)=p^(-C ln p). For large p, C ln p > mu-1, so
exp(-C(ln p)^2) is SMALLER. So an irrationality measure, IF it applies to theta=ln3/ln4, gives a
STRONGER bound than MW. KEY QUESTION: is mu(ln3/ln4) KNOWN and finite & effective?
"""
from math import log
import mpmath as mp
mp.mp.dps=50
theta = mp.log(3)/mp.log(4)
print("theta = ln3/ln4 =", mp.nstr(theta,30))
# empirical irrationality measure proxy: for each convergent, mu_k = -ln|theta-h/k| / ln(k)
cf=[]; x=theta
for _ in range(25):
    a=int(mp.floor(x)); cf.append(a); fr=x-a
    if fr==0: break
    x=1/fr
print("CF:", cf[:15])
# convergents and the measured exponent |theta - h/k| ~ 1/(k^mu)
h_prev,h_cur=1,cf[0]; k_prev,k_cur=0,1
print("\nk(=p), |theta-h/k|, implied local mu = -ln|err|/ln k:")
for a in cf[1:14]:
    h_next=a*h_cur+h_prev; k_next=a*k_cur+k_prev
    if k_next>1:
        err=abs(theta - mp.mpf(h_next)/k_next)
        mu = -mp.log(err)/mp.log(k_next)
        print(f"  k={int(k_next):>8d}  err={mp.nstr(err,4):>12}  mu_local={mp.nstr(mu,5)}")
    h_prev,h_cur=h_cur,h_next; k_prev,k_cur=k_cur,k_next
print("\nNOTE: log3/log4 is a ratio of logs of multiplicatively-independent integers.")
print("Its irrationality is known (Baker), but an EFFECTIVE FINITE irrationality MEASURE")
print("mu(log3/log4) < infinity that is SHARP enough is the open question -- check what's CITED.")
