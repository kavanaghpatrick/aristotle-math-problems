"""
Ground-truth reference: brute-force the EXACT 647.lean predicate over small n.
Predicate: n is a witness iff  max_{m in [0,n)} (m + tau(m)) <= n+2.
(sup over Fin n includes m=0; tau(0)=sigma_0(0); in Mathlib sigma 0 0 = 0.
 We use tau(m)=number of divisors, tau(0):=0 to match sigma 0 0 = 0, tau(1)=1.)
OEIS A087280 'numbers n such that max_{k<n}(k+d(k)) <= n+2' = 5,8,10,12,24 (McCranie).
NOTE: A087280 may index differently; we test which convention reproduces 5,8,10,12,24.
"""
def tau(m):
    if m==0: return 0
    c=0; i=1
    while i*i<=m:
        if m%i==0:
            c+= 1 if i*i==m else 2
        i+=1
    return c

def is_witness(n):
    # max over m < n of m+tau(m) <= n+2
    mx=0
    for m in range(0,n):
        v=m+tau(m)
        if v>mx: mx=v
    return mx <= n+2

wit=[n for n in range(1,200) if is_witness(n)]
print("witnesses (m+tau(m) convention, m in [0,n)) up to 200:", wit)

# Try the strict m<n with m starting at 1
def is_witness2(n):
    mx=0
    for m in range(1,n):
        v=m+tau(m)
        if v>mx: mx=v
    return mx <= n+2
wit2=[n for n in range(1,200) if is_witness2(n)]
print("witnesses (m in [1,n)) up to 200:                ", wit2)
