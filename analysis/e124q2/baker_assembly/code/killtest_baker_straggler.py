"""Kill-test baker's pointwise claim: N0(2)=3,982,888 has 0 B7-reps, neighbors have 3-7."""
import numpy as np

N=4_300_000
# B3+B4 reachable (k=2): atoms 3^j,4^j for j>=2
def base_reach(d,k,N):
    r=np.zeros(N+1,dtype=bool); r[0]=True
    e=k
    while d**e<=N:
        a=d**e; r[a:]|=r[:N+1-a]; e+=1
    return r
B3=base_reach(3,2,N); B4=base_reach(4,2,N)
# B3+B4 set
B34=np.zeros(N+1,dtype=bool)
idx4=np.nonzero(B4)[0]
for a in idx4:
    if a==0: B34|=B3
    else: B34[a:]|=B3[:N+1-a]
# B7 subset-sums (k=2): values c = 7^j sums, j>=2
b7=[]; e=2
while 7**e<=N: b7.append(7**e); e+=1
# enumerate B7 subset sums <= N
b7sums=[0]
for a in b7:
    b7sums = sorted(set(b7sums + [s+a for s in b7sums if s+a<=N]))
b7sums=np.array(b7sums)
print(f"B7 atoms (k=2): {b7}, #B7 subset-sums <= {N}: {len(b7sums)}")

def r_b7(n):
    # # of c in B7sums with n-c in B3+B4 and n-c>=0
    cnt=0
    for c in b7sums:
        if c>n: break
        if B34[n-c]: cnt+=1
    return cnt

for n in [3982886,3982887,3982888,3982889,3982890]:
    print(f"  n={n}: r_B7={r_b7(n)}  {'<-- N0(2) straggler' if n==3982888 else ''}")
