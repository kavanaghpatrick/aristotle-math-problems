import sys, math
sys.path.insert(0,'.')
from reach import reachable
def largest_missing(D,k,N):
    r=reachable(D,k,N)
    for n in range(N,-1,-1):
        if not ((r>>n)&1): return n
    return -1
# The two exact sum=1 cases + a couple near-tight
cases=[[3,4,7],[3,5,7,13],[3,4,12,14],[3,5,8,10],[3,6,7,8]]
N=400000
print(f"{'D':<22}{'k=1 N0':>10}{'k=2 N0':>10}{'k=3 N0':>10}")
for D in cases:
    n1=largest_missing(D,1,N)
    n2=largest_missing(D,2,N)
    n3=largest_missing(D,3,N)
    print(f"{str(D):<22}{n1:>10}{n2:>10}{n3:>10}")
