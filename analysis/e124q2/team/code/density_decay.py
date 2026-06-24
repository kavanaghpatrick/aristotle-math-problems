import sys
sys.path.insert(0,'/tmp')
from cofin_check import sumset_bitset

D = tuple(int(x) for x in sys.argv[1].split(','))
k = int(sys.argv[2]); N = int(sys.argv[3])
r = sumset_bitset(D,k,N)
full = (1<<(N+1))-1
missing = full & ~r
W = N//15
print(f"D={D} k={k} N={N} gap density per window of {W}:")
for start in range(0, N, W):
    end = min(start+W, N+1)
    window = (missing >> start) & ((1<<(end-start))-1)
    c = bin(window).count('1')
    bar = '#'*int(50*c/W)
    print(f"  [{start:>9},{end:>9}): {c:>6} {c/W:.5f} {bar}")
