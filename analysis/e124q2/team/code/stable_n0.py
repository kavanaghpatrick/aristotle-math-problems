"""Find the TRUE threshold N0(D,k): largest missing value, verified stable by checking that
a window 2x larger gives the same answer (no further gaps above)."""
import sys, math
sys.path.insert(0,'.')
from reach import reachable

def largest_missing(D,k,N):
    r=reachable(D,k,N)
    for n in range(N,-1,-1):
        if not ((r>>n)&1): return n
    return -1

def true_n0(D,k,N_start=100000, N_cap=20_000_000):
    N=N_start
    while N<=N_cap:
        lm=largest_missing(D,k,N)
        # stable if largest missing is comfortably below N (say < N/2)
        if lm < N//2:
            return lm, N, True
        N*=2
    return largest_missing(D,k,N_cap), N_cap, False

if __name__=="__main__":
    import ast
    D=ast.literal_eval(sys.argv[1]); k=int(sys.argv[2])
    lm,N,ok=true_n0(D,k)
    status="STABLE" if ok else "TRUNCATED(window cap hit)"
    print(f"D={D} k={k}: N0={lm}  (verified with window N={N}, {status})")
