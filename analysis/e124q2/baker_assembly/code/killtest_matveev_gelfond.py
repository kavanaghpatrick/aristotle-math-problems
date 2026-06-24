"""KILL-TEST the matveev + gelfond sufficiency numbers, fully independent re-derivation."""
from math import log, exp, log2

ln2, ln3, ln4, ln7 = log(2), log(3), log(4), log(7)

print("="*70)
print("(1) MATVEEV CONSTANT re-derivation")
print("="*70)
# matveev claims: real case, log|Lambda| > -1.4 * 30^(n+3) * n^4.5 * D^2 (1+logD)(1+logB) A1...An
# n=2, D=1. C := 1.4 * 30^5 * 2^4.5
C = 1.4 * 30**5 * 2**4.5
print(f"  1.4 * 30^5 * 2^4.5 = {C:.5e}   (matveev says 7.6978e8)")
A1, A2 = ln3, ln4   # A_j = max{D h(a_j), |log a_j|, 0.16}; h(3)=log3, etc, D=1
print(f"  A1=log3={A1:.4f}, A2=log4={A2:.4f}")
CA = C * A1 * A2
print(f"  C*A1*A2 = {CA:.5e}   (matveev says 1.1724e9)")
# So log|Lambda| > -CA*(1+logB), B=p. And |3^p-4^q|=4^q|Lambda|, rel = |3^p-4^q|/3^p ~ |Lambda|*(4^q/3^p)
# 4^q/3^p ~ 1 at close pairs, so rel ~ |Lambda|. log(rel) > -CA*(1+log p).
print(f"  => log(rel) > -{CA:.4e}*(1+log p)  [the relative-spacing form]")

print()
print("="*70)
print("(2) CROSSOVER p*: smallest p with E_known(p) < 0.356*p (NEEDED), i.e. spacing self-certifies")
print("="*70)
# E_loss(p) in base-3 orders: rel = 3^{-E}, so E = -log(rel)/log3.
# KNOWN bound: rel > exp(-CA*(1+log p)) => E_known(p) = CA*(1+log p)/log3  (Matveev)
# BEGL/MW: rel > exp{ln3(p-500 ln4(8+ln p)^2)}/3^p ... careful: BEGL bound is on |3^p-4^q| not rel.
#   |3^p-4^q| > exp{ln3(p - 500 ln4 (8+ln p)^2)}  => rel=|.|/3^p > exp{ln3(p-500ln4(8+lnp)^2)}/3^p
#   = exp{ln3(p-500ln4(8+lnp)^2) - p ln3} = exp{-ln3*500 ln4 (8+ln p)^2}
#   => E_MW(p) = -log(rel_LB)/log3 = 500 ln4 (8+ln p)^2   (the loss exponent)
def E_MW(p): return 500*ln4*(8+log(p))**2
def E_Mat(p): return CA*(1+log(p))/ln3
NEEDED_slope = ln2/ln7   # base-7 counting exponent log2/log7
print(f"  NEEDED slope = log2/log7 = {NEEDED_slope:.4f}  (gelfond says 0.356)")
# crossover: E(p) = NEEDED_slope * p
import numpy as np
def crossover(Efn, hi):
    ps = np.arange(2, hi)
    # vectorize
    if Efn is E_MW:
        E = 500*ln4*(8+np.log(ps))**2
    else:
        E = CA*(1+np.log(ps))/ln3
    need = NEEDED_slope*ps
    idx = np.where(need > E)[0]
    return ps[idx[0]] if len(idx) else None
pMW = crossover(E_MW, 2_000_000)
print(f"  BEGL/MW crossover p* = {pMW}   (matveev/gelfond say ~2.94e5; nesterenko 293885)")
# Matveev crossover is ~2.67e10, too big to vectorize; solve p = E_Mat(p)/slope by iteration
p = 1e10
for _ in range(300):
    p = E_Mat(p)/NEEDED_slope
print(f"  Matveev crossover p* = {p:.3e}   (matveev says ~2.67e10)")

print()
print("="*70)
print("(3) GELFOND TABLE 1: E_actual, E_MW, E_Matveev at convergents")
print("="*70)
print(f"{'p':>4} {'q':>4} {'rel':>12} {'E_act':>7} {'NEED=.356p':>11} {'E_MW':>10} {'E_Matveev':>11}")
for p,q in [(5,4),(24,19),(29,23),(53,42),(612,485),(665,527)]:
    P,Q=3**p,4**q
    rel=abs(P-Q)/min(P,Q)
    Eact=-log(rel)/ln3
    print(f"{p:>4} {q:>4} {rel:>12.3e} {Eact:>7.3f} {NEEDED_slope*p:>11.3f} {E_MW(p):>10.0f} {E_Mat(p):>11.3e}")
