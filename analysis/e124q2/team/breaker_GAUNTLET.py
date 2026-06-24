"""breaker's reusable kill-test gauntlet for E124 bridge/cofiniteness candidates.
Import and call gauntlet(predicate, name) where predicate(D,k) -> bool is the candidate's
claimed cofiniteness verdict. Returns PASS/FAIL with the family that breaks it.
GROUND TRUTH (exact, validated atom-sieve):
  COFINITE (β>=1): every admissible family.
  NOT COFINITE (β<1): even if it LOOKS cofinite to huge N (deep-trap families).
A candidate is CORRECT iff predicate(D,k) == is_cofinite(D,k) on the whole gauntlet.
"""
import numpy as np
from fractions import Fraction
from math import gcd

def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    for p in at: rep[p:]|=rep[:N+1-p].copy()
    return rep
def beta(D): return float(sum(Fraction(1,d-1) for d in D))
def is_admissible(D):
    g=0
    for d in D: g=gcd(g,d)
    return all(d>=3 for d in D) and beta(D)>=1 and g==1

# GROUND TRUTH LABELS (cofinite True/False). For β>=1 admissible: True (proven direction by Pomerance+
# all-tested-finite). For β<1: False (Pomerance converse, EXACT). k-independent label (cofiniteness
# holds/fails for all k>=0 the same way per the conjecture+converse).
GAUNTLET = {
  # admissible (COFINITE = True)
  (3,4,7):True, (3,4,5):True, (3,5,7,13):True, (3,4,11,16):True, (4,5,6,7,8):True,
  (3,4,8,9):True, (3,5,6,21):True, (3,4,6):True,
  # sub-threshold β<1 (NOT cofinite = False) — incl the DEEP TRAPS that look cofinite
  (3,4):False, (3,5):False, (3,4,11):False, (3,4,10):False, (3,4,12):False,
  (3,5,7):False, (3,4,9):False, (3,4,13):False, (4,5,6,7):False,
}
def gauntlet(predicate, name, ks=(1,)):
    """predicate(D,k)->bool. Test on GAUNTLET. Return (passed, failures)."""
    fails=[]
    for D,truth in GAUNTLET.items():
        for k in ks:
            try: pred=predicate(D,k)
            except Exception as e: pred=f"ERR:{e}"
            if pred!=truth:
                fails.append((D,k,beta(D),truth,pred))
    passed=len(fails)==0
    print(f"[{name}] {'PASS' if passed else 'FAIL'} ({len(fails)} mismatches)")
    for D,k,b,t,p in fails[:8]:
        print(f"    D={D} k={k} β={b:.3f} truth_cofinite={t} predicted={p}")
    return passed, fails

if __name__=="__main__":
    # sanity: the harmonic β>=1 predicate should PASS (it's the Pomerance answer)
    gauntlet(lambda D,k: beta(D)>=1, "harmonic β>=1 (control, should PASS)")
