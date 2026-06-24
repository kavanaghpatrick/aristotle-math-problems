# ============================================================
# Verify baker's large-deviation kill does NOT apply to the gap lemma.
# baker's kill: the "count" M*frac (B7 shifts * B3+B4 density) is a MEAN; at the
# straggler n0=581 (k=1) the mean predicts ~4.3 but actual count is 0. First-moment dies.
#
# The GAP LEMMA is atomSum(<v) >= v + 2N0. Is this a count/mean, or deterministic?
# ============================================================
N0_1=581; N0_2=3982888
def atomSum_below(v, kmin=2):
    s=0
    for d in (3,4,7):
        p=d**kmin
        while p<v: s+=p; p*=d
    return s

print("Is the gap lemma a first-moment count (baker's kill applies) or deterministic?")
print()
print("The gap lemma atomSum(<v) >= v + 2N0 is a SUM OF ATOMS — an EXACT integer,")
print("NOT a representation count, NOT a mean, NOT a probability. It does not 'predict'")
print("anything; it's a deterministic arithmetic inequality on the atom set.")
print()
print("baker's large-deviation kill applies to: r(n) = #{B7 shifts c: n-c in B3+B4}, the")
print("REPRESENTATION COUNT — a first-moment quantity that dips to 0 at stragglers.")
print()
print("These are DIFFERENT objects:")
print("  - r(n) [count]: dies at stragglers (n0=581, n0=3982888). baker's kill is CORRECT.")
print("  - atomSum(<v) [gap lemma]: deterministic; does NOT involve representation counts.")
print()
print("CRITICAL: the gap lemma is evaluated at ATOMS v (powers 3^e,4^e,7^e), all of which")
print("are FAR ABOVE the stragglers in the tail. The stragglers (n0) are NOT atoms and are")
print("NOT where the gap lemma is checked. The straggler n0=3982888 is handled by the FINITE")
print("SIEVE (L2) + native_decide base case, NEVER by the gap lemma.")
print()
# demonstrate: the gap lemma at the first atom above N0(2) is comfortably satisfied
v = 4**11  # first atom above N0(2)
asb = atomSum_below(v)
print("At first atom above N0(2): v=4^11=%d, atomSum(<v)=%d, v+2N0=%d, margin=%d" % 
      (v, asb, v+2*N0_2, asb-(v+2*N0_2)))
print("  => gap lemma holds with margin %d (deterministic, no count involved)." % (asb-(v+2*N0_2)))
print()
print(">>> baker's large-deviation kill is CORRECT for the joint-covering count route")
print("    (BRIDGE-RIESZ-0), but does NOT touch the gap-lemma route. The gap lemma is")
print("    deterministic atom arithmetic, evaluated at atoms in the tail, never at stragglers.")
print("    So k=2 STAYS CLOSED via the gap lemma. The retraction affects only the SUPERSEDED")
print("    joint formulation (which lives on at all-k, where baker's kill IS relevant). <<<")
