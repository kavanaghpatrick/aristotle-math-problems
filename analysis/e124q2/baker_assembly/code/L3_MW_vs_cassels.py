import math
# ============================================================
# THE DECISIVE COMPUTATION: does the Cassels ratio S(a-)/a stay > 1 at the
# deep CF convergents, and does the MW bound GUARANTEE it?
#
# At a = 3^p with 4^q just below (q = floor(p*log3/log4)), the ratio dips
# because 4^q is close to 3^p but the next 4-power 4^{q+1} > 3^p is excluded.
# Let me get the ASYMPTOTIC dip value and see if it -> 1 (boundary) or stays
# bounded above 1.
# ============================================================
log3=math.log(3); log4=math.log(4); log7=math.log(7)

# Asymptotic ratio at a=3^p (large p): 
# S(a-)/a = [3-ray below 3^p]/3^p + [4-ray below 3^p]/3^p + [7-ray below 3^p]/3^p
# 3-ray below 3^p: sum_{j=2}^{p-1} 3^j = (3^p - 9)/2, over 3^p -> 1/2.
# 4-ray below 3^p: sum_{4^j < 3^p} 4^j. Largest 4-power below 3^p is 4^q, q=floor(p log3/log4).
#   sum = (4^{q+1}-16)/3 ~ 4^{q+1}/3 = 4*4^q/3. Over 3^p: (4/3)*(4^q/3^p).
#   4^q/3^p = exp(q log4 - p log3) =: rho in (1/4, 1] (how close 4^q is below 3^p).
# 7-ray below 3^p: ~ (7/6)*(7^l/3^p), 7^l largest 7-power below 3^p.
# So ratio ~ 1/2 + (4/3)*rho_4 + (7/6)*rho_7, where rho_4=4^q/3^p, rho_7=7^l/3^p.
# The DIP happens when rho_4 and rho_7 are both SMALL (powers just BELOW are far).
# Minimum over the fractional parts. Let me compute the true infimum.
print("Asymptotic ratio at a=3^p:  r ~ 1/2 + (4/3)*rho4 + (7/6)*rho7")
print("  rho4 = 4^q/3^p in (1/4,1], rho7 = 7^l/3^p in (1/7,1]  (frac parts)")
print()
# The infimum of r: minimize 1/2 + (4/3)rho4 + (7/6)rho7. rho4 in (1/4,1], rho7 in (1/7,1].
# Min when rho4->1/4+ and rho7->1/7+: r -> 1/2 + (4/3)(1/4) + (7/6)(1/7) = 1/2+1/3+1/6 = 1.0!
print("INFIMUM (rho4->1/4, rho7->1/7):  r -> 1/2 + 1/3 + 1/6 = %.4f = beta = 1" % (0.5+1/3+1/6))
print()
print(">>> THE RATIO'S INFIMUM IS EXACTLY beta = 1 (the boundary!). <<<")
print("The ratio S(a-)/a does NOT have a liminf bounded above 1 in general --")
print("it approaches 1 as the powers of 4 and 7 below 3^p both approach their")
print("MINIMUM relative position (just above the previous power). So whether the")
print("ratio stays STRICTLY > 1 at every atom is a QUANTITATIVE Diophantine question:")
print("can rho4 -> 1/4 AND rho7 -> 1/7 simultaneously, i.e. 4^q ~ (1/4)3^p AND")
print("7^l ~ (1/7)3^p, i.e. 4^{q+1} ~ 3^p AND 7^{l+1} ~ 3^p -- a TRIPLE coincidence")
print("3^p ~ 4^{q+1} ~ 7^{l+1}. MW/Baker bounds how close => ratio stays > 1 by a")
print("margin controlled by the three-log linear form. THIS IS WHERE L1 ENTERS L3.")
print()
# Verify: is the dip at 3^294 explained by rho4 near 1/4?
for p in [294, 193, 246, 92]:
    q=int(p*log3/log4); l=int(p*log3/log7)
    rho4=math.exp(q*log4-p*log3); rho7=math.exp(l*log7-p*log3)
    r_approx=0.5+(4/3)*rho4+(7/6)*rho7
    print("  3^%d: rho4=4^%d/3^p=%.4f, rho7=7^%d/3^p=%.4f -> r~%.4f" % (p,q,rho4,l,rho7,r_approx))
print()
print("So the ratio dip at 3^294 (r=1.0098) has rho4 NOT at 1/4 -- it's a MILD dip.")
print("The TRUE worst case requires rho4->1/4 AND rho7->1/7 together (triple coincidence),")
print("which MW says happens only finitely closely. KEY: is inf actually ATTAINED > 1?")
