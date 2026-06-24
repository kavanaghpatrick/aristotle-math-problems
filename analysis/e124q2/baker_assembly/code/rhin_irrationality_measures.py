"""
rhin: explicit irrationality measures for the cross-base ratios — literature verdict + transfer.

MISSION: find the best PUBLISHED explicit irrationality measure applicable to
log4/log3 = 2 log2/log3 and log7/log3, and the (3,4)/(3,7)/(4,7) spacings.

FINDINGS (all citations verified against the actual Zudilin survey arXiv:math/0404523
reference list, text-extracted via pdftotext; arxiv-API + Wikipedia cross-checked):

1. NO explicit finite irrationality measure of a RATIO of logs (log a/log b) exists in
   the literature. Confirmed across 6+ independent arxiv-API/Wikipedia/MathWorld searches.
   The Diophantine-approximation literature treats:
     (i)  single log VALUES: mu(log2) <= 3.8914 (Rukhadze 1987), mu(log3) (Rhin),
     (ii) Q-LINEAR FORMS in logs: mu(gamma) < 8.616 for gamma in Q log2 + Q log3
          (Rhin, via Zudilin Thm 3; Rhin "Approximants de Pade et mesures effectives
           d'irrationalite", Sem. Theorie des Nombres Paris 1985-86, Progr. Math. 71,
           Birkhauser 1987, 155-164),
     (iii) linear INDEPENDENCE measures of logs of rationals (Wu, Math. Comp. 72 (2002)
           901-911; also log5, log7).
   A RATIO log4/log3 is NONE of these — it is a quotient, not in Q log2 + Q log3, and
   not a single log value. So no off-the-shelf measure applies to it directly.

2. TRANSFER: log4/log3 = 2*(log2/log3), so mu(log4/log3) = mu(log2/log3) EXACTLY
   (rational scaling preserves the irrationality exponent). Hence IF a log2/log3 ratio
   measure existed it would transfer with zero loss — but none does (point 1).

3. The CORRECT object for |3^p - 4^q| is the LINEAR FORM |p log3 - 2q log2| (a Z-linear
   form in log2, log3). The cited explicit bounds are:
     - BEGL96's displayed MW two-log: |3^p-4^q|/3^p > exp(-762*(8+log p)^2)  [shape (log p)^2]
       (= Mignotte-Waldschmidt, Acta Arith. 53 (1989) Cor 10.1)
     - Generic Matveev 2000 (real, n=2, D=1): rel > exp(-1.17e9*(1+log p))    [shape (log p)^1]
   The MW (log p)^2 bound DOMINATES (is far larger) than the Matveev (log p)^1 bound at all
   relevant p, because Matveev's constant (~1e9) dwarfs MW's (~762).

4. The generic Baker/Matveev-derived irrationality measure of the RATIO (the fallback the
   mission asked to compute when no direct measure exists):
       |log4/log3 - p/q| > c * q^{-(1+C)},  C = c0*log3*log4 ~ 1.17e9 (Matveev),
   i.e. mu_generic(log4/log3) <= 1 + C — FINITE but astronomical. This is the honest
   "known measure," and it is what underlies matveev's crossover p* ~ 2.67e10. The sharper
   MW/LMN tuned constant gives p* ~ 2.94e5 (BEGL96's actual proof ceiling).

BOTTOM LINE for the board: mu_known for log4/log3 is NOT a small Salikhov-school constant.
It is the generic Baker-derived 1+C (astronomical), realized in practice as the MW (log p)^2
relative-spacing bound. This does NOT change FACE 1 (already discharged by MW/Matveev via
finiteness) and does NOT touch FACE 2 (the joint base-7 equidistribution, no citable bound).
It TIGHTENS the finite-check ceiling p* only insofar as the tuned LMN/Laurent constant beats
the generic Matveev one — exactly as gelfond's table anticipated.
"""
import mpmath as mp
mp.mp.dps = 60
L2, L3, L4, L7 = mp.log(2), mp.log(3), mp.log(4), mp.log(7)

# --- verify the transfer ---
g, th = L2/L3, L4/L3
assert abs(2*g - th) < mp.mpf(10)**-40, "transfer broken"
print("VERIFIED transfer: log4/log3 == 2*(log2/log3) =>",
      "mu(log4/log3) = mu(log2/log3) exactly.")

# --- which cited shape dominates, at every relevant scale ---
print("\nRelative-spacing lower bound log(rel) [nat log]; LARGER = sharper:")
print(f"{'p':>8} {'MW (logp)^2':>16} {'Matveev (logp)^1':>18} {'sharper':>10}")
for p in [5, 53, 665, 10**3, 10**5, 293885, 10**7, 10**10]:
    lp = float(mp.log(p))
    mw  = -762.0*(8+lp)**2                       # BEGL/MW-1989 displayed, relative (nat log)
    mat = -float(mp.mpf('1.1724e9'))*(1+lp)      # Matveev 2000 real n=2, relative (nat log)
    print(f"{p:>8} {mw:>16.1f} {mat:>18.3e} {('MW' if mw>mat else 'Matveev'):>10}")

# --- the generic measure exponent of the ratio ---
C = float(mp.mpf('1.1724e9'))
print(f"\nGeneric Matveev-derived irrationality exponent of log4/log3:  mu <= 1+C = {1+C:.4e}")
print("(FINITE, astronomical — NOT a small explicit Salikhov-type measure; none such exists.)")

# --- log7/log3 is an independent object (no transfer from the (3,4) ratio) ---
print(f"\nlog7/log3 = {float(L7/L3):.6f} = independent ratio; its spacing |3^p-7^l| needs its")
print("own two-log bound (Matveev (3,7): C*A1*A2 = 1.65e9, matveev board). Same conclusion:")
print("no direct ratio measure; generic Baker bound only.")
