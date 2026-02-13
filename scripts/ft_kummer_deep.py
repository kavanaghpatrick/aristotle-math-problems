#!/usr/bin/env python3
"""Deep Kummer symbol analysis for FT p=3, q ≡ 71 mod 72."""
import sympy
from sympy.ntheory import primitive_root, discrete_log
from sympy.ntheory import n_order
from collections import Counter

def main():
    results = []
    for q in range(71, 200000, 72):
        if not sympy.isprime(q):
            continue
        A = q*q + q + 1
        if not sympy.isprime(A):
            continue
        
        # Direct FT check
        ft_val = pow(3, q, A)
        ft_holds = (ft_val == 1)
        
        # Kummer symbol = 3^{q+1} mod A
        kummer = pow(3, q+1, A)
        
        # Under assumption, kummer should = 3. Check:
        kummer_eq_3 = (kummer == 3 % A)
        
        # Order of 3 mod A
        order_3 = n_order(3, A)
        
        # Index: (A-1)/order_3
        index = (A-1) // order_3
        
        # (A-1)/q
        A1_over_q = (A-1) // q  # = q+1
        
        results.append({
            'q': q, 'A': A, 
            'ft_val': ft_val, 'ft_holds': ft_holds,
            'kummer': kummer, 'kummer_eq_3': kummer_eq_3,
            'order_3': order_3, 'index': index,
            'q_plus_1': q+1
        })

    print(f"Total eligible (q ≡ 71 mod 72, q prime, A=q²+q+1 prime): {len(results)}")
    print(f"FT violations (3^q ≡ 1 mod A): {sum(1 for r in results if r['ft_holds'])}")
    print()

    # Show first 20
    print(f"{'q':>8} {'A':>14} {'ord(3)':>10} {'index':>8} {'q+1':>8} {'3^q mod A':>12} {'kummer=3?':>10}")
    print("-" * 80)
    for r in results[:20]:
        print(f"{r['q']:>8} {r['A']:>14} {r['order_3']:>10} {r['index']:>8} {r['q_plus_1']:>8} {r['ft_val']:>12} {r['kummer_eq_3']:>10}")

    print()

    # Analyze index structure
    indices = [r['index'] for r in results]
    orders = [r['order_3'] for r in results]
    print("=== Index distribution ===")
    idx_counts = Counter(indices)
    for idx, count in sorted(idx_counts.items()):
        print(f"  index={idx}: {count} primes")

    print()

    # Check: is order always a multiple of 12?
    print(f"Orders divisible by 12: {all(o % 12 == 0 for o in orders)}")
    print(f"Orders divisible by 6: {all(o % 6 == 0 for o in orders)}")
    print(f"Orders divisible by 3: {all(o % 3 == 0 for o in orders)}")
    print(f"Min order: {min(orders)}")
    print(f"Max order: {max(orders)}")

    # For each q, compute order/q ratio  
    print()
    print("=== Order/q ratios (first 20) ===")
    for r in results[:20]:
        ratio = r['order_3'] / r['q']
        print(f"  q={r['q']}: ord={r['order_3']}, ord/q = {ratio:.4f}, ord/(q+1) = {r['order_3']/(r['q']+1):.4f}")

    # Key question: what is ord(3) mod A in terms of q?
    # A-1 = q(q+1). If ord(3) = q, then 3^q = 1 (FT violation).
    # Otherwise ord(3) divides q(q+1) but != q.
    print()
    q_divides = sum(1 for r in results if r['order_3'] % r['q'] == 0)
    qp1_divides = sum(1 for r in results if r['order_3'] % r['q_plus_1'] == 0)
    print(f"q divides order: {q_divides}/{len(results)} ({100*q_divides/len(results):.1f}%)")
    print(f"(q+1) divides order: {qp1_divides}/{len(results)} ({100*qp1_divides/len(results):.1f}%)")

    # Factorization of order
    print()
    print("=== Order factorizations (first 20) ===")
    for r in results[:20]:
        o = r['order_3']
        q = r['q']
        # What divides order from {q, q+1, 12, ...}
        divs = []
        if o % q == 0: divs.append("q")
        if o % (q+1) == 0: divs.append("q+1")
        if o % 12 == 0: divs.append("12")
        if o % (12*q) == 0: divs.append("12q")
        if o == q*(q+1): divs.append("q(q+1)=A-1")
        print(f"  q={q}: ord={o}, (A-1)/ord={r['index']}, divides: {', '.join(divs)}")

    # More detailed: what is order as a product of factors of q and q+1?
    print()
    print("=== Detailed order decomposition ===")
    print("Since A-1 = q(q+1), ord(3) must divide q(q+1).")
    print("Write ord(3) = q^a * d where d | (q+1), a in {0,1}")
    print()
    
    dq_vals = []
    dqp1_vals = []
    
    for r in results[:40]:
        o = r['order_3']
        q = r['q']
        qp1 = q + 1
        
        # Since q is prime, divisors of q are {1, q}
        # q+1 = 72k for some k (since q = 71 mod 72)
        if o % q == 0:
            d_q = q
            d_qp1 = o // q
        else:
            d_q = 1
            d_qp1 = o  # must divide q+1
        
        dq_vals.append(d_q)
        dqp1_vals.append(d_qp1)
        
        if r in results[:20]:
            # Verify d_qp1 divides q+1
            divides_check = (qp1 % d_qp1 == 0)
            cofactor = qp1 // d_qp1 if divides_check else -1
            print(f"  q={q}: ord={o} = q^{1 if d_q==q else 0} * {d_qp1}, d|(q+1)={'Y' if divides_check else 'N'}, (q+1)/d={cofactor}")

    print()
    print(f"Cases where q | ord(3): {sum(1 for d in dq_vals if d > 1)}/{len(dq_vals)}")
    print(f"Cases where q does not divide ord(3): {sum(1 for d in dq_vals if d == 1)}/{len(dq_vals)}")

    # When q does NOT divide order, what is the order?
    print()
    print("=== When q does not divide ord(3), order must divide q+1 ===")
    no_q_count = 0
    for r in results:
        o = r['order_3']
        q = r['q']
        if o % q != 0:
            no_q_count += 1
            qp1 = q + 1
            if no_q_count <= 20:
                print(f"  q={q}: ord={o}, q+1={qp1}, (q+1)/ord={qp1//o}")
    if no_q_count > 20:
        print(f"  ... ({no_q_count} total)")

    # Distribution of (q+1)/d_{q+1} when q | ord
    print()
    print("=== When q | ord(3), distribution of (q+1)/d ===")
    cofactors = []
    for r in results:
        o = r['order_3']
        q = r['q']
        if o % q == 0:
            d_qp1 = o // q
            cofactor = (q+1) // d_qp1
            cofactors.append(cofactor)
    
    cof_counts = Counter(cofactors)
    for c, count in sorted(cof_counts.items()):
        print(f"  (q+1)/d = {c}: {count} primes")
    
    # What fraction of A-1 does the order cover?
    print()
    print("=== Order as fraction of A-1 ===")
    fractions = Counter()
    for r in results:
        fractions[r['index']] += 1
    for idx, count in sorted(fractions.items()):
        pct = 100 * count / len(results)
        print(f"  (A-1)/ord = {idx}: {count} primes ({pct:.1f}%)")

    print()
    print("=== Critical check: is ord(3) ever exactly q? ===")
    exact_q = [r for r in results if r['order_3'] == r['q']]
    print(f"ord(3) = q exactly: {len(exact_q)} cases (these would be FT violations)")
    
    # Values of 3^{q+1} mod A
    print()
    print("=== Values of 3^{q+1} mod A (Kummer symbol) ===")
    print("These should never equal 3 (that would be FT violation)")
    print()
    
    for r in results[:30]:
        q = r['q']
        A = r['A']
        k = r['kummer']
        # k^q mod A should = 3^{q(q+1)} = 3^{A-1} = 1, so k is a q-th root of unity
        k_to_q = pow(k, q, A)
        print(f"  q={q}: 3^{{q+1}} mod A = {k}, (3^{{q+1}})^q mod A = {k_to_q}")

    print()
    print("=== Reciprocity angle: order of 3 modulo q ===")
    print()
    
    for r in results[:20]:
        q = r['q']
        A = r['A']
        # Order of 3 mod q
        ord_3_mod_q = n_order(3, q)
        # A mod q
        A_mod_q = A % q
        # A mod 3
        A_mod_3 = A % 3
        print(f"  q={q}: ord_q(3)={ord_3_mod_q}, A mod q = {A_mod_q}, A mod 3 = {A_mod_3}")

    # Cubic residue character
    print()
    print("=== Cubic residue character of q mod A ===")
    print("Since A = 1 mod 3, cubic character: q^{(A-1)/3} mod A")
    print()
    
    for r in results[:20]:
        q = r['q']
        A = r['A']
        cubic_q = pow(q, (A-1)//3, A)
        cubic_3 = pow(3, (A-1)//3, A)
        quad_3 = pow(3, (A-1)//2, A)
        print(f"  q={q}: q^{{(A-1)/3}} mod A = {cubic_q}, 3^{{(A-1)/3}} mod A = {cubic_3}, 3^{{(A-1)/2}} mod A = {quad_3}")

    print()
    cubic_residue_count = sum(1 for r in results if pow(3, (r['A']-1)//3, r['A']) == 1)
    print(f"3 is cubic residue mod A: {cubic_residue_count}/{len(results)}")
    
    quad_residue_count = sum(1 for r in results if pow(3, (r['A']-1)//2, r['A']) == 1)
    print(f"3 is quadratic residue mod A: {quad_residue_count}/{len(results)}")
    
    # Structure of q+1
    print()
    print("=== Structure of q+1 = (A-1)/q ===")
    for r in results[:10]:
        q = r['q']
        qp1 = q + 1
        fac = sympy.factorint(qp1)
        print(f"  q={q}: q+1={qp1} = {fac}")
    
    # (q+1)-part of ord(3)
    print()
    print("=== (q+1)-part of ord(3) ===")
    print("Writing ord(3) = q^a * d where d | (q+1), a in {0,1}:")
    print()
    
    d_vals = []
    for r in results[:30]:
        o = r['order_3']
        q = r['q']
        qp1 = q + 1
        
        if o % q == 0:
            a = 1
            d = o // q
        else:
            a = 0
            d = o
        
        d_vals.append(d)
        ratio = qp1 / d
        print(f"  q={q}: ord = q^{a} * {d}, d/(q+1) = {d/qp1:.6f}, (q+1)/d = {ratio:.1f}")
    
    print()
    print("=== Summary statistics ===")
    print(f"Total eligible pairs (q,A): {len(results)}")
    print(f"Range: q from {results[0]['q']} to {results[-1]['q']}")
    print(f"FT violations found: {sum(1 for r in results if r['ft_holds'])}")
    print(f"All kummer != 3: {all(not r['kummer_eq_3'] for r in results)}")
    print()
    
    print("=== What a reciprocity proof needs ===")
    print("We need: ord_A(3) != q for all eligible (q, A).")
    print("Equivalently: 3^q not= 1 mod A = q^2+q+1.")
    print("Equivalently: 3^{q+1} not= 3 mod A.")
    print()
    print("Via q-th power reciprocity in Q(zeta_q):")
    print("  (3/A)_q * correction = (A/3)_q")  
    print("where correction involves q-th power residue symbols of units.")
    print()
    print("Since A = 1 mod q, the prime A splits completely in Q(zeta_q).")
    print("The symbol (3/A)_q can be computed via any prime P above A.")
    print("If 3^q = 1 mod A, then (3/A)_q = 3^{(A-1)/q} = 3^{q+1} = 3 mod A")
    print("(under the false assumption). But reciprocity gives a different formula")
    print("that might demonstrably != 3.")
    print()
    
    print("=== Verification: 3^{q+1} = 3 iff 3^q = 1 ===")
    mismatches = 0
    for r in results:
        q = r['q']
        A = r['A']
        check1 = (pow(3, q, A) == 1)
        check2 = (pow(3, q+1, A) == 3)
        if check1 != check2:
            mismatches += 1
            print(f"  MISMATCH at q={q}!")
    print(f"Mismatches: {mismatches} (should be 0)")


if __name__ == "__main__":
    main()
