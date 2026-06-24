"""
e944 floor worker (hunter) — optimized single-shard processor.

Reads graph6 lines on stdin (a geng res/mod shard), applies the FAST filter chain, and
prints any witness it finds (and summary stats on the last line as JSON).

Filter chain (cheap -> expensive, reject ASAP):
  1. NOT 3-colorable    (kills ~all 3-colorable graphs fast; the dominant cost)
  2. 4-colorable        (kills chi>=5)
  3. vertex-critical    (every G-v is 3-colorable)
  4. NO critical edge   (no edge e with G-e 3-colorable)  -> WITNESS

All chi tests via the same independent bitmask backtracker. SAT re-verification is done by the
parent launcher on any candidate (rare), so the worker stays pure-python fast.
"""
import sys


def parse_graph6(line):
    """Decode graph6 to (n, adj-bitmask-list). Self-contained (no networkx in hot loop)."""
    b = line.encode() if isinstance(line, str) else line
    data = [c - 63 for c in b]
    # number of vertices
    if data[0] <= 62:
        n = data[0]
        idx = 1
    else:
        # >=63 markers not expected for n<=62; handle simple case only
        n = data[0]
        idx = 1
    # bit vector of upper triangle
    bits = []
    for x in data[idx:]:
        for k in range(5, -1, -1):
            bits.append((x >> k) & 1)
    adj = [0] * n
    pos = 0
    for j in range(1, n):
        for i in range(j):
            if pos < len(bits) and bits[pos]:
                adj[i] |= (1 << j)
                adj[j] |= (1 << i)
            pos += 1
    return n, adj


def k_colorable(adj, n, k, order):
    """Fast k-colorability via bitmask backtracking with precomputed vertex order.
    color stored implicitly; returns True/False."""
    if k >= n:
        return True
    color = [-1] * n

    def bt(idx, max_used):
        if idx == n:
            return True
        v = order[idx]
        forbidden = 0
        nb = adj[v]
        while nb:
            low = nb & (-nb)
            u = low.bit_length() - 1
            cu = color[u]
            if cu >= 0:
                forbidden |= (1 << cu)
            nb ^= low
        limit = max_used + 1
        if limit > k - 1:
            limit = k - 1
        for c in range(limit + 1):
            if not (forbidden >> c) & 1:
                color[v] = c
                if bt(idx + 1, c if c > max_used else max_used):
                    return True
                color[v] = -1
        return False

    return bt(0, -1)


def deg_order(adj, n):
    return sorted(range(n), key=lambda v: -bin(adj[v]).count("1"))


def is_witness(n, adj):
    order = deg_order(adj, n)
    # 1. chi != 3  (must NOT be 3-colorable)
    if k_colorable(adj, n, 3, order):
        return False
    # 2. chi <= 4
    if not k_colorable(adj, n, 4, order):
        return False
    # chi == 4 confirmed. 3. vertex-critical: every G-v is 3-colorable
    for v in range(n):
        # build adj of G-v relabeled
        keep = [u for u in range(n) if u != v]
        remap = {u: i for i, u in enumerate(keep)}
        sub = [0] * (n - 1)
        for u in keep:
            nb = adj[u] & ~(1 << v)
            ru = remap[u]
            while nb:
                low = nb & (-nb)
                w = low.bit_length() - 1
                sub[ru] |= (1 << remap[w])
                nb ^= low
        so = deg_order(sub, n - 1)
        if not k_colorable(sub, n - 1, 3, so):
            return False  # v not critical
    # 4. no critical edge: every G-e stays NOT-3-colorable
    order_full = order
    for i in range(n):
        nb = adj[i]
        while nb:
            low = nb & (-nb)
            j = low.bit_length() - 1
            nb ^= low
            if i < j:
                adj[i] &= ~(1 << j)
                adj[j] &= ~(1 << i)
                three = k_colorable(adj, n, 3, order_full)
                adj[i] |= (1 << j)
                adj[j] |= (1 << i)
                if three:
                    return False  # edge (i,j) is critical
    return True


def main():
    total = 0
    vc4 = 0
    witnesses = []
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        total += 1
        n, adj = parse_graph6(line)
        order = deg_order(adj, n)
        # fast path: skip 3-colorable
        if k_colorable(adj, n, 3, order):
            continue
        if not k_colorable(adj, n, 4, order):
            continue
        # chi==4; check vertex-critical
        ok_vc = True
        for v in range(n):
            keep = [u for u in range(n) if u != v]
            remap = {u: i for i, u in enumerate(keep)}
            sub = [0] * (n - 1)
            for u in keep:
                nb = adj[u] & ~(1 << v)
                ru = remap[u]
                while nb:
                    low = nb & (-nb)
                    w = low.bit_length() - 1
                    sub[ru] |= (1 << remap[w])
                    nb ^= low
            so = deg_order(sub, n - 1)
            if not k_colorable(sub, n - 1, 3, so):
                ok_vc = False
                break
        if not ok_vc:
            continue
        vc4 += 1
        # no critical edge?
        no_crit = True
        for i in range(n):
            nb = adj[i]
            while nb:
                low = nb & (-nb)
                j = low.bit_length() - 1
                nb ^= low
                if i < j:
                    adj[i] &= ~(1 << j)
                    adj[j] &= ~(1 << i)
                    three = k_colorable(adj, n, 3, order)
                    adj[i] |= (1 << j)
                    adj[j] |= (1 << i)
                    if three:
                        no_crit = False
                        break
            if not no_crit:
                break
        if no_crit:
            witnesses.append(line)
            sys.stderr.write(f"WITNESS_CANDIDATE {line}\n")
            sys.stderr.flush()
    import json
    print(json.dumps({"total": total, "vc4": vc4, "witnesses": witnesses}))


if __name__ == "__main__":
    main()
