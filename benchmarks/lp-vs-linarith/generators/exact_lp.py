"""Exact two-phase simplex over Fraction. Solves  min c·x  s.t. Ax = b, x ≥ 0.
Bland's rule for guaranteed termination. Returns (value, x) exact, or None."""
from fractions import Fraction as F

def simplex_eq(c, A, b):
    m = len(A); nv = len(c)
    A = [[F(v) for v in row] for row in A]; b = [F(v) for v in b]; c = [F(v) for v in c]
    for i in range(m):
        if b[i] < 0:
            A[i] = [-v for v in A[i]]; b[i] = -b[i]
    N = nv + m   # original + artificials
    T = [A[i] + [F(1) if j == i else F(0) for j in range(m)] + [b[i]] for i in range(m)]
    basis = [nv + i for i in range(m)]
    def run(cost, allowed):
        while True:
            cB = [cost[basis[i]] for i in range(m)]
            enter = -1
            for j in allowed:
                if j in basis: continue
                red = cost[j] - sum(cB[i] * T[i][j] for i in range(m))
                if red < 0:
                    enter = j; break
            if enter == -1: return True
            leave = -1; best = None
            for i in range(m):
                if T[i][enter] > 0:
                    r = T[i][-1] / T[i][enter]
                    if best is None or r < best or (r == best and basis[i] < basis[leave]):
                        best = r; leave = i
            if leave == -1: return None  # unbounded
            piv = T[leave][enter]
            T[leave] = [v / piv for v in T[leave]]
            for i in range(m):
                if i != leave and T[i][enter] != 0:
                    f = T[i][enter]
                    T[i] = [T[i][k] - f * T[leave][k] for k in range(N + 1)]
            basis[leave] = enter
    cost1 = [F(0)] * nv + [F(1)] * m
    if run(cost1, list(range(N))) is None: return None
    if sum(cost1[basis[i]] * T[i][-1] for i in range(m)) != 0: return None  # infeasible
    cost2 = list(c) + [F(0)] * m
    run(cost2, list(range(nv)))   # forbid artificials from re-entering
    x = [F(0)] * nv
    for i in range(m):
        if basis[i] < nv: x[basis[i]] = T[i][-1]
    val = sum(c[j] * x[j] for j in range(nv))
    return (val, x[:nv])

def hilbert_min(n):
    """min Σx s.t. H x ≥ b, x ≥ 0, scaled Hilbert. Returns exact (v*, x*)."""
    from math import gcd
    def lcm_list(ks):
        o = 1
        for k in ks: o = o * k // gcd(o, k)
        return o
    L = lcm_list(range(1, 2 * n))
    H = [[L // (i + j + 1) for j in range(n)] for i in range(n)]
    b = [sum(r) // 2 + 1 for r in H]
    # standard form: H x - s = b  →  vars [x(n), s(n)], A = [H | -I], min Σx
    A = [H[i] + [F(-1) if j == i else F(0) for j in range(n)] for i in range(n)]
    c = [F(1)] * n + [F(0)] * n
    res = simplex_eq(c, A, b)
    if res is None: return None
    val, xs = res
    return (val, xs[:n], H, b)

if __name__ == "__main__":
    import sys
    n = int(sys.argv[1])
    v, x, H, b = hilbert_min(n)
    # verify feasibility
    ok = all(sum(H[i][j]*x[j] for j in range(n)) >= b[i] for i in range(n)) and all(xj >= 0 for xj in x)
    print(f"n={n}  v*={v}  feasible={ok}  v*≈{float(v):.6f}")
