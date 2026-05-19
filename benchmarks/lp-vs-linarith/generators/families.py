"""Generate hard LP families for lp-vs-linarith comparison.
Usage: gen_fam.py <family> <n> <lp|linarith>
"""
import sys, random
from fractions import Fraction

family, n, tac = sys.argv[1], int(sys.argv[2]), sys.argv[3]
tac = "lp" if tac == "lp" else "linarith"
H = ["import Soplex", "import Mathlib.Tactic.Linarith", "set_option maxHeartbeats 4000000"]

def emit(binders, hyps, goal):
    print("\n".join(H))
    print(f"example ({binders}) {' '.join(hyps)} :\n    {goal} := by {tac}")

if family == "geom":
    # x0 ≤ 1 ; 3 x_i ≤ 2 x_{i-1}.  Goal: x_n ≤ (2/3)^n.
    # Certificate multipliers are (1/3)(2/3)^{n-i} — denominators up to 3^{n+1}.
    vs = [f"x{i}" for i in range(n+1)]
    binders = " ".join(vs) + " : Rat"
    hyps = [f"(_p{i} : 0 ≤ {vs[i]})" for i in range(n+1)]
    hyps.append(f"(_h0 : {vs[0]} ≤ 1)")
    for i in range(1, n+1):
        hyps.append(f"(_h{i} : 3 * {vs[i]} ≤ 2 * {vs[i-1]})")
    goal = f"{vs[n]} ≤ ({2**n} / {3**n} : Rat)"
    emit(binders, hyps, goal)

elif family == "hilbert":
    # Scaled Hilbert matrix H_ij = L/(i+j+1), L = lcm(1..2n-1).
    # Constraints H x ≤ b with b tight at x = 1_n; goal Σx ≤ n.
    from math import gcd
    def lcm_list(ks):
        o = 1
        for k in ks: o = o*k//gcd(o,k)
        return o
    L = lcm_list(range(1, 2*n))
    A = [[L//(i+j+1) for j in range(n)] for i in range(n)]
    b = [sum(r) for r in A]
    vs = [f"x{i+1}" for i in range(n)]
    binders = " ".join(vs) + " : Rat"
    hyps = [f"(_p{i+1} : 0 ≤ {vs[i]})" for i in range(n)]
    for i in range(n):
        lhs = " + ".join(f"{A[i][j]} * {vs[j]}" for j in range(n))
        hyps.append(f"(_h{i+1} : {lhs} ≤ {b[i]})")
    goal = f"{' + '.join(vs)} ≤ {n}"
    emit(binders, hyps, goal)

elif family == "bigcoeff":
    # Dense LP with large pairwise-ish coprime coefficients (4-6 digit).
    random.seed(n)
    primes = [10007,10009,10037,10039,10061,10067,10069,10079,10091,10093,
              10099,10103,10111,10133,10139,10141,10151,10159,10163,10169,
              10177,10181,10193,10211,10223,10243,10247,10253,10259,10267,
              10271,10273,10289,10301,10303,10313,10321,10331,10333,10337]
    vs = [f"x{i+1}" for i in range(n)]
    binders = " ".join(vs) + " : Rat"
    hyps = [f"(_p{i+1} : 0 ≤ {vs[i]})" for i in range(n)]
    A = [[random.choice(primes) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        A[i][i] = sum(A[i]) + random.choice(primes)
    b = [sum(A[i]) for i in range(n)]
    for i in range(n):
        lhs = " + ".join(f"{A[i][j]} * {vs[j]}" for j in range(n))
        hyps.append(f"(_h{i+1} : {lhs} ≤ {b[i]})")
    goal = f"{' + '.join(vs)} ≤ {n}"
    emit(binders, hyps, goal)
