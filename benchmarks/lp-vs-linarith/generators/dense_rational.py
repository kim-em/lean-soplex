"""Dense LPs with rational (1/k) coefficients, to time lp vs linarith on non-integer data.
Usage: dense_rational.py <N> <lp|linarith> [seed]   (seed default = N)
"""
import random, sys
n = int(sys.argv[1]); tactic = sys.argv[2]
seed = int(sys.argv[3]) if len(sys.argv) > 3 else n
random.seed(seed)
vars_ = [f"x{i+1}" for i in range(n)]
# coeffs are c/d with small c,d; diagonal dominant
def coeff(): return f"({random.randint(1,3)}/{random.choice([2,3,5])} : Rat)"
A = [[coeff() for _ in range(n)] for _ in range(n)]
# rhs loose: each var ≤ 1 feasible region; goal sum ≤ n is loose-ish. Use big rhs.
rows = []
for i in range(n):
    lhs = " + ".join(f"{A[i][j]} * {vars_[j]}" for j in range(n))
    rows.append(f"(_h{i+1} : {lhs} ≤ {n})")
nn = " ".join(f"(_n{i+1} : 0 ≤ {v})" for i,v in enumerate(vars_))
goal = " + ".join(vars_)
print("import Soplex"); print("import Mathlib.Tactic.Linarith")
print("set_option maxHeartbeats 4000000")
print(f"example ({' '.join(vars_)} : Rat) {nn} {' '.join(rows)} : {goal} ≤ {n*n} := by {tactic}")
