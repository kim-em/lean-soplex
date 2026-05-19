import random
def gen_dense(n, seed):
    random.seed(seed)
    vars_ = [f"x{i+1}" for i in range(n)]
    A = [[random.randint(1, 3) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        A[i][i] = sum(A[i]) + random.randint(1, 3)
    b = [sum(A[i]) for i in range(n)]
    return vars_, A, b
def render(vars_, A, b, tactic):
    n = len(vars_)
    nn = " ".join(f"(_n{i+1} : 0 ≤ {v})" for i, v in enumerate(vars_))
    rows_h = " ".join(
        f"(_h{i+1} : " + " + ".join(f"{c} * {v}" for c, v in zip(row, vars_))
        + f" ≤ {rhs})" for i, (row, rhs) in enumerate(zip(A, b)))
    goal = " + ".join(vars_)
    return f"example ({' '.join(vars_)} : Rat) {nn} {rows_h} : {goal} ≤ {n} := by {tactic}"
import sys
# Usage: dense_integer.py <N> <lp|linarith> [seed]   (seed default = N)
n = int(sys.argv[1]); tactic = sys.argv[2]
seed = int(sys.argv[3]) if len(sys.argv) > 3 else n
vars_, A, b = gen_dense(n, seed=seed)
print("import Soplex")
print("import Mathlib.Tactic.Linarith")
print("set_option maxHeartbeats 4000000")
print(render(vars_, A, b, tactic))
