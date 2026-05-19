import sys
sys.path.insert(0, "/tmp")
from exact_lp import hilbert_min
from fractions import Fraction

n, tac = int(sys.argv[1]), sys.argv[2]
tac = "lp" if tac == "lp" else "linarith"
v, x, H, b = hilbert_min(n)
vs = [f"x{i+1}" for i in range(n)]
binders = " ".join(vs) + " : Rat"
hyps = [f"(_p{i+1} : 0 ≤ {vs[i]})" for i in range(n)]
for i in range(n):
    lhs = " + ".join(f"{H[i][j]} * {vs[j]}" for j in range(n))
    hyps.append(f"(_h{i+1} : {lhs} ≥ {b[i]})")
# tight goal: Σx ≥ v*  (v* exact rational)
vlit = f"({v.numerator} / {v.denominator} : Rat)"
print("import Soplex\nimport Mathlib.Tactic.Linarith\nset_option maxHeartbeats 4000000")
print(f"example ({binders}) {' '.join(hyps)} :\n    {' + '.join(vs)} ≥ {vlit} := by {tac}")
