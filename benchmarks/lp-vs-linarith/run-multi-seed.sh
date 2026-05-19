#!/bin/bash
# Multi-seed wall-clock benchmark. For each (family, N, tactic) and each
# seed in 1..5, generate a one-example Lean file under LPvsLinarith/Seeded/
# and run it with `/usr/bin/time -p`. Print one row per run; a Python
# summarize step at the end reports mean / min / max per (family, N, tactic).
#
# Individual runs are expected to fail at large N — `linarith` hits
# `maximum recursion depth` on the dense integer family — so the per-run
# invocation below is `|| true`: a failed run is recorded (with its error)
# and the sweep continues. The summary step reports errored runs
# separately. `set -e` still guards genuine setup errors (cd, mkdir,
# generator failures).
#
# The Seeded/ dir is gitignored — multi-seed runs are not committed.
set -e
cd "$(dirname "$0")"
mkdir -p LPvsLinarith/Seeded
LOG=/tmp/lp-vs-linarith-multiseed.log
echo "=== multi-seed lp vs linarith — $(date) ===" | tee "$LOG"
INT_SIZES="10 20 30 40 50 60 80 100"
RAT_SIZES="8 16 24 32 40 48 56 64 72 80"
SEEDS="1 2 3 4 5"
for seed in $SEEDS; do
  for n in $INT_SIZES; do
    for t in lp linarith; do
      f="LPvsLinarith/Seeded/IntN${n}_${t}_s${seed}.lean"
      python3 generators/dense_integer.py $n $t $seed > "$f"
      r=$( { /usr/bin/time -p lake env lean "$f" ; } 2>&1 ) || true
      real=$(echo "$r" | grep -E "^real" | awk '{print $2}')
      err=$(echo "$r" | grep -oE "error:.*" | head -1 | cut -c1-40)
      tac=$([ "$t" = "lp" ] && echo "lp     " || echo "linarith")
      printf "int N=%-3s seed=%s %s %6ss  %s\n" "$n" "$seed" "$tac" "$real" "$err" | tee -a "$LOG"
    done
  done
  for n in $RAT_SIZES; do
    for t in lp linarith; do
      f="LPvsLinarith/Seeded/RatN${n}_${t}_s${seed}.lean"
      python3 generators/dense_rational.py $n $t $seed > "$f"
      r=$( { /usr/bin/time -p lake env lean "$f" ; } 2>&1 ) || true
      real=$(echo "$r" | grep -E "^real" | awk '{print $2}')
      err=$(echo "$r" | grep -oE "error:.*" | head -1 | cut -c1-40)
      tac=$([ "$t" = "lp" ] && echo "lp     " || echo "linarith")
      printf "rat N=%-3s seed=%s %s %6ss  %s\n" "$n" "$seed" "$tac" "$real" "$err" | tee -a "$LOG"
    done
  done
done
echo "=== done $(date) ===" | tee -a "$LOG"
# Summarize: mean / min / max per (family, N, tactic).
python3 - "$LOG" <<'PY'
import sys, re, statistics
runs = {}
errs = {}
for line in open(sys.argv[1]):
    m = re.match(r"(int|rat) N=(\d+)\s+seed=(\d+)\s+(lp|linarith)\s+([\d.]+)s\s+(.*)$", line)
    if not m: continue
    fam, n, _, tac, t, errtail = m.groups()
    key = (fam, int(n), tac.strip())
    if errtail.startswith("error:"):
        errs.setdefault(key, []).append(errtail.strip())
        continue
    runs.setdefault(key, []).append(float(t))
print("\nSummary (mean / min / max over successful seeds):")
print(f"{'family':6s} {'N':>4s} {'tactic':10s} {'n':>3s} {'mean':>7s} {'min':>7s} {'max':>7s}  notes")
def order(k):
    fam,n,t = k; return (fam, n, t)
for k in sorted(runs.keys(), key=order):
    fam,n,t = k
    ts = runs[k]
    e = len(errs.get(k, []))
    extra = f" ({e} err)" if e else ""
    print(f"{fam:6s} {n:>4d} {t:10s} {len(ts):>3d} {statistics.mean(ts):>6.2f}s {min(ts):>6.2f}s {max(ts):>6.2f}s {extra}")
for k in sorted(errs.keys(), key=order):
    if k in runs: continue
    fam,n,t = k
    print(f"{fam:6s} {n:>4d} {t:10s}  all {len(errs[k])} runs errored: {errs[k][0]}")
PY
