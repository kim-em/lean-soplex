#!/bin/bash
# Wall-clock benchmark harness for `lp` vs `linarith`. Runs each test file
# in isolation under `lake env lean`, with `/usr/bin/time -p`, and prints
# one row per (problem, tactic). Each run includes the ~3s import baseline.
#
# Usage: cd benchmarks/lp-vs-linarith && ./run.sh
set -e
cd "$(dirname "$0")"
echo "=== lp vs linarith — $(date) ==="
echo "## integer dense (N = number of variables = number of constraints + n nonneg)"
for n in 10 20 30 40 50 60 80 100; do
  for t in LP LA; do
    f="LPvsLinarith/IntN${n}${t}.lean"
    r=$( { /usr/bin/time -p lake env lean "$f" ; } 2>&1 )
    real=$(echo "$r" | grep -E "^real" | awk '{print $2}')
    err=$(echo "$r" | grep -oE "error:.*" | head -1 | cut -c1-45)
    tac=$([ "$t" = "LP" ] && echo "lp     " || echo "linarith")
    printf "int N=%-3s %s %6ss  %s\n" "$n" "$tac" "$real" "$err"
  done
done
echo "## rational dense"
for n in 8 16 24 32 40 48 56 64 72 80; do
  for t in LP LA; do
    f="LPvsLinarith/RatN${n}${t}.lean"
    r=$( { /usr/bin/time -p lake env lean "$f" ; } 2>&1 )
    real=$(echo "$r" | grep -E "^real" | awk '{print $2}')
    err=$(echo "$r" | grep -oE "error:.*" | head -1 | cut -c1-45)
    tac=$([ "$t" = "LP" ] && echo "lp     " || echo "linarith")
    printf "rat N=%-3s %s %6ss  %s\n" "$n" "$tac" "$real" "$err"
  done
done
echo "=== done $(date) ==="
