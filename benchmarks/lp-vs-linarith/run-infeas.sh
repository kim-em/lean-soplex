#!/bin/bash
# Wall-clock harness for the infeasible-LP path. Runs each generated
# `InfeasGeomN*LP.lean` once under `lake env lean` and prints
# `infeas N=N lp <real>s`. Each run includes the ~3s import baseline.
#
# Usage: cd benchmarks/lp-vs-linarith && ./run-infeas.sh
set -e
cd "$(dirname "$0")"
echo "=== infeasible LP — $(date) ==="
for n in 8 16 32 64; do
  f="LPvsLinarith/InfeasGeom${n}LP.lean"
  r=$( { /usr/bin/time -p lake env lean "$f" ; } 2>&1 )
  real=$(echo "$r" | grep -E "^real" | awk '{print $2}')
  err=$(echo "$r" | grep -oE "error:.*" | head -1 | cut -c1-45)
  printf "infeas N=%-3s lp %6ss  %s\n" "$n" "$real" "$err"
done
echo "=== done $(date) ==="
