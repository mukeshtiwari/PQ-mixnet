#!/bin/sh
# Builds the development and checks that the audited theorems use no axioms.
set -e
cd "$(dirname "$0")"
dune build @default 2>&1 | grep -B2 -A20 "^Error" && exit 1
B=_build/default/src
out=$(rocq compile -R $B/Algebra Algebra -R $B/Utility Utility -R $B/Probability Probability \
  -R $B/Crypto Crypto -R $B/Examples Examples -o /tmp/Audit.vo audit/Audit.v 2>&1) || true
echo "$out"
n=$(grep -c "^Print Assumptions" audit/Audit.v)
k=$(echo "$out" | grep -c "Closed under the global context")
[ "$n" = "$k" ] && echo "AUDIT OK ($k theorems, no axioms)" || { echo "AUDIT FAILED ($k of $n closed)"; exit 1; }
