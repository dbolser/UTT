#!/usr/bin/env bash
# Typecheck the const-case experiments against the current tree (not part of the build).
# Fuel, CtorClause, IHVacuous and Measure carry deliberate, commented `sorry`s, so only
# `error` counts as failure. Pass -q to skip the plan/ evidence files.
set -e
cd "$(dirname "$0")/../.."
check() {
  printf '%-22s' "$1"
  if lake env lean "$1" 2>&1 | grep -q '^.*error'; then echo FAIL; exit 1; else echo ok; fi
}
# CounterC and ClauseA, and the files in plan/historical/, were typechecked at 3c35f59 and stopped
# compiling when the typed logical relation landed (PLAN.md D6, R1+R2); they are kept for the record.
for f in Stuck Subst1 Fuel CtorClause Reconcile IHVacuous Measure Inert; do
  check "docs/const-case/$f.lean"
done
if [ "$1" != "-q" ] && [ -d docs/const-case/plan ]; then
  for f in docs/const-case/plan/*.lean; do check "$f"; done
fi
