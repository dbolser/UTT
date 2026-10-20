#!/usr/bin/env bash
# Typecheck the const-case experiments against the current tree (not part of the build).
# IHVacuous carries deliberate, commented `sorry`s, so only `error` counts as
# failure. Pass -q to skip the plan/ evidence files.
set -e
cd "$(dirname "$0")/../.."
check() {
  printf '%-22s' "$1"
  if lake env lean "$1" 2>&1 | grep -q '^.*error'; then echo FAIL; exit 1; else echo ok; fi
}
# CounterC, ClauseA and the files in plan/historical/ stopped compiling when the typed logical
# relation landed (PLAN.md D6, R1+R2); CtorClause and Subst1 when the constructor clause landed
# (D1/D2, R3); Measure and eight more plan/ files when IsDefEqStrong got its environment index
# (D4, R4); Fuel and plan/SelfType when Pattern.gen and the rank fields landed (D4/D3, R5).
# All were typechecked at 3c35f59 and are kept for the record.
for f in Stuck Reconcile IHVacuous Inert; do
  check "docs/const-case/$f.lean"
done
if [ "$1" != "-q" ] && [ -d docs/const-case/plan ]; then
  for f in docs/const-case/plan/*.lean; do check "$f"; done
fi
