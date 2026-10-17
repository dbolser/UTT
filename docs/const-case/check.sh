#!/usr/bin/env bash
# Typecheck the const-case experiments against the current tree (not part of the build).
set -e
cd "$(dirname "$0")/../.."
for f in Stuck Subst1 Fuel CtorClause; do
  printf '%-12s' "$f"
  if lake env lean "docs/const-case/$f.lean" 2>&1 | grep -q '^.*error'; then echo FAIL; exit 1; else echo ok; fi
done
