#!/usr/bin/env bash
# Typecheck the Params-instance experiments against the current tree (not part of the build).
# NatParams.lean has three deliberate, marked `sorry`s, so only `error` counts as failure.
set -e
cd "$(dirname "$0")/../.."
for f in EmptyParams NatParams Schema; do
  printf '%-12s' "$f"
  if lake env lean "docs/params/$f.lean" 2>&1 | grep -q '^.*error'; then echo FAIL; exit 1; else echo ok; fi
done
