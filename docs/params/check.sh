#!/usr/bin/env bash
# Typecheck the Params-instance experiments against the current tree (not part of the build).
# Each file must have no `error` and exactly its expected number of `declaration uses sorry`
# warnings: EmptyParams 0, NatParams 1 (the marked `ctor_sort_nat`). Then `traceSorries`
# rooted at `natParams` (NatParams.lean with the tracer of scripts/TraceSorry.lean appended,
# in a scratch file, since docs files are not importable) must find exactly one constant
# directly containing `sorry`: `ctor_sort_nat`. Schema.lean is historical (typechecked at
# 3c35f59, before R6 restated extra_patV on λ-telescopes) and is not checked.
set -e
cd "$(dirname "$0")/../.."
check() { # file, expected number of sorry warnings
  printf '%-12s' "$1"
  st=0; out=$(lake env lean "docs/params/$1.lean" 2>&1) || st=$?
  if [ "$st" != 0 ] || printf '%s\n' "$out" | grep -q 'error'; then
    echo FAIL; printf '%s\n' "$out" | grep -m20 'error' || printf '%s\n' "$out" | tail -5; exit 1
  fi
  n=$(printf '%s\n' "$out" | grep -c 'declaration uses .sorry.' || true)
  if [ "$n" != "$2" ]; then echo "FAIL ($n sorry warnings, expected $2)"; exit 1; fi
  echo "ok ($n sorry)"
}
check EmptyParams 0
check NatParams 1

tmp=$(mktemp --suffix=.lean)
trap 'rm -f "$tmp"' EXIT
{ cat docs/params/NatParams.lean; cat <<'LEAN'

open Lean in
/-- Walk the dependency graph from `roots`; report axioms reached and constants
whose own definition directly mentions `sorryAx` (scripts/TraceSorry.lean's). -/
def traceSorries (roots : List Name) : CoreM Unit := do
  let env ← getEnv
  let mut visited : NameSet := {}
  let mut stack := roots
  let mut direct : Array Name := #[]
  let mut axioms : Array Name := #[]
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if visited.contains n then continue
    visited := visited.insert n
    match env.find? n with
    | none => continue
    | some ci =>
      let used := ci.getUsedConstantsAsSet
      if let .axiomInfo _ := ci then axioms := axioms.push n
      if used.contains ``sorryAx then direct := direct.push n
      for c in used.toList do
        if !visited.contains c then stack := c :: stack
  IO.println s!"== roots: {roots}"
  IO.println s!"axioms reached ({axioms.size}):"
  for a in axioms.qsort (·.toString < ·.toString) do IO.println s!"  {a}"
  IO.println s!"constants directly containing sorry ({direct.size}):"
  for d in direct.qsort (·.toString < ·.toString) do IO.println s!"  {d}"

#eval traceSorries [``Lean4Lean.NatEnv.natParams]
LEAN
} > "$tmp"
printf '%-12s' trace
st=0; out=$(lake env lean "$tmp" 2>&1) || st=$?
if [ "$st" != 0 ] || printf '%s\n' "$out" | grep -q 'error'; then
  echo FAIL; printf '%s\n' "$out" | grep -m20 'error' || printf '%s\n' "$out" | tail -5; exit 1
fi
block=$(printf '%s\n' "$out" | sed -n '/^constants directly containing sorry/,$p')
expected=$(printf '%s\n' 'constants directly containing sorry (1):' '  Lean4Lean.NatEnv.ctor_sort_nat')
if [ "$block" != "$expected" ]; then echo FAIL; printf '%s\n' "$block"; exit 1; fi
echo "ok (natParams: only ctor_sort_nat contains sorry)"
