import Lean4Lean.Experimental.E6.PatLeaf

open Lean in
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

#print axioms Lean4Lean.SExpr.T.pat_leaf_1a
#print axioms Lean4Lean.SExpr.T.pat_leaf_1a_restricted
#print axioms Lean4Lean.SExpr.T.pat_leaf_iota
#print axioms Lean4Lean.SExpr.T.pat_leaf_delta
-- the pinned lemma: exactly the two fact helpers contain sorry
#eval traceSorries [``Lean4Lean.SExpr.T.pat_leaf_1a]
-- the iota case given the two facts, the delta case, the restricted leaf: sorry-free
#eval traceSorries [``Lean4Lean.SExpr.T.pat_leaf_iota]
#eval traceSorries [``Lean4Lean.SExpr.T.pat_leaf_delta]
#eval traceSorries [``Lean4Lean.SExpr.T.pat_leaf_1a_restricted]

-- statement check (outside any section: no section variables in scope)
example : (type_of% @Lean4Lean.SExpr.LR.pat_leaf_1a) := @Lean4Lean.SExpr.T.pat_leaf_1a
#check @Lean4Lean.SExpr.T.gap_major_levels
#check @Lean4Lean.SExpr.T.gap_prop_root_sort
#check @Lean4Lean.SExpr.T.pat_leaf_1a_restricted
