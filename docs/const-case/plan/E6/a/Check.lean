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
#eval traceSorries [``Lean4Lean.SExpr.T.pat_leaf_1a]
example : (type_of% @Lean4Lean.SExpr.LR.pat_leaf_1a) := @Lean4Lean.SExpr.T.pat_leaf_1a
#check @Lean4Lean.SExpr.T.pat_leaf_1a

-- the gap, and the sorry-free cases
#print axioms Lean4Lean.SExpr.T.pat_leaf_delta
#print axioms Lean4Lean.SExpr.T.pat_leaf_iota
#eval traceSorries [``Lean4Lean.SExpr.T.pat_leaf_delta, ``Lean4Lean.SExpr.T.pat_leaf_iota]
#check @Lean4Lean.SExpr.T.pat_leaf_gap

-- every constant of the E6 modules
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods := #[`Lean4Lean.Experimental.E6.Helpers, `Lean4Lean.Experimental.E6.RhsCore,
    `Lean4Lean.Experimental.E6.Parts, `Lean4Lean.Experimental.E6.IotaData,
    `Lean4Lean.Experimental.E6.Iota, `Lean4Lean.Experimental.E6.PatLeaf]
  let idxs := mods.filterMap env.getModuleIdx?
  let mut names : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if let some i := env.getModuleIdxFor? n then
      if idxs.contains i && !n.isInternal then names := names.push n
  IO.println s!"E6 constants: {names.size}"
  liftCoreM <| traceSorries names.toList
