import Lean4Lean.Experimental.E1.TypedLR

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

#print axioms Lean4Lean.SExpr.T.LRS
#print axioms Lean4Lean.SExpr.T.LR
#print axioms Lean4Lean.SExpr.T.LR.DefEq.lift
#print axioms Lean4Lean.SExpr.T.LR.TyDefEq.lift
#eval traceSorries [``Lean4Lean.SExpr.T.LR.DefEq.lift, ``Lean4Lean.SExpr.T.LR.TyDefEq.lift, ``Lean4Lean.SExpr.T.LR, ``Lean4Lean.SExpr.T.LR.SubstWF.id]

-- extra (not required by the task): the other E1 targets that live in this part
#print axioms Lean4Lean.SExpr.T.LR0
#print axioms Lean4Lean.SExpr.T.LR.SubstWF.symm
#print axioms Lean4Lean.SExpr.T.LR.SubstWF.left
#print axioms Lean4Lean.SExpr.T.LogRelBase.TyDefEq.sort
