import Lean4Lean.Experimental.E2.CtorLR
import Lean4Lean.Experimental.E2.CtorAdequacy

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
#print axioms Lean4Lean.SExpr.T.LR.Adequate.mono_r

#eval traceSorries [``Lean4Lean.SExpr.T.LR.DefEq.lift, ``Lean4Lean.SExpr.T.LR.TyDefEq.lift,
  ``Lean4Lean.SExpr.T.LR, ``Lean4Lean.SExpr.T.LR.SubstWF.id]
#eval traceSorries [``Lean4Lean.SExpr.T.LR.adequacy]

-- the LogRel field signatures (unchanged from the repo's D6 `LogRel`)
#check @Lean4Lean.SExpr.T.LogRel.sort_iff
#check @Lean4Lean.SExpr.T.LogRel.sort_iff_ty
#check @Lean4Lean.SExpr.T.LogRel.whr
#check @Lean4Lean.SExpr.T.LogRel.whr_ty
#check @Lean4Lean.SExpr.T.LogRel.bot
#check @Lean4Lean.SExpr.T.LogRel.conv
#check @Lean4Lean.SExpr.T.LogRel.mono_l
