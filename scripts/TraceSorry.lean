import Lean4Lean.Experimental.UniqueTyping
open Lean

/-- Walk the dependency graph from `roots`; report axioms reached and constants
whose own definition directly mentions `sorryAx`. -/
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

#eval traceSorries [``Lean4Lean.SExpr.IsDefEq'.uniq]
#eval traceSorries [``Lean4Lean.SExpr.HasTypeS.uniq]
#eval traceSorries [``Lean4Lean.SExpr.IsDefEq.toHasTypeS]
#eval traceSorries [``Lean4Lean.SExpr.forallE_inv, ``Lean4Lean.SExpr.sort_inv, ``Lean4Lean.SExpr.sort_forallE_inv]
#eval traceSorries [``Lean4Lean.SExpr.LR.adequacy]
#eval traceSorries [``Lean4Lean.SExpr.IsDefEq.mkS, ``Lean4Lean.VEnv.IsDefEq.of_mk_eq]
#eval traceSorries [``Lean4Lean.VEnv.IsDefEqU.sort_invS, ``Lean4Lean.VEnv.IsDefEqU.sort_forallE_invS,
  ``Lean4Lean.VEnv.IsDefEqU.forallE_invS]

-- Environment assumptions, translated from `Params.henv` / the VExpr-level `Params` fields.
#print axioms Lean4Lean.SExpr.Params.const_wf
#print axioms Lean4Lean.SExpr.Params.defeq_wf
#print axioms Lean4Lean.SExpr.Params.extra_pat
#eval traceSorries [``Lean4Lean.SExpr.Params.const_wf, ``Lean4Lean.SExpr.Params.defeq_wf,
  ``Lean4Lean.SExpr.Params.extra_pat]
