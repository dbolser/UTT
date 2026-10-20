import Lean4Lean.Experimental.E5.LamAdequacy
open Lean in
/-- which of `targets` are reachable from `root`, with one parent chain each -/
def reach (root : Name) (targets : List Name) : CoreM Unit := do
  let env ← getEnv
  let mut parent : Std.HashMap Name Name := {}
  let mut visited : NameSet := {}
  let mut stack := [root]
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if visited.contains n then continue
    visited := visited.insert n
    if let some ci := env.find? n then
      for c in ci.getUsedConstantsAsSet.toList do
        if !visited.contains c then
          if !parent.contains c then parent := parent.insert c n
          stack := c :: stack
  for t in targets do
    if visited.contains t then
      let mut chain := [t]
      let mut cur := t
      for _ in [0:40] do
        match parent.get? cur with
        | some p => chain := p :: chain; cur := p
        | none => break
      IO.println s!"{root} reaches {t}: {chain.reverse.take 8}"
    else IO.println s!"{root} does NOT reach {t}"
#eval reach ``Lean4Lean.SExpr.T.LR.adequacy [``Lean4Lean.Params.extra_patV, ``Lean4Lean.SExpr.Params.extra_pat]
#eval reach ``Lean4Lean.SExpr.T.LR.lamRule [``Lean4Lean.Params.extra_patV, ``Lean4Lean.SExpr.Params.extra_pat]
#eval reach ``Lean4Lean.SExpr.T.strongSoundS_extra_lam [``Lean4Lean.Params.extra_patV, ``Lean4Lean.SExpr.Params.extra_pat]
#eval reach ``Lean4Lean.SExpr.T.extra_pat_lam [``Lean4Lean.Params.extra_patV, ``Lean4Lean.SExpr.Params.extra_pat]
