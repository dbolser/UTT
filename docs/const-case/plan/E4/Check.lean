import Lean4Lean.Experimental.E4.NatParamsA

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

#eval traceSorries [``Lean4Lean.NatEnvA.natParamsR]
#print axioms Lean4Lean.NatEnvA.natParamsR
#print Lean4Lean.ParamsR

-- extra roots: every constant of the module's namespace NatEnvA, and the λ-rule typings
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let some idx := mods.idxOf? `Lean4Lean.Experimental.E4.NatParamsA | throwError "no module"
  let names := env.constants.map₁.toList.filterMap fun (n, _) =>
    if env.getModuleIdxFor? n == some idx && !n.isInternal then some n else none
  IO.println s!"module constants (roots of the next trace): {names.length}"
  let mut visited : NameSet := {}
  let mut stack := names
  let mut direct : Array Name := #[]
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if visited.contains n then continue
    visited := visited.insert n
    match env.find? n with
    | none => continue
    | some ci =>
      let used := ci.getUsedConstantsAsSet
      if used.contains ``sorryAx then direct := direct.push n
      for c in used.toList do
        if !visited.contains c then stack := c :: stack
  IO.println s!"constants directly containing sorry, all module roots ({direct.size}):"
  for d in direct.qsort (·.toString < ·.toString) do IO.println s!"  {d}"
#print axioms Lean4Lean.NatEnvA.iotaSuccLam_wf
#print axioms Lean4Lean.NatEnvA.iotaZeroLam_wf
#print axioms Lean4Lean.NatEnvA.envA_ordered
#print axioms Lean4Lean.NatEnvA.extra_patV
#print axioms Lean4Lean.NatEnvA.pat_typed
#print axioms Lean4Lean.NatEnvA.pat_defeq
