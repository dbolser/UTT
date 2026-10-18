import Lean4Lean.Experimental.SExpr

/-! A `Params` instance for the empty environment: shows the hypothesis package
`SExpr.Params` (SExpr.lean 24-80) is satisfiable.  No `variable [Params]` here;
this *is* the instance. -/

namespace Lean4Lean

@[instance_reducible] def emptyParams : Params := {
  env := .empty
  henv := .empty
  univs := 0
  Pat := fun _ _ => False
  classify := fun _ => none
  pat_simple := fun h => False.elim h
  pat_wf := fun h => False.elim h
  pat_uniq := fun h => False.elim h
  -- `VEnv.empty.defeqs df` unfolds to `False`
  extra_patV := fun h => False.elim h
  -- `classify c = some cl` is `none = some cl`
  ctor_syn := fun _ h => nomatch h
  ctor_sort := fun _ h => nomatch h
}

#print axioms emptyParams

/-- Sanity: with the instance in scope the theory's `Params`-dependent names resolve. -/
example : @Params.env emptyParams = VEnv.empty := rfl
example : @Params.univs emptyParams = 0 := rfl

end Lean4Lean
