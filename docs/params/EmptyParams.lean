import Lean4Lean.Experimental.SExpr

/-! A `Params` instance for the empty environment: shows the hypothesis package
`SExpr.Params` (SExpr.lean 24-80) is satisfiable.  No `variable [Params]` here;
this *is* the instance. -/

namespace Lean4Lean

/-- Every rank prefix of the empty environment is empty
(docs/const-case/plan/historical/EmptyBelow.lean). -/
theorem VEnv.empty_below (rank : Name → Nat) (k : Nat) : VEnv.empty.below rank k = .empty := by
  have hc : (VEnv.empty.below rank k).constants = VEnv.empty.constants := by
    funext c; simp only [VEnv.below]; split <;> rfl
  have hd : (VEnv.empty.below rank k).defeqs = VEnv.empty.defeqs := by
    funext df; simp only [VEnv.below]; exact propext ⟨fun h => h.1, fun h => h.elim⟩
  cases h : VEnv.empty.below rank k
  rw [h] at hc hd; cases hc; cases hd; rfl

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
  rank := fun _ => 0
  rank_ordered := fun k => by rw [VEnv.empty_below]; exact .empty
  -- `VEnv.empty.constants c = some ci` is `none = some ci`
  type_below := fun h => nomatch h
  -- `Pat` is `False`
  pat_rank := fun h => False.elim h
  pat_gen := fun h => False.elim h
  pat_typed := fun h => False.elim h
  pat_defeq := fun h => False.elim h
  pat_check := fun h => False.elim h
  indTy_closed := fun h => nomatch h
  ctor_fields_closed := fun _ h => nomatch h
}

#print axioms emptyParams

/-- Sanity: with the instance in scope the theory's `Params`-dependent names resolve. -/
example : @Params.env emptyParams = VEnv.empty := rfl
example : @Params.univs emptyParams = 0 := rfl

end Lean4Lean
