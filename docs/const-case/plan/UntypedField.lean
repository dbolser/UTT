import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Audit (circularity/measure), finding F2: constructor shapes are typed at `indTy` regardless of
their field shapes, so an iota pattern variable bound to a constructor field can carry an
UNTYPED shape.  `LR.SubstWF.cons` needs the pushed shape typed, and the stage-1a `FieldRel`
says nothing at such a field.  Against HEAD 3c35f59 (/tmp/utt-snap6).  No sorries. -/
namespace Lean4Lean.SExpr
variable [Params]

-- copy of the plan's FieldRel (synth/CtorClause1a.lean)
def FieldRel {Γ : List SExpr} : ∀ {n}, LogRel Γ n → SExpr → SExpr → SExpr → WShape n → Prop
  | 0, _, _, _, _, _ => True
  | _+1, IH, X, Y, T, p => ∀ q, q ≤ p → q.HasType .indTy → IH.DefEq X Y T q .indTy

/-- (1) a ctor shape with a `sort` field is typed at `indTy` (Shape.hasType, ShapeLogRel.lean:2494). -/
theorem ctor_sortField_typed (c : Name) :
    Shape.HasType (n := 2) (ShapeS.ctor c [Shape.sort true]) ShapeS.indTy := rfl

/-- (2) the field itself is not typed at `indTy`, nor at `⊥`. -/
theorem sortField_untyped :
    ¬ Shape.HasType (n := 1) (Shape.sort true) ShapeS.indTy ∧
    ¬ Shape.HasType (n := 1) (Shape.sort true) Shape.bot := by
  exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

/-- (3) the shape-level iota match binds the pattern variable to that raw field shape:
`rec (c x)` against the rargs `[ctor' c [sort]]`; the `inr none` path gets `sort`. -/
theorem matches_binds_untyped (rec c : Name) :
    LE_Interp.Matches (.app (.const rec) (.var (.const c))) (n := 2) rec
      [WShape.ctor' c [WShape.sort (n := 1) true]]
      (Sum.elim nofun (fun o => o.elim (WShape.sort (n := 1) true).T nofun)) :=
  .app .const (.var .const)

/-- (4) the plan's `FieldRel` is vacuous at the untyped field: only `q = ⊥` is below `sort` and
typed at `indTy`, so any `X Y T` are "related". -/
theorem fieldRel_sort_trivial {Γ : List SExpr} (X Y T : SExpr) :
    FieldRel (LR Γ (n := 1)) X Y T (WShape.sort true) := by
  intro q hq ht
  cases ht.unfold with
  | bot _ => exact (LR Γ).bot .indTy
  | ctor =>
    exfalso
    obtain ⟨_, _, he, _⟩ := WShape.ctor_le.1 hq
    cases congrArg (·.1) he

/-- (6) for a Prop-valued closed inductive field type (allowed by the plan's `indTy_closed`, whose
`ci.type = .sort u` permits `u = 0`), `indTy` is not a type shape at all, so "hA₁ the Const.indTy
leaf" (plan D4 step 1) is unavailable: only `⊥` types those fields. -/
theorem indTy_not_prop : ¬ Shape.HasType (n := 1) ShapeS.indTy (Shape.sort false) :=
  fun h => nomatch h

-- (5) `SubstWF.cons` demands a typed pushed shape (`x.HasType a`).
#check @LR.SubstWF.cons

#print axioms ctor_sortField_typed
#print axioms matches_binds_untyped
#print axioms fieldRel_sort_trivial
#print axioms indTy_not_prop
end Lean4Lean.SExpr
