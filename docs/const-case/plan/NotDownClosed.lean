import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Lens 1, experiment 3: `HasType` is not downward closed in the element shape.
`lam g ≤ lam g'` and `lam g' : Π (Π ⊥ ⊥), sort`, but `lam g` is not.  Hence for design B's naive
clause `∃ t, p : t ∧ DefEq x y T p t`, `mono_l` (from `ctor c [lam g']` to `ctor c [lam g]`) cannot
reuse the witness `t`, and no other witness need exist.  With the code in the shape (`ClauseA`),
`hasType (ctor c l k) indTy` forces `p : a₁` on *both* sides, so this never arises. -/
namespace Lean4Lean.SExpr
variable [Params]

def gS  : Shape 2 := .lam [(.bot, .bot), (.sort true, .sort true)]
def gS' : Shape 2 := .lam [(.bot, .sort true)]
def aS  : Shape 2 := .forallE (.forallE .bot [(.bot, .bot)]) [(.bot, .sort true)]

theorem gS_le : gS ≤ gS' := rfl
theorem gS'_typed : Shape.HasType gS' aS := rfl
theorem gS_untyped : ¬ Shape.HasType gS aS := fun h => by cases h

end Lean4Lean.SExpr
