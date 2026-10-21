import Lean4Lean.Experimental.ShapeLogRelAdequacy

/-! Lens 2 experiment: a concrete "compatible but incomparable" pair of parameter type-shapes
with a NON-trivial common typed element, i.e. a case where `HasDom` lowering does NOT collapse
the field shape to `⊥`, so the reconciliation gap bites.

Parameter `P : Type` with `P := (Type → Type) → Type`; field `x : P`, e.g. `x := fun _ => Type`.
`T₀`, `T₁` are two shapes of `P` (recursor side `q := T₀`, constructor side `q' := T₁`),
`y` is a shape of `x` typed at both. -/

namespace Lean4Lean.SExpr
variable [Params]

-- level-1 shapes of `Type → Type`
def b₀ : Shape 1 := ShapeS.forallE (.sort true) [(.sort true, .sort true)]
def b₁ : Shape 1 := ShapeS.forallE (.sort true) [(.bot, .bot)]
-- level-2 shapes of `(Type → Type) → Type`
def T₀ : Shape 2 := ShapeS.forallE b₀ [(.bot, .sort true)]
def T₁ : Shape 2 := ShapeS.forallE b₁ [(.bot, .sort true)]
-- a level-2 shape of `fun (_ : Type → Type) => Type`
def y : Shape 2 := ShapeS.lam [(.bot, .sort true)]

example : Shape.hasType y T₀ = true := by decide
example : Shape.hasType y T₁ = true := by decide
example : Shape.Compat T₀ T₁ = true := by decide
example : ¬ (T₀ ≤ T₁) := by decide
example : ¬ (T₁ ≤ T₀) := by decide
example : ¬ (y ≤ Shape.bot) := by decide
-- the join exists (compat) and is strictly above both
example : Shape.hasType y (T₀.join T₁) = true := by decide

/-! C's `TypedMeet` in its essential form ("a common lower bound of the two type shapes still
types `p`") HOLDS on this example: -/
def b₂ : Shape 1 := ShapeS.forallE (.sort true) [(.sort true, .bot)]
def T₂ : Shape 2 := ShapeS.forallE b₂ [(.bot, .sort true)]
example : T₂ ≤ T₀ := by decide
example : T₂ ≤ T₁ := by decide
example : Shape.hasType y T₂ = true := by decide
/- …but it is not what closes the gap: from `DefEq x x' P' y T₁` (producer) one gets
`DefEq x x' P' y T₂` by `mono_r_2`, and going back UP to `T₀` needs `mono_r_1` with
`TyDefEq P' P' T₀` — validity of the *constructor's* parameter term at the *recursor's* shape —
and the final `conv` to type `P` needs `TyDefEq P' P T₀`.  Neither is in the relation. -/

end Lean4Lean.SExpr
