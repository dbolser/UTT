import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Refuter scratch (patleaf lens, proof-theoretic).
(1) `HasType` is not downward closed in the element shape: concrete level-2 shapes
    `m ≤ m'`, `m'.HasType a`, `¬ m.HasType a`.
(2) `SubstWF.cons` only pushes *typed* shapes (`x.HasType a`), and `LE_Interp.bvar` needs
    `m_e ≤ ρ i`; so a self-occurrence recorded at an untyped `m_e` cannot be pushed as `m_e`.
No sorries. -/
namespace Lean4Lean.SExpr
variable [Params]
set_option linter.unusedSectionVars false

/-- an untyped (as a type-element) level-1 shape: a lambda shape `lam [(bot, Type)]`. -/
def xU : Shape 1 := ShapeS.lam [(Shape0.bot, Shape0.sort true)]
/-- the type shape `Π (X : Type), Type` at level 2. -/
def aPi : Shape 2 := ShapeS.forallE (ShapeS.sort true) [(ShapeS.bot, ShapeS.sort true)]
/-- typed element: the constant function returning `indTy`. -/
def mTop : Shape 2 := ShapeS.lam [(ShapeS.bot, ShapeS.indTy)]
/-- below it, with an extra graph entry at the untyped domain point `xU`. -/
def mLow : Shape 2 := ShapeS.lam [(ShapeS.bot, ShapeS.bot), (xU, ShapeS.indTy)]

theorem mLow_le : Shape.ble mLow mTop = true := by decide
theorem mTop_typed : Shape.hasType mTop aPi = true := by decide
theorem mLow_untyped : Shape.hasType mLow aPi = false := by decide

example : mLow ≤ mTop ∧ Shape.HasType mTop aPi ∧ ¬ Shape.HasType mLow aPi :=
  ⟨mLow_le, mTop_typed, by simp [Shape.HasType, mLow_untyped]⟩

/-- The same at the `WShape` level (well-formedness by `decide`). -/
def wTop : WShape 2 := ⟨mTop, by simp +decide [mTop, Shape.WF, ShapeFun.WF, Shape.bot]⟩
def wLow : WShape 2 := ⟨mLow, by simp +decide [mLow, xU, Shape.WF, ShapeFun.WF, Shape.bot]⟩
def wPi : WShape 2 := ⟨aPi, by simp +decide [aPi, Shape.WF, ShapeFun.WF, Shape.bot]⟩
theorem wshape_not_down : wLow ≤ wTop ∧ wTop.HasType wPi ∧ ¬ wLow.HasType wPi :=
  ⟨mLow_le, mTop_typed, by simp [WShape.HasType, Shape.HasType, wLow, wPi, mLow_untyped]⟩

/-- Every typed shape above `wLow` is strictly above it: so if a self-occurrence is recorded at
`m_e := wLow`, any shape `x` that `SubstWF.cons` may push (typed, `m_e ≤ x`) is itself a typed
shape `≤ x` that is NOT `≤ m_e`; the analyst's `ihBlock` (relatedness at typed `m ≤ m_e` only)
cannot supply `Subst1` at `(x, a)`. -/
theorem typed_above_not_below (x : WShape 2) (h1 : wLow ≤ x) (h2 : x.HasType wPi) : ¬ x ≤ wLow :=
  fun h3 => wshape_not_down.2.2 (WShape.HasType.mono_l h3 h1 h2)

/-- `LE_Interp` is downward closed, so any interpretation at the typed `wTop` yields one at the
untyped `wLow` (in particular as an `RHS.const`/`R` leaf of a model derivation). -/
example {ρ M} (H : LE_Interp ρ wTop.T M) : LE_Interp ρ wLow.T M := H.mono wshape_not_down.1.T

-- (2) the only constructors that extend a valuation require a typed pushed shape:
#check @LR.SubstWF.cons

-- and `HasType` is only invariant under `≤`-equivalence, not under `≤`:
#check @WShape.HasType.mono_l
/-- (3) The fix is available: every non-bot `const` node of a model derivation carries a TYPED
upper bound `m'` of its index (premises `m ≤ m'`, `m'.HasType a` of `LE_Interp.const`), so the local
motive can be stated artifact-style (`adequacy_Y`: `∃ m' ≥ m typed, Adequate at m'`) and the IH at
a self-occurrence then supplies exactly what `SubstWF.cons` pushes. -/
theorem LE_Interp.const_typed_ub {ρ mT c ls} (H : LE_Interp ρ mT (.const c ls)) :
    (∃ n, mT = (WShape.bot (n := n)).T) ∨
    ∃ ci m' a, Params.env.constants c = some ci ∧ mT ≤ m' ∧ m'.HasType a ∧
      LE_Interp ρ a (SExpr.mkInst ls ci.type) := by
  cases H with
  | bot => exact .inl ⟨_, rfl⟩
  | const h1 _ h3 h4 h5 _ _ => exact .inr ⟨_, _, _, h1, h3, h4, h5⟩
end Lean4Lean.SExpr
#print axioms Lean4Lean.SExpr.LE_Interp.const_typed_ub
#print axioms Lean4Lean.SExpr.typed_above_not_below
