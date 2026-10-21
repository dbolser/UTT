import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Refuter check on claim C10 / the proposed `hasType (ctor c l k) indTy := k : type ∧ SpineTyped l k`.
Codes descend one level per field (`(f.app p).lift (n+1)`), so at level 1 no ctor shape with two
or more fields is typable at `indTy` (the second field's code is a lift of a level-0 shape, never a
Π).  In general (argued, not proved here): at level `n+1` at most `n+1` fields can be typed, and
constructor spines include the parameters (e.g. `Prod.mk α β a b` has 4).  No sorries. -/
namespace Lean4Lean.SExpr
variable [Params]

/-- `SpineTyped` exactly as in ClauseA.lean. -/
def SpineTyped : ∀ {n}, List (WShape n) → WShape (n+1) → Prop
  | _, [], _ => True
  | n, p :: ps, k => ∃ (a₁ : WShape n) (f : WShapeFun n),
      k = .forallE a₁ f ∧ p.HasType a₁ ∧ SpineTyped ps ((f.app p).lift (n+1))

theorem spineTyped_two_fields_level1 (p₁ p₂ : WShape 0) (ps : List (WShape 0)) (k : WShape 1) :
    ¬ SpineTyped (p₁ :: p₂ :: ps) k := by
  intro H
  simp only [SpineTyped] at H
  obtain ⟨a₁, f, -, -, a₂, f₂, h, -⟩ := H
  generalize f.app p₁ = s at h
  obtain ⟨⟨⟩ | ⟨r⟩, _⟩ := s
  · rw [show (⟨Shape0.bot, _⟩ : WShape 0) = WShape.bot from rfl, WShape.lift_bot] at h
    cases congrArg (·.1) h
  · rw [show (⟨Shape0.sort r, _⟩ : WShape 0) = WShape.sort r from rfl, WShape.lift_sort] at h
    cases congrArg (·.1) h

end Lean4Lean.SExpr
#print axioms Lean4Lean.SExpr.spineTyped_two_fields_level1
