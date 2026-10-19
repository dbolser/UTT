import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Refuter (proof, lens clause), experiment 4.  With ClauseA's `hasType (ctor c l k) indTy :=
k : type ∧ SpineTyped l k`, a level-1 ctor shape (fields at level 0) can carry at most ONE field:
the descended code is a lift of a level-0 shape, never a `forallE`.  (In general at level `L`
at most `L` fields.)  Today `Shape.hasType (ctor _ _) indTy = true` unconditionally
(ShapeLogRel.lean 2496), so this is a real change to which shapes are typed.  No sorries. -/
namespace Lean4Lean.SExpr
variable [Params]

def SpineTyped : ∀ {n}, List (WShape n) → WShape (n+1) → Prop
  | _, [], _ => True
  | n, p :: ps, k => ∃ (a₁ : WShape n) (f : WShapeFun n),
      k = .forallE a₁ f ∧ p.HasType a₁ ∧ SpineTyped ps ((f.app p).lift (n+1))

theorem lift0_not_forallE (s : WShape 0) (a : WShape 0) (f : WShapeFun 0) :
    s.lift 1 ≠ .forallE a f := by
  obtain ⟨⟨⟩, _⟩ := s <;> intro h <;> cases congrArg (·.1) h

theorem depth_level1 (p₁ p₂ : WShape 0) (ps : List (WShape 0)) (k : WShape 1) :
    ¬ SpineTyped (p₁ :: p₂ :: ps) k := by
  intro H
  simp only [SpineTyped] at H
  obtain ⟨a₁, f, -, -, a₂, g, h, -⟩ := H
  exact lift0_not_forallE _ _ _ h

end Lean4Lean.SExpr
#print axioms Lean4Lean.SExpr.depth_level1
