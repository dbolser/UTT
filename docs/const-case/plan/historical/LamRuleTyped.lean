import Lean4Lean.Experimental.ShapeLogRelAdequacy
-- historical: typechecked at 3c35f59, before extra_patV was restated on λ-telescopes (docs/const-case/PLAN.md D5, landed by R6); no longer compiles.
/-! Audit (circularity/measure), finding F1: the `extra` case for λ-wrapped rules under D6's
TYPED `whr` needs the typed beta step `(λA.R) a ≡ R[a] : T[a]` at the rule's declared codomain
`T`.  Against HEAD 3c35f59 (/tmp/utt-snap6).  No sorries. -/
namespace Lean4Lean.SExpr
variable [Params]

-- (1) `beta` needs the body typed at the codomain `B` it reports:
#check @IsDefEq.beta
-- (2) the only syntactic λ-inversion in the tree gives the body well-typed at SOME type:
#check @VEnv.HasType.lam_inv
-- (3) the SExpr Pi-injectivity that would identify that type with the declared codomain is a
--     corollary of `LR.adequacy` (so it reaches the const-case sorry):
#print axioms forallE_inv

/-- (4) the fix is cheap if the rule's OPEN typed equation is supplied (one binder shown):
the typed reduction of a λ-rule instance needs no inversion and no `⊢ Γ`. -/
theorem typed_beta_rule {Γ : List SExpr} {A L R T a : SExpr} {u}
    (hA : Γ ⊢ A : .sort u) (hLR : A::Γ ⊢ L ≡ R : T) (ha : Γ ⊢ a : A) :
    Γ ⊢ .app (.lam A L) a ≡ R.inst a : T.inst a :=
  .trans (.appDF (.lamDF hA hLR) ha) (.beta hLR.hasType.2 ha)

/-- (5) and the `N`-side step `(λA.R) a ≡ R[a]` from the same data. -/
theorem typed_beta_rhs {Γ : List SExpr} {A L R T a : SExpr}
    (hLR : A::Γ ⊢ L ≡ R : T) (ha : Γ ⊢ a : A) :
    Γ ⊢ .app (.lam A R) a ≡ R.inst a : T.inst a := .beta hLR.hasType.2 ha

#print axioms typed_beta_rule
#print axioms typed_beta_rhs
end Lean4Lean.SExpr
