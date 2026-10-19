import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Completeness audit 2. `LR.pat_leaf_1a` (PLAN D4, amend-1/PatLeafStmt.lean) takes
`(g : PatGen)` with NO hypothesis tying `g` to `p`, `r`, `c`, `Ts`. Its `hty`/`hdef`
hypotheses are then satisfiable by a junk `g` for EVERY `p r c ci rank`, so the statement
carries no RHS typing (the defect `PatTypedDegenerate.lean` found for existential witnesses).
Sorry-free. -/
namespace Lean4Lean

def VExpr.OnConsts (P : Name → Prop) : VExpr → Prop
  | .bvar _ | .sort _ => True
  | .const c _ => P c
  | .app f a | .lam f a | .forallE f a => f.OnConsts P ∧ a.OnConsts P
def VDefEq.OnConsts (P : Name → Prop) (df : VDefEq) : Prop :=
  df.lhs.OnConsts P ∧ df.rhs.OnConsts P ∧ df.type.OnConsts P
def VEnv.below (env : VEnv) (rank : Name → Nat) (k : Nat) : VEnv where
  constants c := if rank c < k then env.constants c else none
  defeqs df := env.defeqs df ∧ df.OnConsts (rank · < k)

structure PatGen where
  ctx : List VExpr
  self : List VExpr
  lhs : VExpr
  rhs : VExpr
  rhsAbs : VExpr
  type : VExpr

/-- `g := ⟨[], [], Prop, Prop, Prop, Type⟩`. -/
def junkGen : PatGen := ⟨[], [], .sort .zero, .sort .zero, .sort .zero, .sort (.succ .zero)⟩

namespace SExpr
variable [Params]

/-- `pat_leaf_1a`'s `hty` and `hdef`, verbatim, hold for `junkGen` at any `rank c ci`. -/
theorem junkGen_sat (rank : Name → Nat) (c : Name) (ci : VConstant) :
    let g := junkGen
    (OnCtx (g.self ++ g.ctx) (fun Γ A => (Params.env.below rank (rank c)).IsType ci.uvars Γ A) ∧
      (Params.env.below rank (rank c)).HasType ci.uvars (g.self ++ g.ctx) g.rhsAbs
        (g.type.liftN g.self.length)) ∧
    Params.env.IsDefEq ci.uvars g.ctx g.lhs g.rhs g.type :=
  ⟨⟨trivial, .sortDF trivial trivial rfl⟩, .sortDF trivial trivial rfl⟩

end SExpr
end Lean4Lean
#print axioms Lean4Lean.SExpr.junkGen_sat
