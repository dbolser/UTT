import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Completeness audit 3: `rank_ordered` for `emptyParams` (env := .empty). `VEnv.below` as in
Measure6.lean:44 / PatLeafStmt.lean:44 (copied). Sorry-free. -/
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

theorem VEnv.empty_below (rank : Name → Nat) (k : Nat) : VEnv.empty.below rank k = .empty := by
  have hc : (VEnv.empty.below rank k).constants = VEnv.empty.constants := by
    funext c; simp only [VEnv.below]; split <;> rfl
  have hd : (VEnv.empty.below rank k).defeqs = VEnv.empty.defeqs := by
    funext df; simp only [VEnv.below]; exact propext ⟨fun h => h.1, fun h => h.elim⟩
  cases h : VEnv.empty.below rank k
  rw [h] at hc hd; cases hc; cases hd; rfl

theorem emptyParams_rank_ordered (rank : Name → Nat) (k : Nat) :
    (VEnv.empty.below rank k).Ordered := by rw [VEnv.empty_below]; exact .empty

#print axioms emptyParams_rank_ordered
