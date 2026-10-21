import Lean4Lean.Experimental.ShapeLogRelAdequacy

/-! C4/C5 level check.  In the pat leaf the recursor's parameter entry `q` is one level ABOVE the
constructor's field shapes (C1's own `Matches` example: `q : WShape (n+1)`, `q' x xs : WShape n`),
so the analyst's `LR.field_retype` / `LR.Subst1.tyValid_below` (common bound `q : WShape n` at the
fields' level) do not instantiate as stated.  They do go through with a `TShape` bound: -/

namespace Lean4Lean.SExpr
variable [Params]

theorem LR.field_retype_T {n} {Q : TShape} {a a₁ p p'' : WShape n} {x x' P P' : SExpr}
    (ha : a.T ≤ Q) (ha₁ : a₁.T ≤ Q)
    (hp : p.HasType a) (hp'' : p''.HasType a₁) (hle : p'' ≤ p)
    (hT : ∀ m : WShape n, m.T ≤ Q → m.HasType .type → (LR Γ₀).TyDefEq P P m)
    (hPP' : (LR Γ₀).TyDefEq P' P a)
    (h : (LR Γ₀).DefEq x x' P' p a) :
    (LR Γ₀).DefEq x x' P p'' a₁ := by
  have h1 : (LR Γ₀).DefEq x x' P p a := (LR Γ₀).conv hPP' h
  have hC : a.Compat a₁ := WShape.Compat.T_iff.2 (TShape.Compat.def'.2 ⟨Q, ha, ha₁⟩)
  have hJ := WShape.Join.mk hC
  have ⟨hj1, hj2⟩ := hJ.le
  have hjq : (a.join a₁).T ≤ Q := (hJ.T Q).2 ⟨ha, ha₁⟩
  have hjt : (a.join a₁).HasType .type := hp.isType.join' hJ hp''.isType
  have hpj : p.HasType (a.join a₁) := WShape.HasType.mono_r hj1 hjt hp
  have hp''j : p''.HasType (a.join a₁) := WShape.HasType.mono_r hj2 hjt hp''
  have h2 := (LR Γ₀).mono_r_1 hj1 hp hpj (hT _ hjq hjt) h1
  have h3 := (LR Γ₀).mono_l hle hp''j hpj h2
  exact (LR Γ₀).mono_r_2 hj2 hp'' hjt h3

theorem LR.Subst1.tyValid_below_T {n} {Q : TShape} {P P' A₀ A A' : SExpr} {ρ : Valuation}
    (h : LR.Subst1 Γ₀ P P' A₀ A A' (ρ.push Q))
    (hA₀ : LE_Interp (ρ.push Q) (WShape.sort true : WShape n).T A₀)
    {m : WShape n} (hm : m.T ≤ Q) (hmt : m.HasType (.sort true)) : (LR Γ₀).TyDefEq P P m :=
  (LR Γ₀).left_ty <| (LR Γ₀).toType <| (h.2 _ hA₀).2 (LE_Interp.bvar0.mono hm) hmt

/-- Instantiation at the real level split: recursor parameter entry `q : WShape (n+1)`. -/
example {n} {q : WShape (n+1)} {a a₁ p p'' : WShape n} {x x' P P' P'' A₀ A A' : SExpr}
    {ρ : Valuation}
    (hS : LR.Subst1 Γ₀ P P'' A₀ A A' (ρ.push q.T))
    (hA₀ : ∀ {k}, LE_Interp (ρ.push q.T) (WShape.sort true : WShape k).T A₀)
    (ha : a.T ≤ q.T) (ha₁ : a₁.T ≤ q.T)
    (hp : p.HasType a) (hp'' : p''.HasType a₁) (hle : p'' ≤ p)
    (hPP' : (LR Γ₀).TyDefEq P' P a) (h : (LR Γ₀).DefEq x x' P' p a) :
    (LR Γ₀).DefEq x x' P p'' a₁ :=
  LR.field_retype_T ha ha₁ hp hp'' hle
    (fun _ hm hmt => LR.Subst1.tyValid_below_T hS hA₀ hm hmt) hPP' h

end Lean4Lean.SExpr
