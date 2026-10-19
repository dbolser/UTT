import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Refuter check of claim C1 (analyst lens `clause`).

`CounterC.lean` shows the per-field conjunct of design C fails at level 2 for the lifted field
shape under the valuation `ρ₀ = nil.push (Π ⊥ ⊥).T`, with the previous field being the *variable*
`bvar 0 : sort 0`.  Here: replace the previous field by a *realised* one, i.e. a term that really
whnf's to a Π (so C's own first-field conjunct can hold at shape `Π ⊥ ⊥`).  Then the analyst's
failing instance (field `λ (_ : Xp). Type : Xp → Type` at `(p₁.lift 2, a')`) HOLDS at level 2.
So the failure in `level2_fails` comes from the unrealised valuation, not from C's clause.
No sorries. -/
namespace Lean4Lean.SExpr
variable [Params]

-- the analyst's data (copied from CounterC.lean)
def g₀ : WShapeFun 0 := WShapeFun.single .bot (.sort true)
theorem g₀_nz : g₀.NonZero := ⟨(Shape.bot, Shape.sort true), ShapeFun.self_mem_single, by decide⟩
def p₁ : WShape 1 := WShape.lam g₀ g₀_nz
def a₁' : WShape 1 := WShape.forallE .bot .bot
def f' : WShapeFun 1 := WShapeFun.single .bot (.sort true)
def a' : WShape 2 := WShape.forallE a₁' f'
def l₁ : SLevel := .succ .zero

theorem p₁_lift : p₁.lift 2 = WShape.lam (g₀.lift 1) ((WShapeFun.NonZero.lift_iff (Nat.le_succ 0)).2 g₀_nz) :=
  WShape.lift_lam (Nat.le_succ 0)

-- realised previous field: `Xp := Prop → Prop` (whnf is a Π), in the empty context
def Γr : List SExpr := []
def Xp : SExpr := .forallE (.sort .zero) (.sort .zero)
/-- the second field's declared type, instantiated with the realised first field -/
def Tσ : SExpr := .forallE Xp (.sort l₁)
def Xr : SExpr := .lam Xp (.sort l₁)

theorem g₀_lift : g₀.lift 1 = (WShapeFun.single .bot (.sort true) : WShapeFun 1) := by
  apply WShapeFun.ext; rw [WShapeFun.lift_val (Nat.le_succ 0)]; rfl

theorem f'_app (p : WShape 1) : f'.app p = .sort true := by
  rw [f', WShapeFun.single_app, if_pos WShape.bot_le]

/-- The failing step of `level2_fails` (`TyDefEq _ _ (Π ⊥ ⊥)` at level 1) holds for `Xp`. -/
theorem tyXp : (LR Γr (n := 1)).TyDefEq Xp Xp a₁' := by
  show LRS.TyDefEq (n := 0) (LR Γr) Xp Xp (WShape.forallE .bot .bot)
  rw [LRS.TyDefEq.forallE_iff]
  refine ⟨.sort .zero, .sort .zero, .sort .zero, .sort .zero, _, _, .rfl, .rfl, .sort, .sort,
    trivial, ⟨fun _ _ _ _ _ _ => ?_, fun _ _ _ _ _ => ?_⟩⟩ <;>
    simp only [WShapeFun.bot_app] <;> trivial

/-- **The analyst's level-2 instance, realised: it holds.** -/
theorem realised_level2 : (LR Γr (n := 2)).DefEq Xr Xr Tσ (p₁.lift 2) a' := by
  show LRS.DefEq (n := 1) (LR Γr) Xr Xr Tσ (p₁.lift 2) (WShape.forallE a₁' f')
  rw [p₁_lift, LRS.DefEq.lam_forallE]
  refine ⟨Xp, .sort l₁, _, _, .rfl, .forallEDF .sort .sort, tyXp, .sort, ?_, ?_⟩
  · refine ⟨fun _ _ p _ _ _ => ?_, fun _ p _ _ _ => ?_⟩ <;> rw [f'_app p]
    · exact ⟨LogRelBase.TyDefEq.sort, LogRelBase.TyDefEq.sort⟩
    · exact LogRelBase.TyDefEq.sort
  · refine ⟨fun _ _ p _ _ _ => ?_, fun _ p _ _ _ => ?_⟩ <;>
      rw [f'_app p, g₀_lift, WShapeFun.single_app, if_pos WShape.bot_le]
    · exact ⟨(LR _).sort_iff.2 ⟨l₁, .tail .rfl .beta, .tail .rfl .beta⟩,
             (LR _).sort_iff.2 ⟨l₁, .tail .rfl .beta, .tail .rfl .beta⟩⟩
    · exact (LR _).sort_iff.2 ⟨l₁, .tail .rfl .beta, .tail .rfl .beta⟩

/-- The DefEq type in C's clause is `T.subst σ` with `T = Π (bvar 0), Type` the *unsubstituted*
field type (the one `LE_Interp ρ₀ a'.T T` is about, `a'_valid` in CounterC.lean) and
`σ = id.cons Xp` built from the realised previous field. -/
theorem Tσ_eq : (SExpr.forallE (.bvar 0) (.sort l₁)).subst (Subst.id.cons Xp) = Tσ := rfl

end Lean4Lean.SExpr
#print axioms Lean4Lean.SExpr.realised_level2
