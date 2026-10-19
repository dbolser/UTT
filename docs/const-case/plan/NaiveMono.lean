import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Refuter check of claim C8 (B's naive ∃-type-shape field clause fails `mono_l`).
The analyst only typechecked the shape fact (`HasType` not downward closed in the element).
Here the full per-field failure: for the closed field `Xr := λ (_ : Prop → Prop). Type` of type
`Tσ := (Prop → Prop) → Type`, the ∃-clause `N p := ∃ t, p : t ∧ DefEq Xr Xr Tσ p t` holds at
`gS' = p₁.lift 2` but fails at the smaller `gSw ≤ gS'`.  So `mono_l` (which, at `indTy`, has no
field-typing hypothesis under the current `hasType (ctor ..) indTy = true`) is false for that clause.
No sorries. -/
namespace Lean4Lean.SExpr
variable [Params]

def g₀ : WShapeFun 0 := WShapeFun.single .bot (.sort true)
theorem g₀_nz : g₀.NonZero := ⟨(Shape.bot, Shape.sort true), ShapeFun.self_mem_single, by decide⟩
def p₁ : WShape 1 := WShape.lam g₀ g₀_nz
def a₁' : WShape 1 := WShape.forallE .bot .bot
def f' : WShapeFun 1 := WShapeFun.single .bot (.sort true)
def a' : WShape 2 := WShape.forallE a₁' f'
def l₁ : SLevel := .succ .zero
theorem p₁_lift : p₁.lift 2 = WShape.lam (g₀.lift 1) ((WShapeFun.NonZero.lift_iff (Nat.le_succ 0)).2 g₀_nz) :=
  WShape.lift_lam (Nat.le_succ 0)
theorem p₁_lift_typed : (p₁.lift 2).HasType a' := by
  rw [p₁_lift, WShape.lam_eq_lam']
  refine WShape.HasType.lam ?_
  show Shape.HasTypeLam (g₀.lift 1).1 a₁'.1 f'.1
  rw [WShapeFun.lift_val (Nat.le_succ 0)]
  have h : Shape.HasType (n := 2) (.lam (ShapeFun.lift (Shape.lift (n := 0) 1) (ShapeFun.single (n := 0) .bot (.sort true))))
      (.forallE (.forallE .bot [(.bot, .bot)]) (ShapeFun.single (n := 1) .bot (.sort true))) := rfl
  cases h.unfold with | lam H => exact H
def Γr : List SExpr := []
def Xp : SExpr := .forallE (.sort .zero) (.sort .zero)
def Tσ : SExpr := .forallE Xp (.sort l₁)
def Xr : SExpr := .lam Xp (.sort l₁)
theorem g₀_lift : g₀.lift 1 = (WShapeFun.single .bot (.sort true) : WShapeFun 1) := by
  apply WShapeFun.ext; rw [WShapeFun.lift_val (Nat.le_succ 0)]; rfl
theorem f'_app (p : WShape 1) : f'.app p = .sort true := by
  rw [f', WShapeFun.single_app, if_pos WShape.bot_le]
theorem tyXp : (LR Γr (n := 1)).TyDefEq Xp Xp a₁' := by
  show LRS.TyDefEq (n := 0) (LR Γr) Xp Xp (WShape.forallE .bot .bot)
  rw [LRS.TyDefEq.forallE_iff]
  refine ⟨.sort .zero, .sort .zero, .sort .zero, .sort .zero, _, _, .rfl, .rfl, .sort, .sort,
    trivial, ⟨fun _ _ _ _ _ _ => ?_, fun _ _ _ _ _ => ?_⟩⟩ <;>
    simp only [WShapeFun.bot_app] <;> trivial
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

/-- B's naive per-field clause. -/
def NaiveField (x : SExpr) (T : SExpr) (p : WShape 2) : Prop :=
  ∃ t : WShape 2, p.HasType t ∧ (LR Γr).DefEq x x T p t

/-- `gS = {⊥ ↦ ⊥, sort ↦ sort}` (NotDownClosed.lean). -/
def gS1 : WShapeFun 1 := WShapeFun.single (.sort true) (.sort true)
theorem gS1_nz : gS1.NonZero :=
  ⟨(Shape.sort true, Shape.sort true), ShapeFun.self_mem_single, by decide⟩
def gSw : WShape 2 := WShape.lam gS1 gS1_nz

theorem gSw_le : gSw ≤ p₁.lift 2 := by
  show gSw.1 ≤ (p₁.lift 2).1
  rw [WShape.lift_val (Nat.le_succ 1)]; exact rfl

theorem naive_big : NaiveField Xr Tσ (p₁.lift 2) := ⟨a', p₁_lift_typed, realised_level2⟩

theorem naive_small_fails : ¬ NaiveField Xr Tσ gSw := by
  rintro ⟨t, ht, hD⟩
  generalize eq : gSw = m at ht
  cases ht.unfold with
  | bot => cases congrArg (·.1) eq
  | sort => cases congrArg (·.1) eq
  | forallE => cases congrArg (·.1) eq
  | ctor => cases congrArg (·.1) eq
  | indTy => cases congrArg (·.1) eq
  | @lam _ f a b hl =>
    have hf : f = gS1 := by
      have := congrArg (·.1) eq; simp only [gSw, WShape.lam, WShape.lam'] at this
      split at this
      · injection this with this; exact WShapeFun.ext this.symm
      · cases this
    subst hf
    -- the key `sort ↦ sort` forces `sort : a`
    have hd := (WShape.HasTypeLam.iff.1 hl).2.1
    obtain ⟨x', y', hmem, -, hy, hx'⟩ := WShape.HasDom.def.1 hd (.sort true) (.sort true)
      (WShapeFun.mem_single.2 (.inl rfl))
    rcases WShapeFun.mem_single.1 hmem with h | ⟨-, h⟩
    · cases h
      -- `DefEq` at `(lam, Π a b)` demands `TyDefEq Xp Xp a`, and `sort : a`
      have hD' : LRS.DefEq (n := 1) (LR Γr) Xr Xr Tσ gSw (WShape.forallE a b) := hD
      rw [gSw, LRS.DefEq.lam_forallE] at hD'
      obtain ⟨A₁, A₂, _, _, rT, -, hTy, -⟩ := hD'
      cases WHNF.forallE.whRedS rT
      cases a using WShape.casesOn' with
      | sort r =>
        obtain ⟨_, rX, -⟩ := hTy
        cases WHNF.forallE.whRedS rX
      | _ => cases hx'
    · cases h; have := WShape.le_bot.1 hy; cases congrArg (·.1) this

end Lean4Lean.SExpr
#print axioms Lean4Lean.SExpr.naive_small_fails
#print axioms Lean4Lean.SExpr.naive_big
#print axioms Lean4Lean.SExpr.gSw_le
