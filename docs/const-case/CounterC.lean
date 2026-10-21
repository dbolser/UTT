import Lean4Lean.Experimental.ShapeLogRelAdequacy
-- historical: typechecked at 3c35f59, before the typed logical relation (docs/const-case/PLAN.md D6, landed by R1+R2); no longer compiles.
/-! Lens 1, experiment 1: design C's field clause (universal over `LE_Interp`-valid type shapes,
"Subst1 form") is NOT level-invariant: `LR.DefEq.lift` (⇐ direction) fails for it.

`FieldC IH X Y T p ρ` is the per-field conjunct of `LRS.CtorArgsEq.cons`
(docs/const-case/CtorClause.lean), with the field type already instantiated.  C's §4 `mono_l`
fix (`∀ q ≤ p`) is covered by `FieldC'`.  We exhibit `X T p ρ Γ` such that the clause holds at
level 1 (so `ctor c [p]` would be related at level 2) but fails at level 2 for the lifted field
shape `p.lift 2` (so `ctor c [p.lift 2] = (ctor c [p]).lift 3` is NOT related at level 3).
The head-reduction conjuncts of `CtorDefEq` are level-free, so this is a counterexample to the
⇐ direction of `LR.lift_succ_aux` for any `LRS.DefEq` clause containing `FieldC`/`FieldC'`.

Why: under the fake-but-admissible valuation `ρ 0 = ⟦Π ⊥, ⊥⟧`, the level-2 type shape
`a' = Π (Π ⊥ ⊥), sort` of `T = Π (x : bvar 0), sort` is valid and types `(lam g).lift`, yet the
LR at `(lam g).lift, a'` demands `TyDefEq (bvar 0) (bvar 0) (Π ⊥ ⊥)`, i.e. `bvar 0 ⤳* Π _ _`,
which is false.  At level 1 the only valid domain shape is `⊥`, where nothing is demanded.
No sorries. -/
namespace Lean4Lean.SExpr
variable [Params]

/-- Design C's field conjunct (CtorClause.lean, `CtorArgsEq.cons`, 4th premise). -/
def FieldC (IH : LogRel Γ n) (X Y T : SExpr) (p : WShape n) (ρ : Valuation) : Prop :=
  ∀ a : WShape n, LE_Interp ρ a.T T → p.HasType a → IH.DefEq X Y T p a

/-- Design C §4's `mono_l` fix: relatedness at all typed points below `p`. -/
def FieldC' (IH : LogRel Γ n) (X Y T : SExpr) (p : WShape n) (ρ : Valuation) : Prop :=
  ∀ a : WShape n, LE_Interp ρ a.T T → ∀ q ≤ p, q.HasType a → IH.DefEq X Y T q a

theorem FieldC'.toFieldC {IH : LogRel Γ n} : FieldC' IH X Y T p ρ → FieldC IH X Y T p ρ :=
  fun H a ha hp => H a ha p .rfl hp

/-! ### The data -/

/-- `g₀ = {⊥ ↦ sort}` at level 0. -/
def g₀ : WShapeFun 0 := WShapeFun.single .bot (.sort true)
theorem g₀_nz : g₀.NonZero := ⟨(Shape.bot, Shape.sort true), ShapeFun.self_mem_single, by decide⟩
/-- The field shape: `λ _. sort` at level 1. -/
def p₁ : WShape 1 := WShape.lam g₀ g₀_nz
/-- `Π ⊥, ⊥` at level 1 — NOT a lift of any level-0 shape. -/
def a₁' : WShape 1 := WShape.forallE .bot .bot
/-- `{⊥ ↦ sort}` at level 1. -/
def f' : WShapeFun 1 := WShapeFun.single .bot (.sort true)
/-- `Π (Π ⊥ ⊥), sort` at level 2. -/
def a' : WShape 2 := WShape.forallE a₁' f'
/-- Valuation declaring `bvar 0` to have shape `Π ⊥ ⊥`. -/
def ρ₀ : Valuation := Valuation.nil.push a₁'.T

def l₁ : SLevel := .succ .zero
theorem l₁_ne : l₁ ≠ .zero := by
  intro h; have := congrArg (fun l : SLevel => l.1 []) h
  simp [l₁, SLevel.succ, SLevel.zero] at this

/-- The field type `Π (x : bvar 0), sort`. -/
def T₀ : SExpr := .forallE (.bvar 0) (.sort l₁)
/-- The field `λ (x : bvar 0). sort`. -/
def X₀ : SExpr := .lam (.bvar 0) (.sort l₁)
def Γ₀ : List SExpr := [.sort .zero]

theorem X₀_beta : Γ₀ ⊢ X₀.app a ⤳* .sort l₁ := .tail .rfl .beta

theorem WHNF.bvar : WHNF Γ (.bvar i) := by
  intro _ H; cases H with
  | extra h1 h2 => obtain ⟨_|_, rfl⟩ := Params.pat_simple h1 <;> nomatch h2

/-! ### Level 1: the clause holds (even in the `∀ q ≤ p` form) -/

theorem lr0_ty_sort {s : WShape 0} : LR0.TyDefEq Γ (.sort l) (.sort l) s := by
  obtain ⟨⟨⟩, _⟩ := s
  · trivial
  · exact ⟨l, .rfl, .rfl⟩

theorem lr0_defEq_X {m s : WShape 0} :
    LR0.DefEq Γ₀ (X₀.app a) (X₀.app b) m s := by
  obtain ⟨⟨⟩, _⟩ := s
  · trivial
  · show LR0.TyDefEq _ _ _ _
    obtain ⟨⟨⟩, _⟩ := m
    · trivial
    · exact ⟨l₁, X₀_beta, X₀_beta⟩

theorem level1_holds : FieldC' (LR Γ₀) (n := 1) X₀ X₀ T₀ p₁ ρ₀ := by
  intro a ha q le hq
  cases q using WShape.casesOn' with
  | bot => exact (LR _).bot hq.isType
  | sort => exact (Shape.LE.def.1 le).elim
  | forallE _ _ => exact (Shape.LE.def.1 le).elim
  | ctor => exact (Shape.LE.def.1 le).elim
  | indTy => exact (Shape.LE.def.1 le).elim
  | lam g hg =>
  cases a using WShape.casesOn' with
  | forallE a₁ f₁ => ?_
  | _ => cases hq
  have htm : WShape.HasTypeLam g a₁ f₁ := by
    cases Shape.HasType.unfold hq with | lam H => exact H
  -- the only valid level-0 domain shape under `ρ₀` is `⊥`
  have hle : a₁.T ≤ a₁'.T := LE_Interp.bvar_iff.1 (ha.forallE_inv.1)
  obtain ⟨_ | r, _⟩ := a₁
  · -- a₁ = ⊥
    simp only [LR, LRS, LRS.DefEq.lam_forallE]
    refine ⟨.bvar 0, .sort l₁, .zero, l₁.succ, .rfl, IsDefEq.bvar .zero, trivial, .sort, ?_, ?_⟩
    · exact ⟨fun _ _ _ _ _ _ => ⟨lr0_ty_sort, lr0_ty_sort⟩, fun _ _ _ _ _ => lr0_ty_sort⟩
    · exact ⟨fun _ _ _ _ _ _ => ⟨lr0_defEq_X, lr0_defEq_X⟩, fun _ _ _ _ _ => lr0_defEq_X⟩
  · -- a₁ = sort: not below `Π ⊥ ⊥`
    exfalso
    have hle' : (WShape.sort r : WShape 0).T ≤ a₁'.T := hle
    rw [TShape.LE.lift_l (Nat.zero_le 1), WShape.lift_sort] at hle'
    exact (Shape.LE.def.1 hle').elim

/-! ### Level 2: the clause fails for the lifted field shape -/

theorem a₁'_type : a₁'.HasType .type := rfl
theorem bot_a₁' : (WShape.bot : WShape 1).HasType a₁' := rfl

theorem a'_valid : LE_Interp ρ₀ a'.T T₀ := by
  refine .forallE (n := 1) (b := a₁') (b' := a₁') (f := f') (.bvar TShape.LE.rfl) (.bvar TShape.LE.rfl)
    ?_ ?_ TShape.LE.rfl
  · -- HasDom f' a₁'
    rw [WShape.HasDom.def]; intro x y h
    rcases WShapeFun.mem_single.1 h with ⟨⟨⟩⟩ | ⟨h, _⟩
    · exact ⟨_, _, h, .rfl, .rfl, bot_a₁'⟩
    · exact absurd WShape.LE.rfl h
  · intro x _
    refine .sort ?_
    rw [show f'.app x = .sort true by rw [f', WShapeFun.single_app, if_pos WShape.bot_le],
      decide_eq_true l₁_ne]
    exact TShape.sort_eqv.1

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

theorem level2_fails : ¬ FieldC (LR Γ₀) (n := 2) X₀ X₀ T₀ (p₁.lift 2) ρ₀ := by
  intro H
  have key : LRS.DefEq (n := 1) (LR Γ₀) X₀ X₀ T₀ (p₁.lift 2) (WShape.forallE a₁' f') :=
    H a' a'_valid p₁_lift_typed
  rw [p₁_lift, LRS.DefEq.lam_forallE] at key
  obtain ⟨A₁, A₂, u, v, rT, -, hValA, -, -, -⟩ := key
  have eT : SExpr.forallE (.bvar 0) (.sort l₁) = .forallE A₁ A₂ := WHNF.forallE.whRedS rT
  cases eT
  -- `TyDefEq (bvar 0) (bvar 0) (Π ⊥ ⊥)` at level 1 demands `bvar 0 ⤳* Π _ _`
  have hValA' : LRS.TyDefEq (n := 0) (LR Γ₀) (.bvar 0) (.bvar 0) (WShape.forallE .bot .bot) := hValA
  obtain ⟨B₁, F₁, _, _, _, _, rM, -⟩ := (LRS.TyDefEq.forallE_iff (IH := LR Γ₀)).1 hValA'
  cases WHNF.bvar.whRedS rM

/-- **The counterexample.**  Both C's clause and its `∀ q ≤ p` variant hold at level 1 for the
field `(X₀ : T₀)` at shape `p₁` under `ρ₀`, and fail at level 2 for the lifted shape. -/
theorem fieldC_not_lift_invariant :
    FieldC' (LR Γ₀) (n := 1) X₀ X₀ T₀ p₁ ρ₀ ∧ FieldC (LR Γ₀) (n := 1) X₀ X₀ T₀ p₁ ρ₀ ∧
    ¬ FieldC (LR Γ₀) (n := 2) X₀ X₀ T₀ (p₁.lift 2) ρ₀ ∧
    ¬ FieldC' (LR Γ₀) (n := 2) X₀ X₀ T₀ (p₁.lift 2) ρ₀ :=
  ⟨level1_holds, level1_holds.toFieldC, level2_fails, fun h => level2_fails h.toFieldC⟩

/-- Sanity: `a₁'` is not the lift of any level-0 shape (level 0 has no `Π`). -/
theorem a₁'_not_lift : ∀ s : WShape 0, s.lift 1 ≠ a₁' := by
  intro s h; obtain ⟨⟨⟩, _⟩ := s <;> cases h

end Lean4Lean.SExpr

#print axioms Lean4Lean.SExpr.fieldC_not_lift_invariant
