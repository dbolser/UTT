import Lean4Lean.Experimental.ShapeLogRelAdequacy
-- historical: typechecked at 3c35f59, before the typed logical relation (docs/const-case/PLAN.md D6, landed by R1+R2); no longer compiles.
/-! Refuter (proof, lens clause), experiment 1.
CounterC.lean's configuration, but checked against design C's FULL clause
(`LRS.CtorArgsEq`, copied verbatim from docs/const-case/CtorClause.lean), not the isolated field
conjunct `FieldC`.  In C's clause the valuation `ρ` is built from the previous fields' shapes
(`ρ.push p.T`) and the previous field itself must be related at that shape.  CounterC puts the
previous field (`bvar 0`, the `Γ₀` variable its `T₀`/`X₀` mention) at shape `a₁' = Π ⊥ ⊥`; the
previous-field conjunct then demands `bvar 0 ⤳* Π _ _`, which is false.  So the full clause is
false at BOTH levels in that configuration, and CounterC is not a counterexample to
`LR.DefEq.lift` for C's clause.  Moreover the exact fact CounterC's `level2_fails` refutes
(`TyDefEq A₁ A₁ a₁'` at level 1, with `A₁` the previous field) is literally supplied by C's
first-field conjunct at level 1 (`first_field_supplies`).  No sorries. -/
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


/-- Verbatim from docs/const-case/CtorClause.lean. -/
inductive LRS.CtorArgsEq' (IH : LogRel Γ n) :
    List SExpr → List SExpr → List SExpr → List (WShape n) → Valuation → Subst → Subst → Prop
  | nil : CtorArgsEq' IH [] [] [] [] ρ σ σ'
  | cons {T Ts X Xs Y Ys} {p : WShape n} {l ρ σ σ'} :
    (∃ u, Γ ⊢ T.subst σ ≡ T.subst σ' : .sort u) →
    (∀ a : WShape n, LE_Interp ρ a.T T → a.HasType .type →
      IH.TyDefEq (T.subst σ) (T.subst σ') a) →
    Γ ⊢ X ≡ Y : T.subst σ →
    (∀ a : WShape n, LE_Interp ρ a.T T → p.HasType a → IH.DefEq X Y (T.subst σ) p a) →
    CtorArgsEq' IH Ts Xs Ys l (ρ.push p.T) (σ.cons X) (σ'.cons Y) →
    CtorArgsEq' IH (T :: Ts) (X :: Xs) (Y :: Ys) (p :: l) ρ σ σ'

theorem sort0_valid {n} : LE_Interp Valuation.nil (WShape.sort (n := n+1) false).T (.sort .zero) := by
  refine .sort ?_
  have : decide (SLevel.zero ≠ SLevel.zero) = false := by simp
  rw [this]; exact TShape.sort_eqv.1

theorem a₁'_prop : a₁'.HasType (WShape.sort false) := rfl

/-- The previous-field conjunct at shape `a₁'` (level 1) forces its term to reduce to a Π. -/
theorem prev_forces_pi {X Y : SExpr}
    (h4 : ∀ a : WShape 1, LE_Interp Valuation.nil a.T (.sort .zero) → a₁'.HasType a →
      (LR Γ₀).DefEq X Y ((SExpr.sort .zero).subst .id) a₁' a) :
    ∃ B F, Γ₀ ⊢ X ⤳* .forallE B F := by
  have key := h4 _ sort0_valid a₁'_prop
  have k2 : LRS.TyDefEq (n := 0) (LR Γ₀) X Y (WShape.forallE .bot .bot) := key
  obtain ⟨B₁, F₁, _, _, _, _, rM, -⟩ := (LRS.TyDefEq.forallE_iff (IH := LR Γ₀)).1 k2
  exact ⟨_, _, rM⟩

/-- (a) Level 1 (fields at level 1, i.e. the clause of the level-2 ctor shape): C's full clause
is FALSE in CounterC's configuration (previous field `bvar 0` at shape `a₁'`). -/
theorem full_level1_false :
    ¬ LRS.CtorArgsEq' (LR Γ₀) (n := 1) [.sort .zero, T₀] [.bvar 0, X₀] [.bvar 0, X₀]
      [a₁', p₁] .nil .id .id := by
  intro h
  cases h with
  | cons _ _ _ h4 _ =>
    obtain ⟨B, F, r⟩ := prev_forces_pi h4
    cases WHNF.bvar.whRedS r

/-- (b) Level 2 (lifted field shapes): also FALSE, for the same reason. -/
theorem full_level2_false :
    ¬ LRS.CtorArgsEq' (LR Γ₀) (n := 2) [.sort .zero, T₀] [.bvar 0, X₀] [.bvar 0, X₀]
      [a₁'.lift 2, p₁.lift 2] .nil .id .id := by
  intro h
  cases h with
  | cons _ _ _ h4 _ =>
    have ht : (a₁'.lift 2).HasType (WShape.sort false) := by
      have := (WShape.HasType.lift (Nat.le_succ 1)).2 a₁'_prop; rwa [WShape.lift_sort] at this
    have key := h4 _ sort0_valid ht
    have e : a₁'.lift 2 = WShape.forallE (WShape.bot.lift 1) (WShapeFun.bot.lift 1) :=
      WShape.lift_forallE (Nat.le_succ 0)
    have k2 : LRS.TyDefEq (n := 1) (LR Γ₀) (.bvar 0) (.bvar 0) (a₁'.lift 2) := key
    rw [e] at k2
    obtain ⟨B₁, F₁, _, _, _, _, rM, -⟩ := (LRS.TyDefEq.forallE_iff (IH := LR Γ₀)).1 k2
    cases WHNF.bvar.whRedS rM

/-- (c) Whatever the previous field `X` is: the fact CounterC's `level2_fails` shows missing
(`TyDefEq A₁ A₁ a₁'` at level 1 with `A₁ = X`, the domain of the instantiated field type
`Π (x : X), sort`) is literally C's first-field conjunct at level 1. -/
theorem first_field_supplies {X : SExpr}
    (h4 : ∀ a : WShape 1, LE_Interp Valuation.nil a.T (.sort .zero) → a₁'.HasType a →
      (LR Γ₀).DefEq X X ((SExpr.sort .zero).subst .id) a₁' a) :
    (LR Γ₀ (n := 1)).TyDefEq X X a₁' :=
  h4 _ sort0_valid a₁'_prop

end Lean4Lean.SExpr

#print axioms Lean4Lean.SExpr.full_level1_false
#print axioms Lean4Lean.SExpr.full_level2_false
#print axioms Lean4Lean.SExpr.first_field_supplies
