import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Refuter scratch (patleaf lens).
(a) `pat_typed` (Measure.lean `RankParams.pat_typed`) existentially quantifies `Γp Tp idx self`
    with no link to the rule's telescope.  For an iota RHS of the form `minor x`
    (`W.rec motive minor (W.mk x) ↦ minor x`, pattern `app (varN (const rec) 2) (varN (const mk) 1)`,
    RHS `.app (.var minor) (.var x)`, so `toVExpr idx self = app (bvar (idx minor)) (bvar (idx x))`)
    it is witnessed in EVERY environment by the junk context below, whose entries have nothing to
    do with the real types of `minor`/`x`.  A consumer must therefore work for this witness, and
    `Subst1` (first conjunct `Γ₀ ⊢ σ i ≡ σ' i : Γp[i][σ]`) would demand the actual minor premise be
    typed at `Prop → Prop`: impossible in general.
(b) The LR at type-shape `sort` does not look at the type: conversion of field/result types is
    vacuous there (refines patleaf C16 "non-trivial exactly when sort or Pi").
No sorries. -/
namespace Lean4Lean

/-- junk pattern context: `[x : Prop, minor : Prop → Prop]` (innermost first). -/
def ΓJ : List VExpr := [.sort .zero, .forallE (.sort .zero) (.sort .zero)]

theorem junk_rhs_typed (env : VEnv) (U : Nat) :
    env.HasType U ΓJ (.app (.bvar 1) (.bvar 0)) (.sort .zero) := by
  have h1 : env.HasType U ΓJ (.bvar 1) (.forallE (.sort .zero) (.sort .zero)) :=
    VEnv.IsDefEq.bvar (.succ .zero)
  have h0 : env.HasType U ΓJ (.bvar 0) (.sort .zero) := VEnv.IsDefEq.bvar .zero
  exact VEnv.IsDefEq.appDF h1 h0

theorem junk_ctx_wf (env : VEnv) (U : Nat) :
    env.IsType U [.forallE (.sort .zero) (.sort .zero)] (.sort .zero) ∧
    env.IsType U [] (.forallE (.sort .zero) (.sort .zero)) := by
  have s0 : ∀ Γ, env.HasType U Γ (.sort .zero) (.sort (.succ .zero)) := fun _ =>
    VEnv.IsDefEq.sortDF (by trivial) (by trivial) rfl
  exact ⟨⟨_, s0 _⟩, ⟨_, VEnv.IsDefEq.forallEDF (s0 _) (s0 _)⟩⟩

namespace SExpr
variable [Params]

/-- (b) at every level, `DefEq` at type-shape `sort` is independent of the type argument. -/
example {Γ : List SExpr} {n} {M N A B : SExpr} {m : WShape (n+1)} {r : Bool} :
    (LR Γ (n := n+1)).DefEq M N A m (.sort r) ↔ (LR Γ (n := n+1)).DefEq M N B m (.sort r) :=
  Iff.rfl
example {Γ : List SExpr} {M N A B : SExpr} {m a : WShape 0} :
    (LR Γ (n := 0)).DefEq M N A m a ↔ (LR Γ (n := 0)).DefEq M N B m a := Iff.rfl
/-- ... but at type-shape `forallE` it demands `A ⤳* forallE A₁ A₂` (type-dependent). -/
example {Γ : List SExpr} {n} {M N A : SExpr} {f hf a₁ a₂} :
    (LR Γ (n := n+1)).DefEq M N A (.lam f hf) (.forallE a₁ a₂) ↔
    (∃ A₁ A₂ u v, Γ ⊢ A ⤳* .forallE A₁ A₂ ∧ Γ ⊢ A₁ : .sort u ∧ (LR Γ).TyDefEq A₁ A₁ a₁ ∧
      A₁::Γ ⊢ A₂ : sort v ∧ LRS.PiDefEq (LR Γ) A₁ A₂ A₂ a₁ a₂ ∧
      LRS.LamDefEq (LR Γ) M N A₁ A₂ f a₁ a₂) := LRS.DefEq.lam_forallE (hf := hf) _
end SExpr
end Lean4Lean
#print axioms Lean4Lean.junk_rhs_typed
#print axioms Lean4Lean.junk_ctx_wf
