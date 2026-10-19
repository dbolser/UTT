import Lean4Lean.Experimental.ShapeLogRelAdequacy
namespace Lean4Lean.SExpr
variable [Params]
open _root_.Lean4Lean.Params

/-! Refutation experiment for report claim T12 ("`induction hM` after
`generalize eq : SExpr.const c ls = M at hM` yields an IH for EVERY fixed-constant leaf,
same-block or not").

(1) Exact shape of the IH produced by the recommended recipe, in the setting of the real
`const` case (motive = the const-case goal, type fixed to `mkInst ls ci.type`). -/
example {c : Name} {ci : VConstant} {ls : List SLevel} {ρ : Valuation} {n} {m a : WShape n} {u : SLevel}
    (h1 : env.constants c = some ci) (h2 : ls.length = ci.uvars)
    (ih3 : ∀ {ρ : Valuation} {n} {m a : WShape n}, LE_Interp ρ m.T (mkInst ls ci.type) →
      LE_Interp ρ a.T (.sort u) → m.HasType a →
      LR.Adequate Γ₀ Γ ρ (mkInst ls ci.type) (mkInst ls ci.type) (.sort u) m a)
    (hM : LE_Interp ρ m.T (.const c ls)) (hA : LE_Interp ρ a.T (mkInst ls ci.type))
    (hmem : m.HasType a) :
    (LR Γ₀).DefEq (.const c ls) (.const c ls) (mkInst ls ci.type) m a := by
  generalize eq : SExpr.const c ls = M at hM
  generalize eqm : m.T = mT at hM
  induction hM generalizing n m a with cases eq
  | bot => sorry  -- deliberate: not the point
  | const a1 a2 a3 a4 a5 a6 a7 ihA ihR =>
    -- READ THE TRACE: `ihR : ∀ (m e), R m e → const c ls = e → m = ?.T → … → DefEq e e (mkInst ls ci.type) …`
    -- The equation `const c ls = e` is a *hypothesis of the IH*: for an `R`-leaf
    -- `e = const c' ls'` with `c' ≠ c` (minor premises' constants, other recursors of a
    -- mutual block, the body of a delta rule), or for `e` a closed non-constant term
    -- (delta-rule body `mkInst ls body`), it is unsatisfiable, so the IH says nothing.
    trace_state
    sorry  -- deliberate

/-! (2) The recipe's IH is literally vacuous off the self-reference: the equation it demands
is refutable for any other constant. -/
theorem ih_off_self_vacuous {c c' : Name} {ls ls' : List SLevel} (hne : c' ≠ c)
    {Q : SExpr → Prop} {R : TShape → SExpr → Prop}
    (ihR : ∀ m e, R m e → SExpr.const c ls = e → Q e)
    {m} (h : R m (.const c' ls')) : ¬ (SExpr.const c ls = SExpr.const c' ls') := by
  intro h'; cases h'; exact hne rfl

/-! (3) Generalised motive (design B's step A without a block restriction): induct on the
model derivation of an arbitrary `M`, with the motive "if `M` is a constant `c'` then adequacy
at `c'`'s own type". Now `ihR` IS usable at every constant leaf. But look at the goal in the
`const` case: it needs `DefEq (const c' ls') (const c' ls') (mkInst ls' ci'.type) m a`, and the
`Const.lam` row of `a6` (`a = forallE a₁ a₂`) unfolds it to Π-validity of `mkInst ls' ci'.type`
(`∃ A₁ A₂ u v, mkInst ls' ci'.type ⤳* forallE A₁ A₂ ∧ … ∧ PiDefEq …`, `LRS.DefEq.lam_forallE`).
Nothing in scope gives type adequacy of `c'`: `ihA` is the motive at the type's *model*
derivation, which is about `const _ _`-shaped terms only; `ih3` in the real const case exists
for `c` alone. This is the hole designs A (rank) and B (premises) fill. -/
example {ρ : Valuation} {mT : TShape} {M : SExpr} (hM : LE_Interp ρ mT M) :
    ∀ (c' : Name) (ls' : List SLevel) (ci' : VConstant), env.constants c' = some ci' →
      M = .const c' ls' →
      ∀ {n} (m a : WShape n), mT = m.T → LE_Interp ρ a.T (mkInst ls' ci'.type) → m.HasType a →
      (LR Γ₀).DefEq (.const c' ls') (.const c' ls') (mkInst ls' ci'.type) m a := by
  induction hM with
  | const a1 a2 a3 a4 a5 a6 a7 ihA ihR =>
    intro c' ls' ci' hci' heq n m a hmT hA hmem
    cases heq
    trace_state
    sorry  -- deliberate
  | _ => intros; subst_vars; first | sorry | skip  -- deliberate; other constructors are not `const`

end Lean4Lean.SExpr
