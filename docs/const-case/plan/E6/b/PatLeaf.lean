import Lean4Lean.Experimental.E6.Iota8
/-! # E6: the pattern leaf (`LR.pat_leaf_1a`'s statement, PLAN D4 "RHS step" steps 1-6 as
amended by E6a)

`T.pat_leaf_1a` has exactly the type of `LR.pat_leaf_1a` (ShapeLogRelAdequacy.lean). By
`pat_simple` the pattern is a delta rule `.const c` (`T.pat_leaf_delta`, sorry-free) or an iota
rule `rec x₁…xₘ (c' z₁…zₙ)` (`T.pat_leaf_iota`, sorry-free given two facts about the rule, its
hypotheses `hGA` and `hGB`). The two facts are the only sorries (`E6/Iota7.lean`); both are
unique-typing facts about the rule, not about the spine:
* `T.gap_major_levels` (fact A): the constructor clause's levels are the major domain's. Sorry
  only when the recursor's major domain `const I us` has a delta rule and the constructor is
  universe-polymorphic;
* `T.gap_prop_root_sort` (fact B): a rule whose RHS is a bare constructor field of a `Prop`
  instance type has its codomain in `Prop`.

`T.pat_leaf_1a_restricted` is the same statement under two candidate `Params` fields that discharge
the facts (no recursor's major domain is `symb`-classified; no iota RHS is a bare constructor-field
variable). It is sorry-free. -/
namespace Lean4Lean.SExpr
variable [Params]

/-- The pattern leaf (E6/R10), the statement of `LR.pat_leaf_1a` verbatim. -/
theorem T.pat_leaf_1a {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
    (WFIH : LR.WFIH Params.rank Γ₀ k) {c : Name} {ci : VConstant} {ls : List SLevel}
    (hc : Params.rank c < k) (h1 : Params.env.constants c = some ci) (h2 : ls.length = ci.uvars)
    {R : TShape → SExpr → Prop} (LIH : LR.LocalIH Params.rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e)
    {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} {mC : TShape}
    (hP : Params.Pat p r) (hMt : LE_Interp.Matches p c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1) (hchk : r.2 = .true)
    (g : PatGen) (hg : Pattern.gen Params.env Params.rank Params.classify p r.1 = some g)
    (hty : OnCtx (g.self ++ g.ctx)
        (fun Γ A => (Params.env.below Params.rank (Params.rank c)).IsType ci.uvars Γ A) ∧
      (Params.env.below Params.rank (Params.rank c)).HasType ci.uvars (g.self ++ g.ctx) g.rhsAbs
        (g.type.liftN g.self.length))
    (hdef : Params.env.IsDefEq ci.uvars g.ctx g.lhs g.rhs g.type)
    {Ts : List SExpr} {B : SExpr} (hT : mkInst ls ci.type = Ts.foldr .forallE B)
    (hk : rargs.length = Ts.length)
    {ρ : Valuation} {σ σ' : Subst} (hρ : (Valuation.ofRargs rargs).LE ρ)
    (W : LR.SubstWF Γ₀ σ σ' (Ts.reverse ++ Γ₀) ρ)
    {n'} {m a : WShape n'} (le : m.T ≤ mC) (hA : LE_Interp ρ a.T B) (hmem : m.HasType a)
    (tyV : ∀ {τ τ'}, LR.SubstWF Γ₀ τ τ' (Ts.reverse ++ Γ₀) ρ →
      (LR Γ₀).TyDefEq (B.subst τ) (B.subst τ') a) :
    (LR Γ₀).DefEq ((openSpine c ls Ts.length).subst σ) ((openSpine c ls Ts.length).subst σ')
      (B.subst σ) m a := by
  obtain ⟨sp, rfl⟩ := Params.pat_simple hP
  cases sp with
  | iota rec mm c' nn =>
    have hh := T.matches_head hMt
    obtain rfl : rec = c := (Pattern.head_varN rec mm).symm.trans hh
    have hΓctx : OnCtx g.ctx (fun Γ A => Params.env.IsType ci.uvars Γ A) :=
      (T.onCtx_append_right g.self hty.1).mono (fun h => h.mono (Params.env.below_le ..))
    exact T.pat_leaf_iota WFIH hc h1 h2 LIH hR hP hMt hRHS hchk g hg hty hdef hT hk hρ W le hA
      hmem tyV
      (fun hHs hTc hci' hIc hls hred =>
        T.gap_major_levels hP hg h1 hΓctx hdef hHs hTc hci' hIc hls hred)
      (fun hHs hTc hroot hF hprop hΓ₀ HB =>
        T.gap_prop_root_sort hP hg h1 h2 hHs hTc hroot hF hprop hΓ₀ HB)
  | defn c₀ =>
    exact T.pat_leaf_delta WFIH hc h1 h2 LIH hR hP hMt hRHS hchk g hg hdef hT hk W le hA hmem tyV

/-- The pattern leaf under two candidate `Params` fields, sorry-free: `RA`, no recursor's major
domain is `symb`-classified (a definition), which gives fact A by `T.major_levels_whnf`; `RB`, no
iota RHS is a bare constructor-field variable, which makes fact B vacuous. Both hold for the
recursor rules Lean's kernel generates (the major premise has the inductive type itself; the RHS
is the minor premise applied). -/
theorem T.pat_leaf_1a_restricted
    (RA : ∀ {rec : Name} {mm : Nat} {c' : Name} {nn : Nat}
      {r : (Pattern.iota rec mm c' nn).RHS × (Pattern.iota rec mm c' nn).Check} {ci : VConstant}
      {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr},
      Params.Pat (.iota rec mm c' nn) r → Params.env.constants rec = some ci → Hs.length = mm →
      ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj) →
      ∀ k, Params.classify I ≠ some (.symb k))
    (RB : ∀ {rec : Name} {mm : Nat} {c' : Name} {nn : Nat}
      {r : (Pattern.iota rec mm c' nn).RHS × (Pattern.iota rec mm c' nn).Check},
      Params.Pat (.iota rec mm c' nn) r → ∀ x, r.1 ≠ .var (.inr x))
    {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
    (WFIH : LR.WFIH Params.rank Γ₀ k) {c : Name} {ci : VConstant} {ls : List SLevel}
    (hc : Params.rank c < k) (h1 : Params.env.constants c = some ci) (h2 : ls.length = ci.uvars)
    {R : TShape → SExpr → Prop} (LIH : LR.LocalIH Params.rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e)
    {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} {mC : TShape}
    (hP : Params.Pat p r) (hMt : LE_Interp.Matches p c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1) (hchk : r.2 = .true)
    (g : PatGen) (hg : Pattern.gen Params.env Params.rank Params.classify p r.1 = some g)
    (hty : OnCtx (g.self ++ g.ctx)
        (fun Γ A => (Params.env.below Params.rank (Params.rank c)).IsType ci.uvars Γ A) ∧
      (Params.env.below Params.rank (Params.rank c)).HasType ci.uvars (g.self ++ g.ctx) g.rhsAbs
        (g.type.liftN g.self.length))
    (hdef : Params.env.IsDefEq ci.uvars g.ctx g.lhs g.rhs g.type)
    {Ts : List SExpr} {B : SExpr} (hT : mkInst ls ci.type = Ts.foldr .forallE B)
    (hk : rargs.length = Ts.length)
    {ρ : Valuation} {σ σ' : Subst} (hρ : (Valuation.ofRargs rargs).LE ρ)
    (W : LR.SubstWF Γ₀ σ σ' (Ts.reverse ++ Γ₀) ρ)
    {n'} {m a : WShape n'} (le : m.T ≤ mC) (hA : LE_Interp ρ a.T B) (hmem : m.HasType a)
    (tyV : ∀ {τ τ'}, LR.SubstWF Γ₀ τ τ' (Ts.reverse ++ Γ₀) ρ →
      (LR Γ₀).TyDefEq (B.subst τ) (B.subst τ') a) :
    (LR Γ₀).DefEq ((openSpine c ls Ts.length).subst σ) ((openSpine c ls Ts.length).subst σ')
      (B.subst σ) m a := by
  obtain ⟨sp, rfl⟩ := Params.pat_simple hP
  cases sp with
  | iota rec mm c' nn =>
    have hh := T.matches_head hMt
    obtain rfl : rec = c := (Pattern.head_varN rec mm).symm.trans hh
    exact T.pat_leaf_iota WFIH hc h1 h2 LIH hR hP hMt hRHS hchk g hg hty hdef hT hk hρ W le hA
      hmem tyV
      (fun hHs hTc _ _ _ hred => (T.major_levels_whnf (RA hP h1 hHs hTc) hred).2)
      (fun _ _ hroot _ _ _ _ => absurd hroot (RB hP _))
  | defn c₀ =>
    exact T.pat_leaf_delta WFIH hc h1 h2 LIH hR hP hMt hRHS hchk g hg hdef hT hk W le hA hmem tyV

end Lean4Lean.SExpr
