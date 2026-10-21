import Lean4Lean.Experimental.E3.Measure7
namespace Lean4Lean.SExpr
variable [Params]

-- D4 literal const_local (PLAN.md 389-399), Params.rank := RP.rank
example (RP : RankParams) {Γ₀ : List SExpr} {k : Nat} {c₀ : Name}
    (WFIH : ∀ k' < k, ∀ {Γ M N A}, IsDefEqStrong (Params.env.below RP.rank k') Γ M N A →
      ∀ {ρ n} {m a : WShape n}, LE_Interp ρ m.T M → LE_Interp ρ a.T A → m.HasType a →
      LR.Adequate Γ₀ Γ ρ M N A m a)
    (hΓ₀ : ⊢ Γ₀) (hc₀ : RP.rank c₀ < k) :
    ∀ {ρ mT M} (hM : LE_Interp ρ mT M) {c ls ci}, M = .const c ls → RP.rank c ≤ RP.rank c₀ →
      Params.env.constants c = some ci → ls.length = ci.uvars →
      (∃ n, mT = (WShape.bot (n := n)).T) ∨
      ∃ (n : Nat) (m' a' : WShape n), mT ≤ m'.T ∧ m'.HasType a' ∧ LE_Interp ρ a'.T (mkInst ls ci.type) ∧
        ∀ {n'} (m a : WShape n'), m.T ≤ m'.T → LE_Interp ρ a.T (mkInst ls ci.type) → m.HasType a →
          (LR Γ₀).DefEq (.const c ls) (.const c ls) (mkInst ls ci.type) m a :=
  LR.const_local RP WFIH hΓ₀ hc₀

-- PatLeafStmt2.lean const_spine, literally (IsDefEqStrongE E := IsDefEqStrong E, rank := RP.rank)
example (RP : RankParams) {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
    (WFIH : ∀ k' < k, ∀ {Γ M N A}, IsDefEqStrong (Params.env.below RP.rank k') Γ M N A →
      ∀ {ρ n} {m a : WShape n}, LE_Interp ρ m.T M → LE_Interp ρ a.T A → m.HasType a →
        LR.Adequate Γ₀ Γ ρ M N A m a)
    {c : Name} {ci : VConstant} {ls : List SLevel}
    (hc : RP.rank c < k) (h1 : Params.env.constants c = some ci) (h2 : ls.length = ci.uvars)
    {R : TShape → SExpr → Prop}
    (LIH : ∀ m e, R m e → ∀ c' ls' ci', e = .const c' ls' → RP.rank c' = RP.rank c →
      Params.env.constants c' = some ci' → ls'.length = ci'.uvars → LR.ConstGoal Γ₀ ρ₀ m c' ls' ci')
    {n : Nat} {rargs : List (WShape n)} {mC : TShape} (hC : LE_Interp.Const c ls R rargs mC)
    {Ts : List SExpr} {B : SExpr} (hT : mkInst ls ci.type = Ts.foldr .forallE B)
    (hk : rargs.length = Ts.length)
    {ρ : Valuation} {σ σ' : Subst} (hρ : (rargs.foldr (fun x ρ => ρ.push x.T) Valuation.nil).LE ρ)
    (W : LR.SubstWF Γ₀ σ σ' (Ts.reverse ++ Γ₀) ρ)
    {n'} {m a : WShape n'} (le : m.T ≤ mC) (hA : LE_Interp ρ a.T B) (hmem : m.HasType a)
    (tyV : ∀ {τ τ'}, LR.SubstWF Γ₀ τ τ' (Ts.reverse ++ Γ₀) ρ →
      (LR Γ₀).TyDefEq (B.subst τ) (B.subst τ') a) :
    (LR Γ₀).DefEq ((spine (.const c ls) ((List.range Ts.length).reverse.map .bvar)).subst σ)
      ((spine (.const c ls) ((List.range Ts.length).reverse.map .bvar)).subst σ')
      (B.subst σ) m a :=
  LR.const_spine RP WFIH hc h1 h2 LIH hC hT hk hρ W le hA hmem tyV

-- PatLeafStmt2.lean:168 pat_leaf_1a with gen := Pattern.gen
example (RP : RankParams) {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
    (WFIH : LR.WFIH RP.rank Γ₀ k) {c : Name} {ci : VConstant} {ls : List SLevel}
    (hc : RP.rank c < k) (h1 : Params.env.constants c = some ci) (h2 : ls.length = ci.uvars)
    {R : TShape → SExpr → Prop} (LIH : LR.LocalIH RP.rank Γ₀ ρ₀ c R)
    {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} {mC : TShape}
    (hP : Params.Pat p r) (hMt : LE_Interp.Matches p c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1) (hchk : r.2 = .true)
    (g : PatGen) (hg : Pattern.gen Params.env RP.rank Params.classify p r.1 = some g)
    (hty : OnCtx (g.self ++ g.ctx) (fun Γ A => (Params.env.below RP.rank (RP.rank c)).IsType ci.uvars Γ A) ∧
      (Params.env.below RP.rank (RP.rank c)).HasType ci.uvars (g.self ++ g.ctx) g.rhsAbs
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
      (B.subst σ) m a :=
  LR.pat_leaf_1a RP WFIH hc h1 h2 LIH hP hMt hRHS hchk g hg hty hdef hT hk hρ W le hA hmem tyV

-- (a)-(d) at arbitrary m n, used together (callers chain (a) into (b)/(d))
example {env rank classify} {rec c' : Name} {m n : Nat} {r : (Pattern.iota rec m c' n).RHS} {g : PatGen}
    {ci : VConstant} (hg : Pattern.gen env rank classify (.iota rec m c' n) r = some g)
    (hci : env.constants rec = some ci) :
    ∃ (I : Name) (us : List VLevel) (Bmaj : VExpr), g.lhs = .app (VExpr.bvarSpine (.const rec (VLevel.params ci.uvars)) m n)
        (VExpr.bvarSpine (.const c' us) n 0) ∧
      g.type = (Bmaj.liftN n 1).inst (VExpr.bvarSpine (.const c' us) n 0) ∧
      ∃ Hs : List VExpr, ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj) := by
  obtain ⟨Hs, I, us, Bmaj, l, e, -⟩ := Pattern.gen_head hg hci
  exact ⟨I, us, Bmaj, Pattern.gen_lhs hg hci l e, Pattern.gen_type hg hci l e, Hs, e⟩

-- (e) for delta: the any-Pat form at Arity 0 for `.const c`
example {env rank classify} {c : Name} {r : (Pattern.const c).RHS} {g : PatGen} {ci : VConstant}
    (hg : Pattern.gen env rank classify (.const c) r = some g) (hci : env.constants c = some ci) :
    ∃ (Hs : List VExpr) (B : VExpr), Hs.length = 0 ∧ ci.type = Hs.foldr .forallE B :=
  Pattern.gen_arity hg hci .refl
end Lean4Lean.SExpr
