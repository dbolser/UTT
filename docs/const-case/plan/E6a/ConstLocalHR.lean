import Lean4Lean.Experimental.E6a.FieldLower
/-! Verifier: `const_local` still goes through when `const_spine` also takes `hR` (h7). -/
namespace Lean4Lean.SExpr
variable [Params]
theorem V.const_spine' (RP : RankParams) {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
    (WFIH : LR.WFIH RP.rank Γ₀ k) {c : Name} {ci : VConstant} {ls : List SLevel}
    (hc : RP.rank c < k) (h1 : Params.env.constants c = some ci) (h2 : ls.length = ci.uvars)
    {R : TShape → SExpr → Prop} (LIH : LR.LocalIH RP.rank Γ₀ ρ₀ c R) (hR : ∀ m e, R m e → LE_Interp ρ₀ m e)
    {n : Nat} {rargs : List (WShape n)} {mC : TShape} (hC : LE_Interp.Const c ls R rargs mC)
    {Ts : List SExpr} {B : SExpr} (hT : mkInst ls ci.type = Ts.foldr .forallE B)
    (hk : rargs.length = Ts.length)
    {ρ : Valuation} {σ σ' : Subst} (hρ : (Valuation.ofRargs rargs).LE ρ)
    (W : LR.SubstWF Γ₀ σ σ' (Ts.reverse ++ Γ₀) ρ)
    {n'} {m a : WShape n'} (le : m.T ≤ mC) (hA : LE_Interp ρ a.T B) (hmem : m.HasType a)
    (tyV : ∀ {τ τ'}, LR.SubstWF Γ₀ τ τ' (Ts.reverse ++ Γ₀) ρ →
      (LR Γ₀).TyDefEq (B.subst τ) (B.subst τ') a) :
    (LR Γ₀).DefEq ((openSpine c ls Ts.length).subst σ) ((openSpine c ls Ts.length).subst σ')
      (B.subst σ) m a := by
  sorry -- stub: const_spine with hR added (verifier scratch)

/-- `LR.const_local` (PLAN D4): induction on `hM` through the `R`-closure. Its only recursive
calls are the local IH on the `Const` premise's sub-derivations (`ih7`) and the WF IH at
`rank c ≤ rank c₀ < k` (type validity, `tyV`); the rest is `LR.const_spine` at `rargs = []`. -/
theorem V.const_local' (RP : RankParams) {Γ₀ : List SExpr} {k : Nat} {c₀ : Name}
    (WFIH : LR.WFIH RP.rank Γ₀ k) (hΓ₀ : ⊢ Γ₀) (hc₀ : RP.rank c₀ < k) :
    ∀ {ρ mT M} (_hM : LE_Interp ρ mT M) {c ls ci}, M = .const c ls → RP.rank c ≤ RP.rank c₀ →
      Params.env.constants c = some ci → ls.length = ci.uvars → LR.ConstGoal Γ₀ ρ mT c ls ci := by
  intro ρ mT M hM
  induction hM with
  | bot => intro _ _ _ _ _ _ _; exact .inl ⟨_, rfl⟩
  | @const _ c' ci' mT₀ m' ρ a ls' R h1 h2 h3 h4 h5 h6 h7 _ ih7 =>
    intro c ls ci eM hrk hci hlen
    injection eM with e1 e2; subst c' ls'
    have e3 := Option.some.inj (h1.symm.trans hci); subst ci'
    have hk : RP.rank c < k := Nat.lt_of_le_of_lt hrk hc₀
    -- (i) the local IH: same-rank bare-constant leaves of `R`, from `ih7` (strict sub-derivations)
    have LIH : LR.LocalIH RP.rank Γ₀ ρ c R := fun me e hR c'' ls'' ci'' he hr h1'' h2'' =>
      ih7 me e hR he (hr ▸ hrk) h1'' h2''
    -- (ii) type validity: the WF IH at `rank c < k` on `EnvStrongR.const`
    have hcl : (mkInst ls ci.type).ClosedN := (Params.henv.closedC hci).mkInstS
    have tyV : ∀ {n} {a₁ : WShape n}, LE_Interp .nil a₁.T (mkInst ls ci.type) →
        a₁.HasType .type → (LR Γ₀).TyDefEq (mkInst ls ci.type) (mkInst ls ci.type) a₁ := by
      intro n a₁ hA ha
      obtain ⟨u, Hty₀⟩ := (EnvStrongR.of_params RP).const ls hci
      have Hty := Hty₀.weak0 (Γ := Γ₀)
      obtain ⟨n', a', s, le_n, le_a, hA', hS, hmem'⟩ :=
        ((LE_Interp.soundSE (Params.env.below_le ..) Hty (LR.SubstWF.id hΓ₀).fits).2 hA).out
      have tyDE := (WFIH _ hk Hty hA' hS hmem').2 (LR.SubstWF.id hΓ₀)
      simp only [subst_id] at tyDE
      exact LR.toValTy le_n le_a ha hS hmem' tyDE
    -- (iii) the typed upper bound `m'` of the `const` node, lifted to a common level
    refine .inr ?_
    have hK1 : m'.1 ≤ max m'.1 a.1 := Nat.le_max_left ..
    have hK2 : a.1 ≤ max m'.1 a.1 := Nat.le_max_right ..
    refine ⟨max m'.1 a.1, m'.2.lift _, a.2.lift _, h3.trans (TShape.lift_eqv hK1).2,
      (TShape.HasType.def hK1 hK2).1 h4, h5.lift hK2, ?_⟩
    intro n' m₁ a₁ hle hA₁ hmem₁
    -- (iv) the spine lemma at `rargs = []`, `ρ = .nil`, `W = SubstWF.id`
    have H := V.const_spine' RP WFIH hk hci hlen LIH h7 h6 (Ts := []) (B := mkInst ls ci.type) rfl rfl
      Valuation.LE.rfl (LR.SubstWF.id hΓ₀) (hle.trans (TShape.lift_eqv hK1).1)
      ((LE_Interp.closed_iff hcl).1 hA₁) hmem₁ fun _ => by
        rw [hcl.subst_eq .zero, hcl.subst_eq .zero]
        exact tyV ((LE_Interp.closed_iff hcl).1 hA₁) hmem₁.isType
    simpa only [openSpine, List.length_nil, List.range_zero, List.reverse_nil, List.map_nil,
      spine_nil, subst_id] using H
  | _ => intro _ _ _ eM; cases eM

end Lean4Lean.SExpr
#print axioms Lean4Lean.SExpr.V.const_local'
