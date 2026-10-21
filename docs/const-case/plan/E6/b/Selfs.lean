import Lean4Lean.Experimental.E6.Lower
/-! E6 step 1 (self part): the self entries of `W_p`, pushed by `Adequate.cons` over any
`SubstWF` of the pattern context, from `rhs_lower`'s self facts. -/
namespace Lean4Lean.SExpr
variable [Params]

/-- One self entry: the typed bound `x : b` of `rhs_lower`, the constant itself on both sides. -/
theorem T.cons_self {Γ₀ Δ : List SExpr} {k : Nat} (WFIH : LR.WFIH Params.rank Γ₀ k)
    {c : Name} (hc : Params.rank c < k) {ρ₀ : Valuation} {ls : List SLevel}
    {S e : VExpr} {s : TShape} {c' : Name} {us : List VLevel} {ci' : VConstant}
    (he : e = .const c' us) (hrk : Params.rank c' = Params.rank c)
    (hci' : Params.env.constants c' = some ci') (hlen : us.length = ci'.uvars)
    (hS : mkInst ls S = mkInst (us.map (SLevel.instV ls)) ci'.type)
    (hty : ∃ (kk : Nat) (x b : WShape kk), s = x.T ∧ x.HasType b ∧
      LE_Interp ρ₀ b.T (mkInst (us.map (SLevel.instV ls)) ci'.type))
    (hcg : LR.ConstGoal Γ₀ ρ₀ s c' (us.map (SLevel.instV ls)) ci')
    {σ σ' : Subst} {ρ : Valuation} (W : LR.SubstWF Γ₀ σ σ' Δ ρ) :
    LR.SubstWF Γ₀ (σ.cons (mkInst ls e)) (σ'.cons (mkInst ls e)) (mkInst ls S :: Δ) (ρ.push s) := by
  subst he
  obtain ⟨kk, x, b, rfl, hxb, hb⟩ := hty
  have hcl : (mkInst (us.map (SLevel.instV ls)) ci'.type).ClosedN :=
    (Params.henv.closedC hci').mkInstS
  obtain ⟨u, Hu⟩ := EnvStrongR.of_params.const (us.map (SLevel.instV ls)) hci'
  rw [hrk] at Hu
  rw [hS]
  have hx : Γ₀ ⊢ mkInst ls (.const c' us) ≡ mkInst ls (.const c' us) :
      mkInst (us.map (SLevel.instV ls)) ci'.type :=
    IsDefEq.const hci' (by simpa using hlen)
  have hv : (LR Γ₀).DefEq (mkInst ls (.const c' us)) (mkInst ls (.const c' us))
      (mkInst (us.map (SLevel.instV ls)) ci'.type) x b := by
    rcases hcg with ⟨n, hn⟩ | ⟨n, m', a', hle, -, -, H⟩
    · cases show x = .bot from TShape.le_bot.1 (hn ▸ TShape.bot_le')
      exact (LR _).bot hxb.isType
    · exact H x b hle hb hxb
  exact T.cons_closed WFIH hc Hu.weak0 hcl hxb ((LE_Interp.closed_iff hcl).1 hb) hx hv W

/-- The self entries, as a list induction (`Ss` = the self types, `es` = the self leaves,
`sl` = the shapes `selfs`). -/
theorem T.cons_selfs {Γ₀ Δ : List SExpr} {k : Nat} (WFIH : LR.WFIH Params.rank Γ₀ k)
    {c : Name} (hc : Params.rank c < k) {ρ₀ : Valuation} {ls : List SLevel}
    {σ σ' : Subst} {ρ : Valuation} (W : LR.SubstWF Γ₀ σ σ' Δ ρ) :
    ∀ (Ss es : List VExpr) (sl : List TShape), Ss.length = sl.length → es.length = sl.length →
    (∀ (j : Nat) (S e : VExpr) (s : TShape), Ss[j]? = some S → es[j]? = some e → sl[j]? = some s →
      ∃ (c' : Name) (us : List VLevel) (ci' : VConstant), e = VExpr.const c' us ∧
        Params.rank c' = Params.rank c ∧ Params.env.constants c' = some ci' ∧
        us.length = ci'.uvars ∧ mkInst ls S = mkInst (us.map (SLevel.instV ls)) ci'.type ∧
        (∃ (kk : Nat) (x b : WShape kk), s = x.T ∧ x.HasType b ∧
          LE_Interp ρ₀ b.T (mkInst (us.map (SLevel.instV ls)) ci'.type)) ∧
        LR.ConstGoal Γ₀ ρ₀ s c' (us.map (SLevel.instV ls)) ci') →
    LR.SubstWF Γ₀ ((es.map (mkInst ls)).foldr (fun x τ => τ.cons x) σ)
      ((es.map (mkInst ls)).foldr (fun x τ => τ.cons x) σ')
      (Ss.map (mkInst ls) ++ Δ) (sl.foldr (fun x ρ' => ρ'.push x) ρ)
  | [], [], [], _, _, _ => W
  | S :: Ss, e :: es, s :: sl, h1, h2, H => by
    have IH := T.cons_selfs WFIH hc (ρ₀ := ρ₀) W Ss es sl (by simpa using h1) (by simpa using h2)
      fun j S' e' s' a b c => H (j+1) S' e' s' (by simpa using a) (by simpa using b)
        (by simpa using c)
    obtain ⟨c', us, ci', he, hrk, hci', hlen, hS, hty, hcg⟩ := H 0 S e s rfl rfl rfl
    exact T.cons_self WFIH hc he hrk hci' hlen hS hty hcg IH
  | [], _ :: _, _, h1, h2, _ | _ :: _, [], _, h1, h2, _ | [], [], _ :: _, h1, h2, _
  | _ :: _, _ :: _, [], h1, h2, _ => by simp at h1 h2 <;> omega

end Lean4Lean.SExpr
