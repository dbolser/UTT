import Lean4Lean.Experimental.E6a.FieldLower
/-! E6 (PLAN D4 "RHS step" steps 1-6, as amended by E6a): generic helpers for the pattern leaf. -/
namespace Lean4Lean.SExpr
variable [Params]

/-- `T.strong_env` for a defeq (not only a typing). -/
theorem T.strong_env_defeq {U : Nat} {Γ : List VExpr} {e e' A : VExpr}
    (hΓ : OnCtx Γ (fun Γ A => Params.env.IsType U Γ A))
    (H : Params.env.IsDefEq U Γ e e' A) (ls : List SLevel) :
    IsDefEqStrong Params.env (Γ.map (mkInst ls)) (mkInst ls e) (mkInst ls e') (mkInst ls A) := by
  obtain ⟨vs, hvs, rfl⟩ := SLevel.exists_map_mk ls
  have hS := (VEnv.IsDefEq.strong Params.henv hΓ H).instL hvs
  have := hS.mkSE (CtorProviderE.synE VEnv.LE.rfl) (onCtx_map_instL_levelWF hvs Γ)
  have hctx : Γ.map (mkInst (vs.map SLevel.mk)) = (Γ.map (VExpr.instL vs)).map SExpr.mk := by
    rw [List.map_map]; congr 1; funext B; exact mkInst_map_mk hvs
  rw [hctx, mkInst_map_mk hvs, mkInst_map_mk hvs, mkInst_map_mk hvs]
  exact this

theorem T.substWF_len {Γ₀ Γ : List SExpr} {σ σ' : Subst} {ρ : Valuation}
    (W : LR.SubstWF Γ₀ σ σ' Γ ρ) : Γ₀.length ≤ Γ.length := by
  induction W with
  | id => exact Nat.le_refl _
  | cons _ _ _ _ _ _ ih => simp only [List.length_cons]; omega

/-- A `SubstWF` whose source context is as long as its target context is the identity. -/
theorem T.substWF_self {Γ₀ Γ : List SExpr} {σ σ' : Subst} {ρ : Valuation}
    (W : LR.SubstWF Γ₀ σ σ' Γ ρ) (hl : Γ.length = Γ₀.length) : σ = .id ∧ σ' = .id := by
  cases W with
  | id => exact ⟨rfl, rfl⟩
  | cons W' =>
    have := T.substWF_len W'
    simp only [List.length_cons] at hl; omega

/-- Retyping a `DefEq` from `(y, a')` down to `(m, a)` along a join of compatible type shapes:
`LR.Adequate.mono_r` at the identity substitution (`Γ = Γ₀`, `ρ = .nil`). -/
theorem T.retype {Γ₀ : List SExpr} (hΓ₀ : ⊢ Γ₀) {M N A : SExpr} {n n' : Nat} {m a : WShape n}
    {y a' : WShape n'} (le : m.T ≤ y.T) (hm : m.HasType a) (hy : y.HasType a')
    (hc : a.T.Compat a'.T) (hA : (LR Γ₀).TyDefEq A A a) (hA' : (LR Γ₀).TyDefEq A A a')
    (H : (LR Γ₀).DefEq M N A y a') : (LR Γ₀).DefEq M N A m a := by
  have hid : ∀ {σ σ' ρ}, LR.SubstWF Γ₀ σ σ' Γ₀ ρ → σ = .id ∧ σ' = .id :=
    fun W => T.substWF_self W rfl
  have Had : LR.Adequate Γ₀ Γ₀ .nil M N A y a' := by
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩
    · obtain ⟨rfl, rfl⟩ := hid W
      simp only [subst_id]; exact ⟨(LR Γ₀).left H, (LR Γ₀).left ((LR Γ₀).symm H)⟩
    · obtain ⟨rfl, -⟩ := hid W
      simp only [subst_id]; exact H
  have hT : ∀ {k : Nat} {b : WShape k}, (LR Γ₀).TyDefEq A A b →
      ∀ {{σ σ'}}, LR.SubstWF Γ₀ σ σ' Γ₀ .nil → (LR Γ₀).TyDefEq (A.subst σ) (A.subst σ) b :=
    fun h σ σ' W => by obtain ⟨rfl, -⟩ := hid W; simp only [subst_id]; exact h
  have := (LR.Adequate.mono_r le hm hy hc (hT hA) (hT hA') Had).2 (LR.SubstWF.id hΓ₀)
  simpa only [subst_id] using this

/-- `Adequate.cons` for a closed entry type, with its rank-bounded strong typing in the current
context (the WF IH at `rank c < k` supplies `ihA`). -/
theorem T.cons_closed {Γ₀ Γ : List SExpr} {k : Nat} (WFIH : LR.WFIH Params.rank Γ₀ k)
    {c : Name} (hc : Params.rank c < k) {A : SExpr} {u : SLevel}
    (HA : IsDefEqStrong (Params.env.below Params.rank (Params.rank c)) Γ A A (.sort u))
    (hcl : A.ClosedN) {kk : Nat} {a₁ p : WShape kk} {x x' : SExpr} {σ σ' : Subst} {ρ : Valuation}
    (hp : p.HasType a₁) (hA₁ : LE_Interp ρ a₁.T A)
    (hx : Γ₀ ⊢ x ≡ x' : A) (hv : (LR Γ₀).DefEq x x' A p a₁)
    (W : LR.SubstWF Γ₀ σ σ' Γ ρ) :
    LR.SubstWF Γ₀ (σ.cons x) (σ'.cons x') (A :: Γ) (ρ.push p.T) := by
  have hs : A.subst σ = A := hcl.subst_eq .zero
  refine LR.Adequate.cons (fun hm ha hmem => WFIH _ hc HA hm ha hmem)
    (HA.mono (Params.env.below_le ..)) hp hA₁ (by rw [hs]; exact hx) (by rw [hs]; exact hv) W

/-- `extra` when the rule has no side conditions (`Measure7-b.lean: WHRed.extra_true`). -/
theorem T.extra_true {Γ : List SExpr} {p : Pattern} {r : p.RHS × p.Check} {e : SExpr}
    {m1 : List SLevel} {m2 : p.Path → SExpr} (hP : Params.Pat p r) (hck : r.2 = .true)
    (hm : p.MatchesS e m1 m2) : Γ ⊢ e ⤳ r.1.applyS m1 m2 :=
  WHRed.extra hP hm (dfs := []) (by rw [hck]; rfl) nofun

end Lean4Lean.SExpr
