import Lean4Lean.Experimental.E6.Selfs
/-! E6, the delta shape `p = .const c` of the pattern leaf (D4 steps 1-5 with an empty
pattern context: `W_p` is the self entries over `SubstWF.id`). -/
namespace Lean4Lean.SExpr
variable [Params]

theorem T.lowerCtx_nil (ρ : Valuation) : Valuation.lowerCtx [] ρ 0 = .nil := rfl

/-- `W_p` and the RHS interpretation for any rule, given a `SubstWF` of the pattern context
over `lowerCtx` and the inputs of `rhs_lower`: the lowered valuation, the self constants and
the adequacy of the instantiated `rhsAbs`, at a typed `(y', a'')` above any `m ≤ mC` whose raw
interpretation is known. -/
theorem T.rhs_adequate {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
    (WFIH : LR.WFIH Params.rank Γ₀ k) {c : Name} {ci : VConstant} {ls : List SLevel}
    (hc : Params.rank c < k) (h1 : Params.env.constants c = some ci)
    {R : TShape → SExpr → Prop} (LIH : LR.LocalIH Params.rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e)
    {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} {mC : TShape}
    (hP : Params.Pat p r) (hMt : LE_Interp.Matches p c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1)
    (g : PatGen) (hg : Pattern.gen Params.env Params.rank Params.classify p r.1 = some g)
    {fields : List TShape} {ρ : Valuation} {mm : Nat}
    {σc σc' : Subst} (Wc : LR.SubstWF Γ₀ σc σc' (g.ctx.map (mkInst ls) ++ Γ₀)
      (Valuation.lowerCtx fields ρ mm))
    (hvar : ∀ path {n} {y b : WShape n}, y.T ≤ m2 path → y.HasType b →
      LE_Interp (Valuation.lowerCtx fields ρ mm) b.T
        (SExpr.mkInst ls ((g.ctx.getD (p.pathIdx path) (.sort .zero)).liftN (p.pathIdx path + 1))) →
      y.T ≤ Valuation.lowerCtx fields ρ mm (p.pathIdx path))
    (hhead : ∀ path, m2 path ≤ Valuation.lowerCtx fields ρ mm (p.pathIdx path) ∨
      ∃ (I' : Name) (us : List VLevel) (k : Nat), g.ctx[p.pathIdx path]? = some (.const I' us) ∧
        Params.classify I' = some (.indTy k)) :
    ∃ selfs : List TShape,
      let ρl := Valuation.lower selfs fields ρ mm
      let cs := (r.1.selfLeaves (Pattern.sameRank Params.rank p.head)).map (mkInst ls)
      let σp := cs.foldr (fun x τ => τ.cons x) σc
      let σp' := cs.foldr (fun x τ => τ.cons x) σc'
      selfs.length = g.self.length ∧
      LR.SubstWF Γ₀ σp σp' ((g.self ++ g.ctx).map (mkInst ls) ++ Γ₀) ρl ∧
      (∀ i, ρl (g.self.length + i) = Valuation.lowerCtx fields ρ mm i) ∧
      (∀ i, σp (g.self.length + i) = σc i) ∧ (∀ i, σp' (g.self.length + i) = σc' i) ∧
      (∃ u, IsDefEqStrong (Params.env.below Params.rank (Params.rank c))
        ((g.self ++ g.ctx).map (mkInst ls) ++ Γ₀)
        (mkInst ls (g.type.liftN g.self.length)) (mkInst ls (g.type.liftN g.self.length)) (.sort u)) ∧
      ((∀ path, r.1 = .var path → m2 path ≤ Valuation.lowerCtx fields ρ mm (p.pathIdx path)) →
        LE_Interp ρl mC (mkInst ls g.rhsAbs)) ∧
      (∀ {n₁} {y a : WShape n₁}, LE_Interp ρl y.T (mkInst ls g.rhsAbs) →
        LE_Interp ρl a.T (mkInst ls (g.type.liftN g.self.length)) → y.HasType a →
        (LR Γ₀).DefEq (r.1.applyS ls fun path => σc (p.pathIdx path))
          (r.1.applyS ls fun path => σc' (p.pathIdx path))
          ((mkInst ls (g.type.liftN g.self.length)).subst σp) y a ∧
        (LR Γ₀).TyDefEq ((mkInst ls (g.type.liftN g.self.length)).subst σp)
          ((mkInst ls (g.type.liftN g.self.length)).subst σp) a) ∧
      (∀ {n₁} {y : WShape n₁}, LE_Interp ρl y.T (mkInst ls g.rhsAbs) →
        InterpTyped ρl y.T (mkInst ls g.rhsAbs) (mkInst ls (g.type.liftN g.self.length))) := by
  have hhd : p.head = c := T.matches_head hMt
  have hci : Params.env.constants p.head = some ci := hhd ▸ h1
  obtain ⟨selfs, hlen, hfacts, hraw⟩ := T.rhs_lower2 LIH hR hP hMt hRHS g hg Wc.fits
    hvar hhead
  have hgs := Pattern.gen_self hg
  have Wp0 := T.cons_selfs (ρ₀ := ρ₀) WFIH hc Wc g.self
    (r.1.selfLeaves (Pattern.sameRank Params.rank p.head)) selfs hlen.symm (hgs.1.symm.trans hlen.symm)
    (fun j S e s hS he hs => by
      obtain ⟨c', us, ci', he', hrk, hci', hl, hT, hty, hcg, -⟩ := hfacts j s hs
      cases he.symm.trans he'
      have hgetD : g.self.getD j (.sort .zero) = S := by simp [List.getD_eq_getElem?_getD, hS]
      exact ⟨c', us, ci', rfl, hrk, hci', hl, hgetD ▸ hT, hty, hcg⟩)
  have hΓ : (g.self ++ g.ctx).map (mkInst ls) ++ Γ₀ = g.self.map (mkInst ls) ++ (g.ctx.map (mkInst ls) ++ Γ₀) := by
    simp
  rw [← hΓ] at Wp0
  have hcsl : ((r.1.selfLeaves (Pattern.sameRank Params.rank p.head)).map (mkInst ls)).length =
      g.self.length := by simp [hgs.1]
  have hshiftσ : ∀ (τ : Subst) i, ((r.1.selfLeaves (Pattern.sameRank Params.rank p.head)).map
      (mkInst ls)).foldr (fun x τ => τ.cons x) τ (g.self.length + i) = τ i := by
    intro τ i
    rw [← hcsl]
    generalize (r.1.selfLeaves (Pattern.sameRank Params.rank p.head)).map (mkInst ls) = cs
    induction cs with
    | nil => simp
    | cons x cs ih => rw [List.length_cons, Nat.add_right_comm]; exact ih
  have hselfσ : ∀ (τ : Subst) (j : Nat) (e : VExpr),
      (r.1.selfLeaves (Pattern.sameRank Params.rank p.head))[j]? = some e →
      ((r.1.selfLeaves (Pattern.sameRank Params.rank p.head)).map
        (mkInst ls)).foldr (fun x τ => τ.cons x) τ j = mkInst ls e := by
    intro τ j e he
    generalize r.1.selfLeaves (Pattern.sameRank Params.rank p.head) = es at he
    induction es generalizing j with
    | nil => simp at he
    | cons x es ih =>
      cases j with
      | zero => simp at he; subst he; rfl
      | succ j => exact ih j (by simpa using he)
  have hρshift : ∀ i, Valuation.lower selfs fields ρ mm (g.self.length + i) =
      Valuation.lowerCtx fields ρ mm i := fun i => by rw [← hlen]; exact T.foldr_push_add _ selfs i
  -- the strong typing of `rhsAbs` and of its type
  have Hrhs := (EnvStrongR.of_params.rhs ls hP hg hci).weak_append (Γ₀ := Γ₀)
  rw [hhd] at Hrhs
  obtain ⟨u, Hty⟩ := Hrhs.isType'
  have hAbsσ : ∀ (σc₀ : Subst), (mkInst ls g.rhsAbs).subst
      (((r.1.selfLeaves (Pattern.sameRank Params.rank p.head)).map (mkInst ls)).foldr
        (fun x τ => τ.cons x) σc₀) = r.1.applyS ls fun path => σc₀ (p.pathIdx path) := by
    intro σc₀
    exact Pattern.gen_rhsAbs hg ls _ _ (fun j e he => hselfσ σc₀ j e he)
      (fun path => hshiftσ σc₀ _)
  refine ⟨selfs, hlen, Wp0, hρshift, hshiftσ σc, hshiftσ σc', ⟨u, Hty⟩, hraw, ?_, ?_⟩
  · intro n₁ y a hy ha hya
    have A := (WFIH _ hc Hrhs hy ha hya).1 Wp0
    rw [hAbsσ, hAbsσ] at A
    refine ⟨A.1, ?_⟩
    obtain ⟨n₂, a₂, s, le_n, le_a, hA', hS, hmem'⟩ :=
      ((LE_Interp.soundSE (Params.env.below_le ..) Hty Wp0.fits).2 ha).out
    have tyDE := (WFIH _ hc Hty hA' hS hmem').2 Wp0.left
    exact LR.toValTy le_n le_a hya.isType hS hmem' tyDE
  · intro n₁ y hy
    exact (LE_Interp.soundSE (Params.env.below_le ..) Hrhs Wp0.fits).2 hy

end Lean4Lean.SExpr

namespace Lean4Lean.SExpr
variable [Params]

/-- The delta shape of the pattern leaf: `p = .const c` (`ctx = []`, no pattern variables). -/
theorem T.pat_leaf_delta {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
    (WFIH : LR.WFIH Params.rank Γ₀ k) {c : Name} {ci : VConstant} {ls : List SLevel}
    (hc : Params.rank c < k) (h1 : Params.env.constants c = some ci) (h2 : ls.length = ci.uvars)
    {R : TShape → SExpr → Prop} (LIH : LR.LocalIH Params.rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e)
    {c₀ : Name} {r : (Pattern.const c₀).RHS × (Pattern.const c₀).Check} {n : Nat}
    {rargs : List (WShape n)}
    {m2 : (Pattern.const c₀).Path → TShape} {mC : TShape}
    (hP : Params.Pat (.const c₀) r) (hMt : LE_Interp.Matches (.const c₀) c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1) (hchk : r.2 = .true)
    (g : PatGen) (hg : Pattern.gen Params.env Params.rank Params.classify (.const c₀) r.1 = some g)
    (hdef : Params.env.IsDefEq ci.uvars g.ctx g.lhs g.rhs g.type)
    {Ts : List SExpr} {B : SExpr} (hT : mkInst ls ci.type = Ts.foldr .forallE B)
    (hk : rargs.length = Ts.length)
    {ρ : Valuation} {σ σ' : Subst}
    (W : LR.SubstWF Γ₀ σ σ' (Ts.reverse ++ Γ₀) ρ)
    {n'} {m a : WShape n'} (le : m.T ≤ mC) (hA : LE_Interp ρ a.T B) (hmem : m.HasType a)
    (tyV : ∀ {τ τ'}, LR.SubstWF Γ₀ τ τ' (Ts.reverse ++ Γ₀) ρ →
      (LR Γ₀).TyDefEq (B.subst τ) (B.subst τ') a) :
    (LR Γ₀).DefEq ((openSpine c ls Ts.length).subst σ) ((openSpine c ls Ts.length).subst σ')
      (B.subst σ) m a := by
  cases hMt
  cases Ts with
  | cons => cases hk
  | nil => ?_
  simp only [List.foldr_nil] at hT; subst hT
  obtain ⟨ci₀, h1₀, hctx, hlhs, htype⟩ := Pattern.gen_delta hg
  cases h1.symm.trans h1₀
  have hcl : (mkInst ls ci.type).ClosedN := (Params.henv.closedC h1).mkInstS
  have hΓ₀ := W.wf₀
  have Wc : LR.SubstWF Γ₀ .id .id (g.ctx.map (mkInst ls) ++ Γ₀) (Valuation.lowerCtx [] ρ 0) := by
    rw [hctx, T.lowerCtx_nil]; exact .id hΓ₀
  obtain ⟨selfs, -, Wp, -, -, -, -, hraw, hadeq, hsound⟩ :=
    T.rhs_adequate WFIH hc h1 LIH hR hP (n := n) (rargs := []) LE_Interp.Matches.const hRHS g hg Wc
      (fun path => path.elim) (fun path => path.elim)
  have hraw := hraw fun path => path.elim
  obtain ⟨n'', y', a'', -, hmy, hy, ha'', hya⟩ := (hsound (hraw.mono le) :).out
  have hcl' : ∀ j, (mkInst ls (g.type.liftN j)) = mkInst ls ci.type := fun j => by
    rw [htype, (Params.henv.closedC h1).liftN_eq (Nat.zero_le _)]
  obtain ⟨H, hTy''⟩ := hadeq hy ha'' hya
  simp only [hcl', hcl.subst_eq .zero] at H hTy''
  -- type validity at the goal's `a`
  have hTy : (LR Γ₀).TyDefEq (mkInst ls ci.type) (mkInst ls ci.type) a := by
    have := tyV W.left; rwa [hcl.subst_eq .zero] at this
  -- compatibility: both interpret the closed type
  have hc' : a.T.Compat a''.T :=
    LE_Interp.compat hA ((LE_Interp.closed_iff hcl).1 (by rw [← hcl' g.self.length]; exact ha''))
  have H' := T.retype hΓ₀ hmy hmem hya hc' hTy hTy'' H
  -- the typed delta step
  let e0 : (Pattern.const c).Path → SExpr := fun x => x.elim
  have hfun : ∀ f : (Pattern.const c).Path → SExpr, f = e0 := fun f => funext fun x => x.elim
  rw [hfun (fun path => Subst.id ((Pattern.const c).pathIdx path))] at H'
  have hred : TWHRedS Γ₀ (.const c ls) (r.1.applyS ls e0) (mkInst ls ci.type) := by
    refine ⟨?_, .tail .rfl (T.extra_true hP hchk (Pattern.MatchesS.congr .const
      fun x => x.elim))⟩
    rw [hctx] at hdef
    have Hd := (T.strong_env_defeq (Γ := []) trivial hdef ls).weak0 (Γ := Γ₀) |>.defeq
    rw [hlhs, htype] at Hd
    have e1 : mkInst ls (.const c (VLevel.params ci.uvars)) = .const c ls := by
      simp only [mkInst, SLevel.instV_params h2]
    have e2 : mkInst ls g.rhs = r.1.applyS ls e0 := by
      have := Pattern.gen_rhs hg ls e0 .id (fun path => path.elim)
      rwa [subst_id] at this
    rw [e1, e2] at Hd; exact Hd
  simp only [List.length_nil, openSpine, List.range_zero, List.reverse_nil, List.map_nil, spine_nil,
    SExpr.subst, hcl.subst_eq .zero]
  exact ((LR Γ₀).whr hred hred).2 H'

end Lean4Lean.SExpr
