import Lean4Lean.Experimental.E6.IotaData
/-! E6: the pattern leaf for an iota rule `rec x₁ … xₘ (c' z₁ … zₖ)` (PLAN D4 "RHS step"),
given the two facts `hgapI`/`hgapF` that the landed `Params` does not provide (see
`T.pat_leaf_gap` in `PatLeaf.lean`). Steps, as in the proof: I1 the iota data (`gen_head_ctor`,
`ctor_fields_closed`, `hT`); I2 invert `W` at the major; I3 the major's ctor clause (lifted to a
level with field level ≥ 1; `hgapI` makes the major domain a whnf, so the clause's levels are the
pattern's); I4 the lowered field entries and `Wc` (`T.substWF_push` over `W`'s tail); I5
`hvar`/`hhead`; I6a (d) and the type transfer to `ρ` (`T.ctor_spine_le`); I6 the RHS root is
interpreted at `ρ_low` (at a bare non-Prop field root through `T.le_indTy_of_compat`; `hgapF`);
I7 `T.rhs_core`; I8 type validity of `B` from the WF IH; I9 `σ` with the major replaced; I10 typed
head reductions (`WHRedS.major`, `WHRed.extra'`, `pat_defeq` through `IsDefEq.subst`) and
`T.finish`. -/
namespace Lean4Lean.SExpr
variable [Params]

theorem T.pat_leaf_iota {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
    (WFIH : LR.WFIH Params.rank Γ₀ k) {c : Name} {ci : VConstant} {ls : List SLevel}
    (hc : Params.rank c < k) (h1 : Params.env.constants c = some ci) (h2 : ls.length = ci.uvars)
    {R : TShape → SExpr → Prop} (LIH : LR.LocalIH Params.rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e)
    {c₀ c' : Name} {mm kf : Nat}
    {r : (Pattern.iota c₀ mm c' kf).RHS × (Pattern.iota c₀ mm c' kf).Check} {n : Nat}
    {rargs : List (WShape n)} {m2 : (Pattern.iota c₀ mm c' kf).Path → TShape} {mC : TShape}
    (hP : Params.Pat (.iota c₀ mm c' kf) r) (hMt : LE_Interp.Matches (.iota c₀ mm c' kf) c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1) (hchk : r.2 = .true)
    (g : PatGen)
    (hg : Pattern.gen Params.env Params.rank Params.classify (.iota c₀ mm c' kf) r.1 = some g)
    {Ts : List SExpr} {B : SExpr} (hT : mkInst ls ci.type = Ts.foldr .forallE B)
    (hk : rargs.length = Ts.length)
    {ρ : Valuation} {σ σ' : Subst} (hρ : (Valuation.ofRargs rargs).LE ρ)
    (W : LR.SubstWF Γ₀ σ σ' (Ts.reverse ++ Γ₀) ρ)
    {n'} {m a : WShape n'} (le : m.T ≤ mC) (hA : LE_Interp ρ a.T B) (hmem : m.HasType a)
    (tyV : ∀ {τ τ'}, LR.SubstWF Γ₀ τ τ' (Ts.reverse ++ Γ₀) ρ →
      (LR Γ₀).TyDefEq (B.subst τ) (B.subst τ') a)
    -- the two missing facts (E6's gap; see `T.pat_leaf_gap`)
    (hgapI : ∀ {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr},
      ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj) → Hs.length = mm →
      ∀ j, Params.classify I ≠ some (.symb j))
    (hgapF : ∀ x, r.1 = .var (.inr x) → ∀ (I₀ : Name) (vs : List VLevel) (ciI : VConstant)
      (u : VLevel), g.ctx[(Pattern.iota c₀ mm c' kf).pathIdx (.inr x)]? = some (.const I₀ vs) →
      Params.env.constants I₀ = some ciI → ciI.type = .sort u → ∀ ns, (u.inst vs).eval ns ≠ 0) :
    (LR Γ₀).DefEq ((openSpine c ls Ts.length).subst σ) ((openSpine c ls Ts.length).subst σ')
      (B.subst σ) m a := by
  -- I1: the iota data
  have hhd : c = c₀ := by
    have := T.matches_head hMt
    simp only [Pattern.head, Pattern.head_varN] at this; exact this.symm
  subst hhd
  have hMt0 := hMt
  have hρ0 := hρ
  cases hMt with
  | app hmf hma => ?_
  rename_i n₀ rs_rec c'' rs' mf ma
  have hc'' : c' = c'' := by
    have := T.matches_head hma; rw [Pattern.head_varN] at this; exact this
  subst hc''
  obtain ⟨lf, hxf⟩ := T.matches_varN mm hmf
  obtain ⟨la, hxa⟩ := T.matches_varN kf hma
  obtain ⟨Hs, I, us, Bmaj, hHs, hcty, ci', I', Tsc, args, hci', hcl', hTsc, hI', hcity, hctx⟩ :=
    Pattern.gen_head_ctor hg h1
  obtain ⟨I'', Ts', hcity', hall⟩ := Params.ctor_fields_closed (cl := .ctor kf) rfl hcl' hci'
  have hTT : Tsc = Ts' := T.foldr_forallE_inj' (T.foldr_app_ne_forallE _ _ args)
    (fun _ _ h => by cases h) (hcity.symm.trans hcity')
  subst hTT
  have hlenTs : Ts.length = mm + 1 := by simp [lf] at hk; omega
  have hT' : mkInst ls ci.type = (Hs.map (mkInst ls) ++ [SExpr.const I (us.map (SLevel.instV ls))]).foldr
      .forallE (mkInst ls Bmaj) := by
    rw [hcty, mkInst_foldr_forallE, List.foldr_append]; rfl
  obtain ⟨rfl, rfl⟩ := T.sfoldr_forallE_inj (by simp [hHs, hlenTs]) (hT.symm.trans hT')
  -- I2: invert `W` at the major
  have hW : LR.SubstWF Γ₀ σ σ' (SExpr.const I (us.map (SLevel.instV ls)) ::
      ((Hs.map (mkInst ls)).reverse ++ Γ₀)) ρ := by
    simpa only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.cons_append, List.nil_append] using W
  generalize eΓ : (SExpr.const I (us.map (SLevel.instV ls)) ::
      ((Hs.map (mkInst ls)).reverse ++ Γ₀)) = Γ' at hW
  cases hW with
  | id h => have := congrArg List.length eΓ; simp at this; omega
  | cons Wt h1W h2W h3W hAW h0 => ?_
  injection eΓ with eA eΓt
  subst eA eΓt
  rename_i ρt a₀ u₀ x₀
  -- I3: the major's ctor clause
  have hdomcl : (SExpr.const I (us.map (SLevel.instV ls))).ClosedN := trivial
  have hraw : (WShape.ctor' c' rs'.reverse).T ≤ x₀ := hρ 0
  obtain ⟨N, hN⟩ : ∃ N, N = max (max x₀.1 a₀.1) n₀ := ⟨_, rfl⟩
  have hNx : x₀.1 ≤ N + 2 := by omega
  have hNa : a₀.1 ≤ N + 2 := by omega
  have hNn : n₀ ≤ N + 1 := by omega
  have hma₀ : (x₀.2.lift (N+2)).HasType (a₀.2.lift (N+2)) := (TShape.HasType.def hNx hNa).1 h3W
  have hAa : LE_Interp (ρt.push x₀) (a₀.2.lift (N+2)).T (SExpr.const I (us.map (SLevel.instV ls))).lift :=
    LE_Interp.weak (h2W.lift hNa)
  have hbv : LE_Interp (ρt.push x₀) (x₀.2.lift (N+2)).T (.bvar 0) := .bvar (TShape.lift_eqv hNx).1
  have D₀ := (h0.2 _ hAa).2 hbv hma₀
  -- the major's shape is a ctor shape
  obtain ⟨hstr, hctoreq⟩ := T.ctor'_eq_ctor hcl' (rs'.reverse.map (WShape.lift (N+1)))
  have hle₀ : (WShape.ctor' c' (rs'.reverse.map (WShape.lift (N+1)))) ≤ x₀.2.lift (N+2) := by
    have := (TShape.LE.def (Nat.succ_le_succ hNn) (Nat.le_refl (N+2))).1
      (hraw.trans (TShape.lift_eqv hNx).2)
    rwa [WShape.lift_ctor' hNn, WShape.lift_self] at this
  rw [hctoreq] at hle₀
  obtain ⟨l', h', hm₀, hl'⟩ := WShape.ctor_le.1 hle₀
  rw [hm₀] at hma₀ D₀
  have ha₀ := T.hasType_ctor_inv hma₀
  rw [ha₀] at D₀
  have hcd : LRS.CtorDefEq (LR Γ₀ (n := N+1)) σ.head σ'.head
      (SExpr.const I (us.map (SLevel.instV ls))) c' l' :=
    (LRS.DefEq.ctor_indTy (IH := LR Γ₀ (n := N+1)) (h := h')).1 D₀
  obtain ⟨I₂, ls₂, ci₂, Ts₂, Xs, Ys, hcl₂, hI₂, hci₂, hty₂, hA₂, hX, hY, hF⟩ := hcd
  have hdomW : WHNF Γ₀ (SExpr.const I (us.map (SLevel.instV ls))) :=
    WHNF.of_headE (hgapI hcty hHs) rfl
  have hdomeq := hdomW.whRedS hA₂.2
  injection hdomeq with e1 e2
  subst e1 e2
  cases hci'.symm.trans hci₂
  have hty₃ : mkInst (us.map (SLevel.instV ls)) ci'.type =
      (Tsc.map (mkInst (us.map (SLevel.instV ls)))).foldr .forallE
        (.const I'' ((VLevel.params ci'.uvars).map (SLevel.instV (us.map (SLevel.instV ls))))) := by
    rw [hcity', mkInst_foldr_forallE]; rfl
  obtain ⟨hTs₂, -, -⟩ := foldr_forallE_const_inj (hty₂.symm.trans hty₃)
  subst hTs₂
  have hl'len : l'.length = kf := by cases hcl'.symm.trans hcl₂; rfl
  -- I4: the lowered field entries and the pattern-context part `Wc` of `W_p`
  obtain ⟨hXl, hYl, hll, hFget⟩ := T.fieldsEq_get hF
  simp only [List.length_map, hTsc] at hXl hYl hll
  obtain ⟨es, hes⟩ : ∃ es : List (SExpr × SExpr × SExpr × TShape),
      es = (((Tsc.map (mkInst (us.map (SLevel.instV ls)))).zip (Xs.zip (Ys.zip l'))).map
        fun x => (x.1, x.2.1, x.2.2.1, T.lowF N x.1 x.2.2.2)).reverse := ⟨_, rfl⟩
  have heslen : es.length = kf := by
    simp [hes, List.length_zip, hTsc, hXl, hYl, hll]
  have hesget : ∀ (j : Nat) (e : SExpr × SExpr × SExpr × TShape), es[j]? = some e →
      ∃ i, i + j + 1 = kf ∧
        (Tsc.map (mkInst (us.map (SLevel.instV ls))))[i]? = some e.1 ∧ Xs[i]? = some e.2.1 ∧
        Ys[i]? = some e.2.2.1 ∧ ∃ q, l'[i]? = some q ∧ e.2.2.2 = T.lowF N e.1 q := by
    intro j e he
    have hj : j < kf := heslen ▸ (List.getElem?_eq_some_iff.1 he).1
    refine ⟨kf - 1 - j, by omega, ?_⟩
    have hlz : j + (kf - 1 - j) + 1 = (((Tsc.map (mkInst (us.map (SLevel.instV ls)))).zip
        (Xs.zip (Ys.zip l'))).map fun x => (x.1, x.2.1, x.2.2.1, T.lowF N x.1 x.2.2.2)).length := by
      simp [List.length_zip, hTsc, hXl, hYl, hll]; omega
    rw [hes, List.getElem?_reverse' hlz, List.getElem?_map, Option.map_eq_some_iff] at he
    obtain ⟨⟨A, X, Y, q⟩, hz, rfl⟩ := he
    simp only [List.getElem?_zip_eq_some] at hz
    exact ⟨hz.1, hz.2.1, hz.2.2.1, q, hz.2.2.2, rfl⟩
  have hes1 : es.map (·.1) = (Tsc.map (mkInst (us.map (SLevel.instV ls)))).reverse := by
    rw [hes, List.map_reverse, List.map_map]
    congr 1
    apply List.ext_getElem (by simp [List.length_zip, hTsc, hXl, hYl, hll])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_zip, Function.comp]
  have hctx' : g.ctx.map (mkInst ls) =
      (Tsc.map (mkInst (us.map (SLevel.instV ls)))).reverse ++ (Hs.map (mkInst ls)).reverse := by
    rw [hctx, List.map_append, List.map_reverse, List.map_reverse, List.map_map]
    congr 2; exact List.map_congr_left (fun T₀ _ => mkInst_instL)
  have h1' : Params.env.constants (Pattern.iota c mm c' kf).head = some ci := by
    simpa [Pattern.head, Pattern.head_varN] using h1
  have hhdr : Params.rank (Pattern.iota c mm c' kf).head = Params.rank c := by
    simp [Pattern.head, Pattern.head_varN]
  -- each field type is a closed inductive constant
  have hTsf : ∀ (i : Nat) (A : SExpr), (Tsc.map (mkInst (us.map (SLevel.instV ls))))[i]? = some A →
      ∃ (I₀ : Name) (vs : List SLevel), A = .const I₀ vs ∧ Params.classify I₀ = some (.indTy 0) := by
    intro i A hA
    rw [List.getElem?_map, Option.map_eq_some_iff] at hA
    obtain ⟨T₀, hT₀, rfl⟩ := hA
    obtain ⟨I₀, vs, rfl, hI₀⟩ := hall T₀ (List.mem_of_getElem? hT₀)
    exact ⟨I₀, _, rfl, hI₀⟩
  have hcondF : ∀ (j : Nat) (e : SExpr × SExpr × SExpr × TShape), es[j]? = some e → e.1.ClosedN ∧
      (∃ u, IsDefEqStrong (Params.env.below Params.rank (Params.rank c))
        ((es.drop (j+1)).map (·.1) ++ ((Hs.map (mkInst ls)).reverse ++ Γ₀)) e.1 e.1 (.sort u)) ∧
      ∃ (n : Nat) (a₁ q : WShape n), e.2.2.2 = q.T ∧ q.HasType a₁ ∧ LE_Interp .nil a₁.T e.1 ∧
        Γ₀ ⊢ e.2.1 ≡ e.2.2.1 : e.1 ∧ (LR Γ₀).DefEq e.2.1 e.2.2.1 e.1 q a₁ := by
    intro j e he
    obtain ⟨i, hij, hA, hX, hY, q, hq, hlow⟩ := hesget j e he
    obtain ⟨I₀, vs, hAc, -⟩ := hTsf i e.1 hA
    refine ⟨by rw [hAc]; trivial, ?_, ?_⟩
    · have hj : j < g.ctx.length := by rw [hctx]; simp [hTsc]; omega
      have hgj : g.ctx[j]? = some ((Tsc.map (fun x => VExpr.instL us x)).reverse[j]'(by
          simp [hTsc]; omega)) := by
        rw [hctx, List.getElem?_append_left (by simp [hTsc]; omega)]
        exact List.getElem?_eq_getElem _
      obtain ⟨u, Hu⟩ := EnvStrongR.of_params.ctx ls hP hg h1' (g.self.length + j) _
        (by rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact hgj)
      refine ⟨u, ?_⟩
      have hA' : mkInst ls ((Tsc.map (fun x => VExpr.instL us x)).reverse[j]'(by
          simp [hTsc]; omega)) = e.1 := by
        have : ((g.ctx.map (mkInst ls)))[j]? = some e.1 := by
          rw [hctx', List.getElem?_append_left (by simp [hTsc]; omega),
            List.getElem?_reverse' (j := i) (by simp [hTsc]; omega)]
          exact hA
        rw [List.getElem?_map, hgj] at this
        simpa using this
      have hctxd : ((g.self ++ g.ctx).drop (g.self.length + j + 1)).map (mkInst ls) ++ Γ₀ =
          (es.drop (j+1)).map (·.1) ++ ((Hs.map (mkInst ls)).reverse ++ Γ₀) := by
        rw [Nat.add_assoc, ← List.drop_drop, List.drop_left, List.map_drop, hctx', List.map_drop,
          hes1, List.drop_append_of_le_length (by simp [hTsc]; omega), List.append_assoc]
      rw [← hctxd, ← hA', ← hhdr]; exact Hu.weak_append
    · obtain ⟨X', Y', q', hX', hY', hq', hxy, hrel⟩ := hFget i e.1 hA
      cases hX.symm.trans hX'; cases hY.symm.trans hY'; cases hq.symm.trans hq'
      rw [hlow]
      exact T.lowF_entry hxy hrel
  have Wc0 := T.substWF_push WFIH hc Wt es hcondF
  obtain ⟨fields, hfields⟩ : ∃ fields : List TShape, fields = es.map (·.2.2.2) := ⟨_, rfl⟩
  have hflen : fields.length = kf := by rw [hfields, List.length_map, heslen]
  have hρt : (List.range mm).foldr (fun i ρ' => Valuation.push ρ' ((ρt.push x₀) (i+1)))
      Valuation.nil = ρt := by
    refine T.range_foldr_self (v := ρt) fun i => ?_
    have := T.substWF_val Wt (Hs.map (mkInst ls)).reverse rfl i
    simpa [hHs] using this
  have Wc : LR.SubstWF Γ₀ (es.foldr (fun e τ => τ.cons e.2.1) σ.tail)
      (es.foldr (fun e τ => τ.cons e.2.2.1) σ'.tail) (g.ctx.map (mkInst ls) ++ Γ₀)
      (Valuation.lowerCtx fields (ρt.push x₀) mm) := by
    rw [hctx', List.append_assoc, ← hes1, Valuation.lowerCtx, hρt, hfields, List.foldr_map]
    exact Wc0
  have hm : g.ctx.length = fields.length + mm := by
    rw [hctx]; simp [hTsc, hHs, hflen]
  -- the context substitution on the fields and the recursor arguments
  obtain ⟨σc, hσc⟩ : ∃ σc : Subst, σc = es.foldr (fun e τ => τ.cons e.2.1) σ.tail := ⟨_, rfl⟩
  obtain ⟨σc', hσc'⟩ : ∃ σc' : Subst, σc' = es.foldr (fun e τ => τ.cons e.2.2.1) σ'.tail :=
    ⟨_, rfl⟩
  rw [← hσc, ← hσc'] at Wc
  have hσc_add : ∀ i, σc (kf + i) = σ (i + 1) := fun i => by
    rw [hσc, ← heslen]; exact T.foldr_cons_add (·.2.1) σ.tail es i
  have hσc'_add : ∀ i, σc' (kf + i) = σ' (i + 1) := fun i => by
    rw [hσc', ← heslen]; exact T.foldr_cons_add (·.2.2.1) σ'.tail es i
  have hσc_X : (List.range kf).reverse.map σc = Xs := by
    apply List.ext_getElem (by simp [hXl])
    intro j h1 h2
    have hj : j < kf := by simpa using h1
    have hje : (kf - 1 - j) < es.length := by omega
    obtain ⟨i, hij, -, hX, -, -⟩ := hesget (kf - 1 - j) es[kf - 1 - j] (List.getElem?_eq_getElem hje)
    have hi : i = j := by omega
    subst hi
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]
    rw [hσc, T.foldr_cons_lt (·.2.1) σ.tail es _ es[kf - 1 - i] (List.getElem?_eq_getElem hje)]
    rw [List.getElem?_eq_getElem h2] at hX
    exact (Option.some.inj hX).symm
  have hσc'_Y : (List.range kf).reverse.map σc' = Ys := by
    apply List.ext_getElem (by simp [hYl])
    intro j h1 h2
    have hj : j < kf := by simpa using h1
    have hje : (kf - 1 - j) < es.length := by omega
    obtain ⟨i, hij, -, -, hY, -⟩ := hesget (kf - 1 - j) es[kf - 1 - j] (List.getElem?_eq_getElem hje)
    have hi : i = j := by omega
    subst hi
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]
    rw [hσc', T.foldr_cons_lt (·.2.2.1) σ'.tail es _ es[kf - 1 - i] (List.getElem?_eq_getElem hje)]
    rw [List.getElem?_eq_getElem h2] at hY
    exact (Option.some.inj hY).symm
  -- I5: `hroot`, `hvar`, `hhead` for `T.rhs_core`
  have hinl : ∀ x, Sum.elim mf ma (Sum.inl x) ≤ Valuation.lowerCtx fields (ρt.push x₀) mm
      ((Pattern.iota c mm c' kf).pathIdx (Sum.inl x)) := by
    intro x
    obtain ⟨s, hs, he⟩ := hxf x
    have hi : (Pattern.varN (.const c) mm).pathIdx x < mm :=
      lf ▸ (List.getElem?_eq_some_iff.1 hs).1
    simp only [Sum.elim_inl, Pattern.pathIdx_inl, Pattern.nvars_varN, Pattern.nvars]
    rw [he, Nat.zero_add, show (Pattern.varN (.const c) mm).pathIdx x + kf =
      fields.length + (Pattern.varN (.const c) mm).pathIdx x by omega,
      T.lowerCtx_rec _ _ _ _ hi]
    have := hρ ((Pattern.varN (.const c) mm).pathIdx x + 1)
    rwa [Valuation.ofRargs, List.foldr_cons, Valuation.push, ← Valuation.ofRargs,
      T.ofRargs_get hs] at this
  have hvar : ∀ path {n} {y b : WShape n}, y.T ≤ Sum.elim mf ma path → y.HasType b →
      LE_Interp (Valuation.lowerCtx fields (ρt.push x₀) mm) b.T
        (SExpr.mkInst ls ((g.ctx.getD ((Pattern.iota c mm c' kf).pathIdx path) (.sort .zero)).liftN
          ((Pattern.iota c mm c' kf).pathIdx path + 1))) →
      y.T ≤ Valuation.lowerCtx fields (ρt.push x₀) mm ((Pattern.iota c mm c' kf).pathIdx path) := by
    intro path n y b hy hyb hb
    cases path with
    | inl x => exact hy.trans (hinl x)
    | inr x =>
      obtain ⟨s, hs, he⟩ := hxa x
      simp only [Sum.elim_inr, Pattern.pathIdx_inr] at hy hb ⊢
      rw [he] at hy
      have hi : (Pattern.varN (.const c') kf).pathIdx x < kf :=
        la ▸ (List.getElem?_eq_some_iff.1 hs).1
      have hie : (Pattern.varN (.const c') kf).pathIdx x < es.length := by omega
      obtain ⟨i₀, hi₀, hA, -, -, q, hq, hlow⟩ := hesget _ _ (List.getElem?_eq_getElem hie)
      have hfi : fields[(Pattern.varN (.const c') kf).pathIdx x]? =
          some es[(Pattern.varN (.const c') kf).pathIdx x].2.2.2 := by
        rw [hfields, List.getElem?_map, List.getElem?_eq_getElem hie]; rfl
      rw [Valuation.lowerCtx, T.foldr_push_lt _ _ _ _ hfi, hlow]
      obtain ⟨I₀, vs, hAc, hI₀⟩ := hTsf i₀ _ hA
      -- the context type at the path is the field type
      have hgt : mkInst ls ((g.ctx.getD ((Pattern.varN (.const c') kf).pathIdx x) (.sort .zero)).liftN
          ((Pattern.varN (.const c') kf).pathIdx x + 1)) =
          es[(Pattern.varN (.const c') kf).pathIdx x].1 := by
        rw [T.mkInst_liftN]
        have hj : (Pattern.varN (.const c') kf).pathIdx x < g.ctx.length := by
          rw [hctx]; simp [hTsc]; omega
        have hgm : (g.ctx.map (mkInst ls))[(Pattern.varN (.const c') kf).pathIdx x]? =
            some es[(Pattern.varN (.const c') kf).pathIdx x].1 := by
          rw [hctx', List.getElem?_append_left (by simp [hTsc]; omega),
            List.getElem?_reverse' (j := i₀) (by simp [hTsc]; omega)]
          exact hA
        rw [List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some] at hgm
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some,
          Option.some.inj hgm, hAc, T.liftK_const]
      rw [hgt] at hb
      refine T.hvar_field ⟨I₀, vs, 0, hAc, hI₀⟩ (hy.trans ?_) hyb hb
      have hrs : (rs'.reverse.map (WShape.lift (N+1)))[i₀]? = some (s.lift (N+1)) := by
        rw [List.getElem?_map, List.getElem?_reverse' (j := (Pattern.varN (.const c') kf).pathIdx x)
          (by rw [la]; omega), hs]; rfl
      exact (TShape.lift_eqv hNn).2.trans (WShape.LE.T (T.forall₂_get hl' i₀ _ _ hrs hq))
  have hhead := T.hhead_supply hg hMt0 hρ0 hm
  -- I6a: the types: (d) and the type transfer to `ρ`
  have hgty := Pattern.gen_type hg h1 hHs hcty
  have hτ₀ := T.type_subst ls Bmaj c' us kf
  rw [← hgty] at hτ₀
  obtain ⟨τ, hτ⟩ : ∃ τ : Subst, τ = σ.tail.cons (spine (.const c' (us.map (SLevel.instV ls))) Xs) :=
    ⟨_, rfl⟩
  obtain ⟨τ', hτ'⟩ : ∃ τ' : Subst,
      τ' = σ'.tail.cons (spine (.const c' (us.map (SLevel.instV ls))) Ys) := ⟨_, rfl⟩
  have htyσ : (mkInst ls g.type).subst σc = (mkInst ls Bmaj).subst τ := by
    rw [hτ₀, subst_subst]; congr 1; funext i
    cases i with
    | zero => simp only [Subst.comp, Subst.cons, hτ, openSpine_subst, hσc_X]
    | succ i =>
      simp only [Subst.comp, Subst.cons, hτ, SExpr.subst, Subst.tail]
      rw [Nat.add_comm, hσc_add]
  have htyσ' : (mkInst ls g.type).subst σc' = (mkInst ls Bmaj).subst τ' := by
    rw [hτ₀, subst_subst]; congr 1; funext i
    cases i with
    | zero => simp only [Subst.comp, Subst.cons, hτ', openSpine_subst, hσc'_Y]
    | succ i =>
      simp only [Subst.comp, Subst.cons, hτ', SExpr.subst, Subst.tail]
      rw [Nat.add_comm, hσc'_add]
  have htrans : ∀ {n₂} {b₂ : WShape n₂},
      LE_Interp (Valuation.lowerCtx fields (ρt.push x₀) mm) b₂.T (mkInst ls g.type) →
      LE_Interp (ρt.push x₀) b₂.T (mkInst ls Bmaj) := by
    intro n₂ b₂ hb₂
    rw [hτ₀] at hb₂
    obtain ⟨ρ'', hB'', hσ''⟩ := LE_Interp.subst.1 hb₂
    refine hB''.mono_l fun i => ?_
    cases i with
    | zero =>
      have h0' := hσ'' 0
      simp only [Subst.cons, openSpine] at h0'
      rcases T.ctor_spine_le hcl' (by simp) h0' with hb0 | ⟨nr, rs, hsr, hF2⟩
      · exact hb0.trans TShape.bot_le
      refine hsr.trans ?_
      have hrsl : rs.length = kf := by have := List.Forall₂.length_eq hF2; simpa using this
      have hrs : List.Forall₂ (fun r q => r.T ≤ q.T) rs l' := by
        refine T.forall₂_of_get (by rw [hrsl, hl'len]) fun j r q hr hq => ?_
        have hj : j < kf := hrsl ▸ (List.getElem?_eq_some_iff.1 hr).1
        have hZ : ((List.range kf).reverse.map SExpr.bvar)[j]? = some (.bvar (kf - 1 - j)) := by
          rw [List.getElem?_map, List.getElem?_reverse (by simpa using hj)]
          simp [List.getElem?_range (by omega : kf - 1 - j < kf)]
        have hrZ := T.forall₂_get hF2 j r _ hr hZ
        rw [LE_Interp.bvar_iff] at hrZ
        have hje : kf - 1 - j < es.length := by omega
        obtain ⟨i₀, hi₀, -, -, -, q', hq', hlow⟩ := hesget _ _ (List.getElem?_eq_getElem hje)
        have hi : i₀ = j := by omega
        subst hi
        cases hq.symm.trans hq'
        have hfi : fields[kf - 1 - i₀]? = some es[kf - 1 - i₀].2.2.2 := by
          rw [hfields, List.getElem?_map, List.getElem?_eq_getElem hje]; rfl
        rw [Valuation.lowerCtx, T.foldr_push_lt _ _ _ _ hfi, hlow] at hrZ
        exact hrZ.trans T.lowF_le
      refine (T.ctor'_le_T hrs).trans ?_
      rw [show WShape.ctor' c' l' = WShape.ctor c' l' h' from WShape.ctor_eq_ctor'.symm, ← hm₀]
      exact (TShape.lift_eqv hNx).1
    | succ i =>
      have hi' := hσ'' (i+1)
      simp only [Subst.cons, LE_Interp.bvar_iff] at hi'
      have heq : Valuation.lowerCtx fields (ρt.push x₀) mm (i + kf) = (ρt.push x₀) (i + 1) := by
        rw [Valuation.lowerCtx, show i + kf = fields.length + i by omega, T.foldr_push_add, hρt]
        rfl
      exact heq ▸ hi'
  -- I6: the root of the RHS is interpreted (a bare field root via the type transfer)
  have hrootArg : (m.T ≤ mC ∧ ∀ path, r.1 = .var path → Sum.elim mf ma path ≤
        Valuation.lowerCtx fields (ρt.push x₀) mm ((Pattern.iota c mm c' kf).pathIdx path)) ∨
      ∃ path, r.1 = .var path ∧
        m.T ≤ Valuation.lowerCtx fields (ρt.push x₀) mm ((Pattern.iota c mm c' kf).pathIdx path) := by
    by_cases hbare : ∃ x, r.1 = .var (.inr x)
    case neg =>
      refine .inl ⟨le, fun path hr => ?_⟩
      cases path with
      | inl x => exact hinl x
      | inr x => exact absurd ⟨x, hr⟩ hbare
    obtain ⟨x, hx⟩ := hbare
    refine .inr ⟨.inr x, hx, ?_⟩
    obtain ⟨s, hs, hma_x⟩ := hxa x
    simp only [Pattern.pathIdx_inr]
    have hi : (Pattern.varN (.const c') kf).pathIdx x < kf :=
      la ▸ (List.getElem?_eq_some_iff.1 hs).1
    have hie : (Pattern.varN (.const c') kf).pathIdx x < es.length := by omega
    obtain ⟨i₀, hi₀, hA', -, -, q, hq, hlow⟩ := hesget _ _ (List.getElem?_eq_getElem hie)
    have hfi : fields[(Pattern.varN (.const c') kf).pathIdx x]? =
        some es[(Pattern.varN (.const c') kf).pathIdx x].2.2.2 := by
      rw [hfields, List.getElem?_map, List.getElem?_eq_getElem hie]; rfl
    rw [Valuation.lowerCtx, T.foldr_push_lt _ _ _ _ hfi, hlow]
    -- the element shape is below the raw field shape, hence below `q`
    have hmC : m.T ≤ s.T := by
      have hR2 := hRHS
      rw [hx] at hR2
      cases hR2 with
      | bot => exact le.trans TShape.bot_le'
      | var h => exact le.trans (hma_x ▸ h)
    have hrs : (rs'.reverse.map (WShape.lift (N+1)))[i₀]? = some (s.lift (N+1)) := by
      rw [List.getElem?_map, List.getElem?_reverse' (j := (Pattern.varN (.const c') kf).pathIdx x)
        (by rw [la]; omega), hs]; rfl
    have hmq : m.T ≤ q.T :=
      hmC.trans ((TShape.lift_eqv hNn).2.trans (WShape.LE.T (T.forall₂_get hl' i₀ _ _ hrs hq)))
    -- the field type, at the generic level and at `ls`
    have hi₀l : i₀ < Tsc.length := by omega
    obtain ⟨I₀, vs₀, hT₀, hI₀⟩ := hall Tsc[i₀] (List.getElem_mem hi₀l)
    have hgctx : g.ctx[(Pattern.varN (.const c') kf).pathIdx x]? =
        some (.const I₀ (vs₀.map (·.inst us))) := by
      rw [hctx, List.getElem?_append_left (by simp [hTsc]; omega),
        List.getElem?_reverse' (j := i₀) (by simp [hTsc]; omega), List.getElem?_map,
        List.getElem?_eq_getElem hi₀l, hT₀]; rfl
    have hgm : (g.ctx.map (mkInst ls))[(Pattern.varN (.const c') kf).pathIdx x]? =
        some es[(Pattern.varN (.const c') kf).pathIdx x].1 := by
      rw [hctx', List.getElem?_append_left (by simp [hTsc]; omega),
        List.getElem?_reverse' (j := i₀) (by simp [hTsc]; omega)]
      exact hA'
    rw [List.getElem?_map, hgctx, Option.map_some, Option.some.injEq] at hgm
    -- its constant, level count and sort, from the strong typing of the context entry
    have hjc : (Pattern.varN (.const c') kf).pathIdx x < g.ctx.length := by
      rw [hctx]; simp [hTsc]; omega
    obtain ⟨u', Hu⟩ := EnvStrongR.of_params.ctx ls hP hg h1'
      (g.self.length + (Pattern.varN (.const c') kf).pathIdx x) _
      (by rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact hgctx)
    have ssC := (LE_Interp.strongSoundS (Hu.mono (Params.env.below_le ..))).left
    simp only [mkInst] at ssC
    obtain ⟨-, -, hcoreC, -⟩ := ssC
    cases hcoreC with
    | const hciI hlenI _ _ _ =>
    obtain ⟨-, u₀, htyI⟩ := Params.indTy_closed hI₀ hciI
    have hnz := hgapF x hx I₀ _ _ u₀ hgctx hciI htyI
    have hu₀ : SLevel.instV ((vs₀.map (·.inst us)).map (SLevel.instV ls)) u₀ ≠ .zero := by
      rw [← SLevel.instV_inst]
      intro h
      have := congrArg (fun l : SLevel => l.1 []) h
      simp only [SLevel.instV, SLevel.zero] at this
      exact hnz _ this
    have hP1 : LE_Interp .nil (WShape.indTy (n := N)).T
        (SExpr.const I₀ ((vs₀.map (·.inst us)).map (SLevel.instV ls))) :=
      T.indTy_interp_const hI₀ hciI hlenI htyI hu₀
    -- the rule's type at the field root is the field type (`SoundEq` of the RHS typing)
    have ssR := (LE_Interp.strongSoundS (T.pat_defeq_inst hP hg h1' ls Γ₀).hasType.2).left
    rw [(Pattern.gen_eq_some hg).2.2.1, hx] at ssR
    simp only [Pattern.RHS.toVExpr, mkInst, Nat.zero_add, Pattern.pathIdx_inr] at ssR
    obtain ⟨-, -, hcoreR, hTeqR⟩ := ssR
    cases hcoreR with
    | bvar hL =>
    obtain ⟨B₀, hB₀, rfl⟩ := T.lookup_eq hL
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_map, hgctx, Option.map_some,
      Option.some.injEq] at hB₀
    subst hB₀
    have hgt : LE_Interp (Valuation.lowerCtx fields (ρt.push x₀) mm) (WShape.indTy (n := N)).T
        (mkInst ls g.type) := by
      refine (hTeqR Wc.fits).1 ?_
      simp only [mkInst, T.liftK_const]
      exact (LE_Interp.closed_iff (M := SExpr.const _ _) trivial).1 hP1
    have haI := T.le_indTy_of_compat (hA.compat (htrans hgt))
    have hbT : LE_Interp .nil a.T es[(Pattern.varN (.const c') kf).pathIdx x].1 := by
      rw [← hgm]; exact hP1.mono haI
    obtain ⟨I₁, vs₁, hTc, hI₁⟩ := hTsf i₀ _ hA'
    exact T.hvar_field ⟨I₁, vs₁, 0, hTc, hI₁⟩ hmq hmem hbT
  -- I7: the RHS part (`T.rhs_core`)
  obtain ⟨n₁, y, b, hle, hyb, hb, D⟩ :=
    T.rhs_core WFIH hc h1 LIH hR hP hMt0 hRHS g hg hm Wc hvar hhead hrootArg
  rw [htyσ] at D
  have hbB := htrans hb
  -- I8: type validity of `B` from the WF IH (`EnvStrongR.const`, `telescope`)
  have hctxT : (Hs.map (mkInst ls) ++ [SExpr.const I (us.map (SLevel.instV ls))]).reverse ++ Γ₀ =
      SExpr.const I (us.map (SLevel.instV ls)) :: ((Hs.map (mkInst ls)).reverse ++ Γ₀) := by
    simp only [List.reverse_append, List.reverse_singleton, List.cons_append, List.nil_append]
  obtain ⟨u₁, HB0⟩ := EnvStrongR.of_params.const ls h1
  rw [hT'] at HB0
  obtain ⟨v₁, HB1⟩ := T.telStrong_last (IsDefEqStrong.telescope HB0)
  have HB : IsDefEqStrong (Params.env.below Params.rank (Params.rank c))
      ((Hs.map (mkInst ls) ++ [SExpr.const I (us.map (SLevel.instV ls))]).reverse ++ Γ₀)
      (mkInst ls Bmaj) (mkInst ls Bmaj) (.sort v₁) := by
    have := HB1.weak_append (Γ₀ := Γ₀); simpa using this
  have tyB : ∀ {n₂} {b₂ : WShape n₂}, LE_Interp (ρt.push x₀) b₂.T (mkInst ls Bmaj) →
      b₂.HasType .type → ∀ {τ₁ τ₂}, LR.SubstWF Γ₀ τ₁ τ₂
        ((Hs.map (mkInst ls) ++ [SExpr.const I (us.map (SLevel.instV ls))]).reverse ++ Γ₀)
        (ρt.push x₀) →
      (LR Γ₀).TyDefEq ((mkInst ls Bmaj).subst τ₁) ((mkInst ls Bmaj).subst τ₂) b₂ := by
    intro n₂ b₂ hb₂ hb₂t τ₁ τ₂ Wτ
    obtain ⟨n₃, a₃, s₃, le_n, le_a, hA₃, hS₃, hmem₃⟩ :=
      ((LE_Interp.soundSE (Params.env.below_le ..) HB Wτ.fits).2 hb₂).out
    exact LR.toValTy le_n le_a hb₂t hS₃ hmem₃ (((WFIH _ hc HB hA₃ hS₃ hmem₃).1 Wτ).1)
  -- I9: `σ` (resp. `σ'`) with the major replaced by the ctor spine is still a `SubstWF`
  have hrefl : TWHRedS Γ₀ σ.head σ.head (SExpr.const I (us.map (SLevel.instV ls))) :=
    ⟨hX.1.hasType.1, .rfl⟩
  have hrefl' : TWHRedS Γ₀ σ'.head σ'.head (SExpr.const I (us.map (SLevel.instV ls))) :=
    ⟨hY.1.hasType.1, .rfl⟩
  have Wτσ : LR.SubstWF Γ₀ τ σ
      ((Hs.map (mkInst ls) ++ [SExpr.const I (us.map (SLevel.instV ls))]).reverse ++ Γ₀)
      (ρt.push x₀) := by
    rw [hctxT, hτ]
    refine .cons Wt.left h1W h2W h3W hAW ⟨hX.1.symm, fun n₂ a₂ ha₂ => ⟨(h0.2 a₂ ha₂).1, ?_⟩⟩
    intro m₂ hm₂ hma₂
    exact ((LR Γ₀).whr hX hrefl).1 ((LR Γ₀).left ((h0.2 a₂ ha₂).2 hm₂ hma₂))
  have Wτσ' : LR.SubstWF Γ₀ τ' σ'
      ((Hs.map (mkInst ls) ++ [SExpr.const I (us.map (SLevel.instV ls))]).reverse ++ Γ₀)
      (ρt.push x₀) := by
    rw [hctxT, hτ']
    refine .cons Wt.symm.left h1W h2W h3W hAW ⟨hY.1.symm, fun n₂ a₂ ha₂ => ⟨?_, ?_⟩⟩
    · intro ht
      obtain ⟨⟨u₂, he⟩, hty⟩ := (h0.2 a₂ ha₂).1 ht
      exact ⟨⟨u₂, he.hasType.2⟩, (LR Γ₀).left_ty ((LR Γ₀).symm_ty hty)⟩
    · intro m₂ hm₂ hma₂
      exact ((LR Γ₀).whr hY hrefl').1 ((LR Γ₀).left ((LR Γ₀).symm ((h0.2 a₂ ha₂).2 hm₂ hma₂)))
  -- I10: typed head reductions of both sides to the RHS instances (D4 step 5)
  rw [hlenTs]
  have Hc : Γ₀ ⊢ .const c ls :
      (Hs.map (mkInst ls) ++ [SExpr.const I (us.map (SLevel.instV ls))]).foldr .forallE
        (mkInst ls Bmaj) := hT ▸ IsDefEq.const h1 h2
  have Hos := T.spine_bvars_typed _ Hc
  rw [T.liftK_const, hlenTs] at Hos
  change _ ⊢ openSpine c ls (mm+1) : _ at Hos
  have hLdec : ∀ σ₀ : Subst, (openSpine c ls (mm+1)).subst σ₀ =
      .app (spine (.const c ls) ((List.range mm).reverse.map fun i => σ₀ (i+1))) (σ₀ 0) := by
    intro σ₀
    rw [openSpine_subst, T.range_reverse_succ, List.map_append, List.map_map, List.map_singleton,
      spine_snoc]; rfl
  have hlhsEq : ∀ (σ₀ σc₀ : Subst) (Zs : List SExpr), (∀ i, σc₀ (kf + i) = σ₀ (i + 1)) →
      (List.range kf).reverse.map σc₀ = Zs →
      (openSpine c ls (mm+1)).subst (σ₀.tail.cons (spine (.const c' (us.map (SLevel.instV ls))) Zs)) =
        (mkInst ls g.lhs).subst σc₀ := by
    intro σ₀ σc₀ Zs hadd hZ
    rw [hLdec, Pattern.gen_lhs_subst hg h1 hHs hcty h2 σc₀, hZ]
    congr 3
    funext i; exact (hadd i).symm
  have hmaj : ∀ σ₀ : Subst, IsMajorPremise
      (spine (.const c ls) ((List.range mm).reverse.map fun i => σ₀ (i+1))) := by
    intro σ₀
    have hsp := T.matchesS_spine (Pattern.MatchesS.const (c := c) (ls := ls))
      ((List.range mm).reverse.map fun i => σ₀ (i+1))
    have hlen : ((List.range mm).reverse.map fun i => σ₀ (i+1)).length = mm := by simp
    rw [hlen] at hsp
    obtain ⟨g₁, hg₁⟩ := hsp
    exact IsMajorPremise.mk hP hg₁
  have HBd := HB.defeqE (Params.env.below_le ..)
  have hred : ∀ (σ₀ σc₀ : Subst) (Zs : List SExpr), (∀ i, σc₀ (kf + i) = σ₀ (i + 1)) →
      (List.range kf).reverse.map σc₀ = Zs →
      (Γ₀ ⊢ σ₀.head ⤳* spine (.const c' (us.map (SLevel.instV ls))) Zs) →
      Γ₀ ⊢ (openSpine c ls (mm+1)).subst σ₀ ⤳*
        r.1.applyS ls (fun path => σc₀ ((Pattern.iota c mm c' kf).pathIdx path)) := by
    intro σ₀ σc₀ Zs hadd hZ hrd
    have h1r : Γ₀ ⊢ (openSpine c ls (mm+1)).subst σ₀ ⤳*
        (openSpine c ls (mm+1)).subst (σ₀.tail.cons (spine (.const c' (us.map (SLevel.instV ls))) Zs)) := by
      rw [hLdec, hLdec]; exact WHRedS.major (hmaj σ₀) hrd
    refine .tail h1r ?_
    rw [hlhsEq σ₀ σc₀ Zs hadd hZ]
    exact WHRed.extra' hP (T.gen_lhs_matches hg h1 hHs hcty h2 σc₀) (by rw [hchk]; exact nofun)
  have hE2 := IsDefEq.subst W.wf₀ Wc.left.toSubstEq (T.pat_defeq_inst hP hg h1' ls Γ₀).defeq
  rw [Pattern.gen_rhs hg ls _ σc (fun _ => rfl), htyσ, ← hlhsEq σ σc Xs hσc_add hσc_X, ← hτ] at hE2
  have hE2' := IsDefEq.subst W.wf₀ Wc.symm.left.toSubstEq (T.pat_defeq_inst hP hg h1' ls Γ₀).defeq
  rw [Pattern.gen_rhs hg ls _ σc' (fun _ => rfl), htyσ', ← hlhsEq σ' σc' Ys hσc'_add hσc'_Y,
    ← hτ'] at hE2'
  have hE1 := IsDefEq.subst W.wf₀ Wτσ.symm.toSubstEq Hos
  have hE1' := IsDefEq.subst W.wf₀ Wτσ'.symm.toSubstEq Hos
  have hE3 := IsDefEq.subst W.wf₀ Wτσ.symm.toSubstEq HBd
  have hE3' := IsDefEq.subst W.wf₀ Wτσ'.symm.toSubstEq HBd
  have hE4 := IsDefEq.subst W.wf₀ W.toSubstEq HBd
  have hL : TWHRedS Γ₀ ((openSpine c ls (mm+1)).subst σ)
      (r.1.applyS ls (fun path => σc ((Pattern.iota c mm c' kf).pathIdx path)))
      ((mkInst ls Bmaj).subst σ) :=
    ⟨hE1.trans (hE3.symm.defeqDF hE2), hred σ σc Xs hσc_add hσc_X hX.2⟩
  have hL' : TWHRedS Γ₀ ((openSpine c ls (mm+1)).subst σ')
      (r.1.applyS ls (fun path => σc' ((Pattern.iota c mm c' kf).pathIdx path)))
      ((mkInst ls Bmaj).subst σ) :=
    ⟨hE4.symm.defeqDF (hE1'.trans (hE3'.symm.defeqDF hE2')), hred σ' σc' Ys hσc'_add hσc'_Y hY.2⟩
  exact T.finish hL hL' D (tyB hbB hyb.isType Wτσ) (tyV W.left) hle hmem hyb
    (hA.compat hbB)

end Lean4Lean.SExpr
