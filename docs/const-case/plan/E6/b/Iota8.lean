import Lean4Lean.Experimental.E6.Iota7
/-! E6, the iota shape of the pattern leaf: assembly of D4 steps 1-6. -/
namespace Lean4Lean.SExpr
variable [Params]

theorem T.pat_leaf_iota {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
    (WFIH : LR.WFIH Params.rank Γ₀ k) {c : Name} {ci : VConstant} {ls : List SLevel}
    (hc : Params.rank c < k) (h1 : Params.env.constants c = some ci) (h2 : ls.length = ci.uvars)
    {R : TShape → SExpr → Prop} (LIH : LR.LocalIH Params.rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e)
    {rec c' : Name} {mm nn : Nat}
    {r : (Pattern.iota rec mm c' nn).RHS × (Pattern.iota rec mm c' nn).Check} {n : Nat}
    {rargs : List (WShape n)}
    {m2 : (Pattern.iota rec mm c' nn).Path → TShape} {mC : TShape}
    (hP : Params.Pat (.iota rec mm c' nn) r) (hMt : LE_Interp.Matches (.iota rec mm c' nn) c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1) (hchk : r.2 = .true)
    (g : PatGen) (hg : Pattern.gen Params.env Params.rank Params.classify (.iota rec mm c' nn) r.1 = some g)
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
      (LR Γ₀).TyDefEq (B.subst τ) (B.subst τ') a)
    -- fact (A), the levels tie of the major (`T.gap_major_levels`)
    (hGA : ∀ {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr} {ci' : VConstant}
      {I_c : Name} {ls'' : List SLevel}, Hs.length = mm →
      ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj) →
      Params.env.constants c' = some ci' → Params.classify I_c = some (.indTy 0) →
      ls''.length = ci'.uvars → TyRedS Γ₀ (.const I (us.map (SLevel.instV ls))) (.const I_c ls'') →
      us.map (SLevel.instV ls) = ls'')
    -- fact (B), the sort of a `Prop`-field-root rule (`T.gap_prop_root_sort`)
    (hGB : ∀ {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr}
      {x : (Pattern.varN (.const c') nn).Path} {F : SExpr} {vB : SLevel}, Hs.length = mm →
      ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj) → r.1 = .var (.inr x) →
      (g.ctx.map (mkInst ls))[(Pattern.varN (.const c') nn).pathIdx x]? = some F →
      (∀ K, ¬ LE_Interp .nil (WShape.indTy (n := K)).T F) → ⊢ Γ₀ →
      IsDefEqStrong (Params.env.below Params.rank (Params.rank c))
        (.const I (us.map (SLevel.instV ls)) :: ((Hs.map (mkInst ls)).reverse ++ Γ₀))
        (mkInst ls Bmaj) (mkInst ls Bmaj) (.sort vB) → vB = SLevel.zero) :
    (LR Γ₀).DefEq ((openSpine c ls Ts.length).subst σ) ((openSpine c ls Ts.length).subst σ')
      (B.subst σ) m a := by
  have hhd : rec = c := by
    have h := T.matches_head hMt
    have e : (Pattern.iota rec mm c' nn).head = rec := Pattern.head_varN rec mm
    exact e.symm.trans h
  subst hhd
  have hMt' := hMt
  have hhead0 : (Pattern.iota rec mm c' nn).head = rec := Pattern.head_varN rec mm
  have hΓ₀ := W.wf₀
  -- syntactic data (spec lemmas (a) with `ctor_syn`, `ctor_fields_closed`)
  obtain ⟨Hs, I, us, Bmaj, hHs, hTc, ci', I', Tsc, args, hci', hcl', hTsc, -, e3, hctx⟩ :=
    Pattern.gen_head_ctor hg h1
  obtain ⟨I'', Tsc', e4, hall⟩ := Params.ctor_fields_closed (cl := .ctor nn) rfl hcl' hci'
  obtain rfl : Tsc = Tsc' := T.foldr_forallE_inj' (T.foldr_app_ne_forallE _ _ args)
    (fun _ _ h => by cases h) (e3.symm.trans e4)
  -- the matched raw shapes
  cases hMt with
  | @app N _ _ rf mf _ c'' rargs' ma hf ha =>
  cases LE_Interp.Matches.varN_const_head ha
  obtain ⟨lf, -⟩ := T.matches_varN mm hf
  -- the recursor telescope `Ts = Hs ++ [D]`, `B = Bmaj`
  have hT2 : mkInst ls ci.type = ((Hs.map (mkInst ls)) ++
      [SExpr.const I (us.map (SLevel.instV ls))]).foldr .forallE (mkInst ls Bmaj) := by
    rw [hTc, mkInst_foldr_forallE, List.foldr_append]; rfl
  obtain ⟨rfl, rfl⟩ := T.foldr_forallE_injS (by simp [hHs, ← hk, lf]) (hT.symm.trans hT2)
  have hctxT : ((Hs.map (mkInst ls)) ++ [SExpr.const I (us.map (SLevel.instV ls))]).reverse ++ Γ₀ =
      SExpr.const I (us.map (SLevel.instV ls)) :: ((Hs.map (mkInst ls)).reverse ++ Γ₀) := by simp
  rw [hctxT] at W tyV
  have hDcl : (SExpr.const I (us.map (SLevel.instV ls))).ClosedN := trivial
  obtain ⟨ρH, x₀, a₀, uD, rfl, WH, hfitD, hA₀, hx₀, hDty, h0⟩ := T.substWF_cons_inv W
  -- the major's typed shape and the constructor clause (D1)
  have hraw : (WShape.ctor' c' rargs'.reverse).T ≤ x₀ := hρ 0
  obtain ⟨K, l, wf, hPle, hlen_l, hbound, hCtor⟩ := T.major_ctor hDcl hcl' hx₀ hA₀ h0 hraw
  obtain ⟨ls'', Xs, Ys, hI'', hDred, hxred, hx'red, hFE, hl_len, hls''⟩ :=
    T.ctor_clause_data hcl' hci' e4 hCtor
  have hΓctx : OnCtx g.ctx (fun Γ A => Params.env.IsType ci.uvars Γ A) :=
    (T.onCtx_append_right g.self hty.1).mono (fun h => h.mono (Params.env.below_le ..))
  have hls''len : ls''.length = ci'.uvars := by
    rw [← hls'']; simp [VLevel.params]
  obtain rfl := hGA hHs hTc hci' hI'' hls''len hDred
  -- the codomain's strong typing in the telescope context
  obtain ⟨uB, HB0⟩ := EnvStrongR.of_params.const ls h1
  rw [hT2] at HB0
  obtain ⟨vB, HB1⟩ := T.telStrong_body HB0.telescope
  have HBs : IsDefEqStrong (Params.env.below Params.rank (Params.rank rec))
      (SExpr.const I (us.map (SLevel.instV ls)) :: ((Hs.map (mkInst ls)).reverse ++ Γ₀))
      (mkInst ls Bmaj) (mkInst ls Bmaj) (.sort vB) := by
    have := HB1.weak_append (Γ₀ := Γ₀)
    simpa using this
  -- lengths
  obtain ⟨hXl, hYl, hll⟩ := T.fieldsEq_len hFE
  simp only [List.length_map] at hXl hYl hll
  rw [hTsc] at hXl hYl hll
  -- the field entries over the recursor part (D4 step 1, fields)
  have hctxM : g.ctx.map (mkInst ls) = (Tsc.map (mkInst (us.map (SLevel.instV ls)))).reverse ++
      (Hs.map (mkInst ls)).reverse := by
    rw [hctx, List.map_append, List.map_reverse, List.map_reverse, List.map_map]
    congr 2; apply List.map_congr_left; intro T _; exact mkInst_instL
  have hFcl : ∀ F ∈ Tsc.map (mkInst (us.map (SLevel.instV ls))), F.ClosedN := by
    intro F hF
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hF
    obtain ⟨J, vs, rfl, -⟩ := hall T hT
    trivial
  have hTyp := T.fields_typing (Γ₀ := Γ₀) hP hg (hhead0 ▸ h1) hctxM hFcl
  rw [hhead0] at hTyp
  have Wc0 := T.cons_fields WFIH hc hFE WH hTyp
  have hnil := T.substWF_nil_beyond WH
  have hρH := T.recVal_eq (x₀ := x₀) (mm := mm) fun i hi => hnil i (by simpa [hHs] using hi)
  have hρc : (List.zipWith (fun F li => (T.lowerF K F li).T)
      (Tsc.map (mkInst (us.map (SLevel.instV ls)))) l).foldl (fun ρ' x => ρ'.push x) ρH =
      Valuation.lowerCtx (List.zipWith (fun F li => (T.lowerF K F li).T)
        (Tsc.map (mkInst (us.map (SLevel.instV ls)))) l).reverse (ρH.push x₀) mm := by
    rw [Valuation.lowerCtx, List.foldr_reverse, ← hρH]
  rw [hρc, ← List.append_assoc, ← hctxM] at Wc0
  have hfl : ((List.zipWith (fun F li => (T.lowerF K F li).T)
      (Tsc.map (mkInst (us.map (SLevel.instV ls)))) l).reverse).length = nn := by
    simp [hTsc, hll]
  have hm : g.ctx.length = ((List.zipWith (fun F li => (T.lowerF K F li).T)
      (Tsc.map (mkInst (us.map (SLevel.instV ls)))) l).reverse).length + mm := by
    rw [hfl, hctx]; simp [hTsc, hHs]
  have hvar := T.hvar_iota (g := g) (ls := ls) hctx hTsc hall hf ha hρ hll hbound
  have hhead := T.hhead_supply hg hMt' hρ hm
  obtain ⟨selfs, hsl, Wp, hρshift, hσshift, hσ'shift, -, hraw', hadeq, hsound⟩ :=
    T.rhs_adequate WFIH hc h1 LIH hR hP hMt' hRHS g hg Wc0 hvar hhead
  -- the field entries of `lowerCtx`, by index
  have hfields : ∀ j, j < nn → ∃ F t, (Tsc.map (mkInst (us.map (SLevel.instV ls))))[j]? = some F ∧
      l[j]? = some t ∧ ((List.zipWith (fun F li => (T.lowerF K F li).T)
        (Tsc.map (mkInst (us.map (SLevel.instV ls)))) l).reverse)[nn - 1 - j]? =
        some (T.lowerF K F t).T := by
    intro j hj
    obtain ⟨F, hF⟩ : ∃ F, (Tsc.map (mkInst (us.map (SLevel.instV ls))))[j]? = some F :=
      ⟨_, List.getElem?_eq_getElem (by simp [hTsc]; omega)⟩
    obtain ⟨t, ht⟩ : ∃ t, l[j]? = some t := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    refine ⟨F, t, hF, ht, ?_⟩
    rw [List.getElem?_reverse (by simp [hTsc, hll]; omega), List.getElem?_zipWith]
    simp only [List.length_zipWith, List.length_map, hTsc, hll, Nat.min_self,
      show nn - 1 - (nn - 1 - j) = j by omega]
    rw [hF, ht]
  have hrecpart : ∀ i, Valuation.lowerCtx ((List.zipWith (fun F li => (T.lowerF K F li).T)
      (Tsc.map (mkInst (us.map (SLevel.instV ls)))) l).reverse) (ρH.push x₀) mm (nn + i) = ρH i := by
    intro i
    rw [← hfl, Valuation.lowerCtx, T.foldr_push_add, ← hρH]
  -- every interpretation of the RHS type at ρ_low interprets `B` at `ρ` (D4 step 6, `a''` vs `a`)
  have hinv : ∀ z, LE_Interp (Valuation.lower selfs ((List.zipWith (fun F li => (T.lowerF K F li).T)
      (Tsc.map (mkInst (us.map (SLevel.instV ls)))) l).reverse) (ρH.push x₀) mm) z
      (mkInst ls (g.type.liftN g.self.length)) → LE_Interp (ρH.push x₀) z (mkInst ls Bmaj) := by
    intro z hz
    rw [T.mkInst_liftN, ← hsl] at hz
    have hz' := (T.LE_Interp_foldr_push_liftK selfs).1 hz
    rw [Pattern.gen_type hg h1 hHs hTc] at hz'
    refine T.type_inv hz' (fun x hx => ?_) (fun i => by rw [hrecpart]; exact .rfl)
    rw [mkInst_bvarSpine] at hx
    obtain ⟨K', rs, hrsl, hrs, hxle⟩ := T.ctor_spine_interp hcl' hx
    obtain ⟨h', he'⟩ := T.ctor'_eq_ctor hcl' l
    refine hxle.trans ((T.ctor'_T_le (l := l) (by simp [hrsl, hll]) fun j s t hs ht => ?_).trans
      (by rw [he']; exact hPle))
    have hj : j < nn := by
      have := (List.getElem?_eq_some_iff.1 hs).1; simp [hrsl] at this; exact this
    rw [List.getElem?_reverse (by omega), hrsl] at hs
    have hb := LE_Interp.bvar_iff.1 (hrs _ s hs)
    obtain ⟨F, t', hF, ht', hfj⟩ := hfields j hj
    cases ht.symm.trans ht'
    rw [Nat.zero_add, T.lowerCtx_field hfj] at hb
    exact hb.trans (WShape.LE.T T.lowerF_le)
  -- `m` is interpreted at ρ_low (D4 step 2; the root case split replaces rhs_lower's `a'`-premise)
  have hmR : LE_Interp (Valuation.lower selfs ((List.zipWith (fun F li => (T.lowerF K F li).T)
      (Tsc.map (mkInst (us.map (SLevel.instV ls)))) l).reverse) (ρH.push x₀) mm) m.T
      (mkInst ls g.rhsAbs) := by
    by_cases hroot : ∃ x, r.1 = .var (.inr x)
    · obtain ⟨x, hx⟩ := hroot
      obtain ⟨la, hxa⟩ := T.matches_varN nn ha
      obtain ⟨s, hs, he⟩ := hxa x
      obtain ⟨j, hjdef⟩ : ∃ j, (Pattern.varN (.const c') nn).pathIdx x = j := ⟨_, rfl⟩
      rw [hjdef] at hs
      have hj : j < nn := la ▸ (List.getElem?_eq_some_iff.1 hs).1
      have hAbs : mkInst ls g.rhsAbs = .bvar (g.self.length + j) := by
        rw [(Pattern.gen_eq_some hg).2.2.2, hx]
        simp [Pattern.RHS.toVExpr, mkInst, hjdef]
      have hmraw : m.T ≤ s.T ∨ m.T ≤ TShape.bot := by
        rw [hx] at hRHS
        cases hRHS with
        | bot => exact .inr (le.trans TShape.bot_eqv.1)
        | var h => exact .inl (le.trans (he ▸ h))
      rw [hAbs]
      refine .bvar ?_
      rw [hρshift]
      obtain hmraw | hmbot := hmraw
      case inr => exact hmbot.trans TShape.bot_le
      obtain ⟨F, t, hF, ht, hfj⟩ := hfields (nn - 1 - j) (by omega)
      rw [show nn - 1 - (nn - 1 - j) = j by omega] at hfj
      rw [T.lowerCtx_field hfj]
      have hsr : rargs'.reverse[nn - 1 - j]? = some s := by
        rw [List.getElem?_reverse (by simp [la]; omega), la,
          show nn - 1 - (nn - 1 - j) = j by omega]; exact hs
      have hst := hbound _ s t hsr ht
      have hFm : F = mkInst (us.map (SLevel.instV ls)) (Tsc[nn - 1 - j]'(by omega)) := by
        rw [List.getElem?_map, List.getElem?_eq_getElem (by omega)] at hF
        exact (Option.some.inj hF).symm
      obtain ⟨J, vs, hJe, hJ⟩ := hall _ (List.getElem_mem (show nn - 1 - j < Tsc.length by omega))
      rw [hJe] at hFm
      have hFcl' : F.ClosedN := by rw [hFm]; trivial
      by_cases hprop : LE_Interp .nil (WShape.indTy (n := K)).T F
      · -- the field type admits `indTy`: the goal's `a` is compatible with it
        have Hr := ((EnvStrongR.of_params.rhs ls hP hg (hhead0 ▸ h1)).weak_append (Γ₀ := Γ₀)).mono
          (Params.env.below_le ..)
        obtain ⟨-, -, hcore, hseq⟩ := (LE_Interp.strongSoundS Hr).left
        rw [hAbs] at hcore
        cases hcore with
        | bvar hL =>
        obtain ⟨B', hB', rfl⟩ := T.lookup_eq hL
        have hB'F : B' = F := by
          rw [List.getElem?_append_left (by simp; omega), List.getElem?_map,
            List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at hB'
          rw [← List.getElem?_map (f := mkInst ls), hctxM, List.getElem?_append_left (by simp; omega),
            List.getElem?_reverse (by simp; omega)] at hB'
          simp only [List.length_map, hTsc] at hB'
          rw [hF] at hB'; exact (Option.some.inj hB').symm
        rw [hB'F] at hseq
        have hI1 : LE_Interp (Valuation.lower selfs ((List.zipWith (fun F li => (T.lowerF K F li).T)
      (Tsc.map (mkInst (us.map (SLevel.instV ls)))) l).reverse) (ρH.push x₀) mm)
            (WShape.indTy (n := K)).T (mkInst ls (g.type.liftN g.self.length)) := by
          refine (hseq Wp.fits).1 ?_
          have e : liftK F (g.self.length + j + 1) = F := by rw [hFm]; simp only [mkInst, T.liftK_const]
          rw [e]; exact (LE_Interp.closed_iff hFcl').1 hprop
        have hcomp := LE_Interp.compat hA (hinv _ hI1)
        have haI := T.compat_indTy_le hcomp
        have hbF : LE_Interp (Valuation.lowerCtx ((List.zipWith (fun F li => (T.lowerF K F li).T)
      (Tsc.map (mkInst (us.map (SLevel.instV ls)))) l).reverse) (ρH.push x₀) mm) a.T F :=
          ((LE_Interp.closed_iff hFcl').1 hprop).mono haI
        exact T.field_var_le hFm hJ (hmraw.trans hst) hmem hbF
      · -- a `Prop`-instance field: `B`'s sort is `Prop` (fact (B), `hGB`), so `m` is `⊥`
        have hFctx : (g.ctx.map (mkInst ls))[(Pattern.varN (.const c') nn).pathIdx x]? = some F := by
          rw [hjdef, hctxM, List.getElem?_append_left (by simp; omega),
            List.getElem?_reverse (by simp; omega)]
          simp only [List.length_map, hTsc]; exact hF
        have hv := hGB hHs hTc hx hFctx (fun K' h => hprop (h.mono T.indTy_T_le)) hΓ₀ HBs
        exact (T.prop_sort_bot (Params.env.below_le ..) HBs W.fits hv hA hmem).trans TShape.bot_le
    · refine (hraw' fun path hp => ?_).mono le
      cases path with
      | inl x =>
        have := T.rec_path_bound hf hρ hfl (fields := ((List.zipWith (fun F li => (T.lowerF K F li).T)
      (Tsc.map (mkInst (us.map (SLevel.instV ls)))) l).reverse)) x
        simp only [Sum.elim_inl, Pattern.pathIdx_inl, Pattern.nvars_varN, Pattern.nvars,
          Nat.zero_add]
        rw [show (Pattern.varN (.const rec) mm).pathIdx x + nn =
          nn + (Pattern.varN (.const rec) mm).pathIdx x from Nat.add_comm _ _]
        exact this
      | inr x => exact absurd ⟨x, hp⟩ hroot
  -- soundness at ρ_low: a typed `(y', a'')` above `m` (D4 step 2), and `a` vs `a''` (step 6)
  obtain ⟨n'', y', a'', -, hmy, hy, ha'', hya⟩ := (hsound hmR).out
  have hcompat : a.T.Compat a''.T := LE_Interp.compat hA (hinv _ ha'')
  obtain ⟨H, hTy''⟩ := hadeq hy ha'' hya
  -- the pattern substitution's field and recursor parts
  have hσc1 : ∀ i, (Xs.foldl (fun (τ : Subst) x => τ.cons x) σ.tail) (nn + i) = σ.tail i := by
    intro i; rw [← hXl]; exact T.foldl_cons_add Xs σ.tail i
  have hσc2 : (List.range nn).reverse.map (Xs.foldl (fun (τ : Subst) x => τ.cons x) σ.tail) = Xs := by
    rw [← hXl]; exact T.foldl_cons_range Xs σ.tail
  have hσc1' : ∀ i, (Ys.foldl (fun (τ : Subst) x => τ.cons x) σ'.tail) (nn + i) = σ'.tail i := by
    intro i; rw [← hYl]; exact T.foldl_cons_add Ys σ'.tail i
  have hσc2' : (List.range nn).reverse.map (Ys.foldl (fun (τ : Subst) x => τ.cons x) σ'.tail) = Ys := by
    rw [← hYl]; exact T.foldl_cons_range Ys σ'.tail
  -- the RHS type under the pattern substitution is `B` at the major-replaced substitution
  have htype : ∀ (σp σc τ : Subst) (Zs : List SExpr), (∀ i, σp (g.self.length + i) = σc i) →
      (∀ i, σc (nn + i) = τ i) → (List.range nn).reverse.map σc = Zs →
      (mkInst ls (g.type.liftN g.self.length)).subst σp =
        (mkInst ls Bmaj).subst (τ.cons (spine (.const c' (us.map (SLevel.instV ls))) Zs)) := by
    intro σp σc τ Zs e1 e2 e3
    rw [T.mkInst_liftN, T.liftK_subst, show (fun i => σp (i + g.self.length)) = σc from
      funext fun i => by rw [Nat.add_comm]; exact e1 i, Pattern.gen_type hg h1 hHs hTc]
    exact T.type_subst e2 (by rw [mkInst_bvarSpine, spine_subst, ← e3]; simp [List.map_map,
      Function.comp_def, SExpr.subst, mkInst])
  rw [htype _ _ σ.tail Xs hσshift hσc1 hσc2] at H hTy''
  -- the major-replaced substitutions (D4 step 6) and the type conversion
  have W₂ := T.major_replace hDcl W hxred
  have W₂' := T.major_replace hDcl W.symm hx'red
  have hTyA := tyV W₂.symm.left
  have hconv := tyV W₂
  have H2 := T.retype hΓ₀ hmy hmem hya hcompat hTyA hTy'' H
  have H3 := (LR Γ₀).conv ((LR Γ₀).symm_ty hconv) H2
  -- typed head reductions of both sides (D4 step 5)
  have hdefS := ((T.strong_env_defeq hΓctx hdef ls).weak_append (Γ₀ := Γ₀)).defeq
  have HBty : (SExpr.const I (us.map (SLevel.instV ls)) :: ((Hs.map (mkInst ls)).reverse ++ Γ₀)) ⊢
      mkInst ls Bmaj : .sort vB := (HBs.mono (Params.env.below_le ..)).defeq
  obtain ⟨ha1, hb1, hr1⟩ := T.iota_typed_red hΓ₀ hP hchk hg h1 h2 hHs hTc hdefS
    WH.left.toSubstEq hxred Wc0.left.toSubstEq hσc1 hσc2
  obtain ⟨ha2, hb2, hr2⟩ := T.iota_typed_red hΓ₀ hP hchk hg h1 h2 hHs hTc hdefS
    WH.symm.left.toSubstEq hx'red Wc0.symm.left.toSubstEq hσc1' hσc2'
  have e1 := IsDefEq.subst hΓ₀ W₂.symm.toSubstEq HBty
  have e2 := IsDefEq.subst hΓ₀ W.symm.toSubstEq HBty
  have e3 := IsDefEq.subst hΓ₀ W₂'.symm.toSubstEq HBty
  have tw1 := And.intro (ha1.trans (.defeqDF e1 hb1)) hr1
  have tw2 := And.intro (IsDefEq.defeqDF e2 (ha2.trans (.defeqDF e3 hb2))) hr2
  have hlen : ((Hs.map (mkInst ls)) ++ [SExpr.const I (us.map (SLevel.instV ls))]).length =
      mm + 1 := by simp [hHs]
  rw [hlen]
  exact ((LR Γ₀).whr tw1 tw2).2 H3

end Lean4Lean.SExpr
