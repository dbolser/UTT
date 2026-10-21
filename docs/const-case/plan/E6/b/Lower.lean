import Lean4Lean.Experimental.E6.Basic
/-! E6: E6a's `LR.rhs_lower` with its main conjunct replaced by the raw-shape conjunct of
`T.rhs_lower_core`. The pattern leaf needs `LE_Interp ρ_low mC rhsAbs` itself when the RHS root is
not a constructor-field variable: the main conjunct asks for a type shape `a'` interpreting the
RHS type at `ρ_low` and typing the goal's `m`, and none is known in advance (only soundness at
`ρ_low` would give one, and soundness needs the interpretation first). -/
namespace Lean4Lean.SExpr
variable [Params]

/-- E6a's `LR.rhs_lower` (its hypotheses less the unused `hm`; the same wrapper around E6a's
`T.rhs_lower_core`, re-run because the conclusion must be about the same `selfs`), concluding
the self facts and: when every root variable's raw shape is below its lowered entry, the raw RHS
shape `mC` itself is interpreted at `ρ_low`. -/
theorem T.rhs_lower2 {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name}
    {ls : List SLevel} {R : TShape → SExpr → Prop} (LIH : LR.LocalIH Params.rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e)
    {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} {mC : TShape}
    (hP : Params.Pat p r) (hMt : LE_Interp.Matches p c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1)
    (g : PatGen) (hg : Pattern.gen Params.env Params.rank Params.classify p r.1 = some g)
    {fields : List TShape} {ρ : Valuation} {m : Nat}
    (hfit : (Valuation.lowerCtx fields ρ m).Fits Γ₀ (g.ctx.map (SExpr.mkInst ls) ++ Γ₀))
    (hvar : ∀ path {n} {y b : WShape n}, y.T ≤ m2 path → y.HasType b →
      LE_Interp (Valuation.lowerCtx fields ρ m) b.T
        (SExpr.mkInst ls ((g.ctx.getD (p.pathIdx path) (.sort .zero)).liftN (p.pathIdx path + 1))) →
      y.T ≤ Valuation.lowerCtx fields ρ m (p.pathIdx path))
    (hhead : ∀ path, m2 path ≤ Valuation.lowerCtx fields ρ m (p.pathIdx path) ∨
      ∃ (I' : Name) (us : List VLevel) (k : Nat), g.ctx[p.pathIdx path]? = some (.const I' us) ∧
        Params.classify I' = some (.indTy k)) :
    ∃ selfs : List TShape, selfs.length = g.self.length ∧
      (∀ j s, selfs[j]? = some s → ∃ (c' : Name) (us : List VLevel) (ci' : VConstant),
        (r.1.selfLeaves (Pattern.sameRank Params.rank p.head))[j]? = some (.const c' us) ∧
        Params.rank c' = Params.rank c ∧ Params.env.constants c' = some ci' ∧ us.length = ci'.uvars ∧
        SExpr.mkInst ls (g.self.getD j (.sort .zero)) =
          SExpr.mkInst (us.map (SLevel.instV ls)) ci'.type ∧
        (∃ (k : Nat) (x b : WShape k), s = x.T ∧ x.HasType b ∧
          LE_Interp ρ₀ b.T (SExpr.mkInst (us.map (SLevel.instV ls)) ci'.type)) ∧
        LR.ConstGoal Γ₀ ρ₀ s c' (us.map (SLevel.instV ls)) ci' ∧
        ((∃ k, s = (WShape.bot (n := k)).T) ∨
          ∃ me, R me (.const c' (us.map (SLevel.instV ls))) ∧ me ≤ s)) ∧
      ((∀ path, r.1 = .var path → m2 path ≤ Valuation.lowerCtx fields ρ m (p.pathIdx path)) →
        LE_Interp (Valuation.lower selfs fields ρ m) mC (SExpr.mkInst ls g.rhsAbs)) := by
  have hhd : p.head = c := T.matches_head hMt
  obtain ⟨⟨ci, hci⟩, hctxlen⟩ := T.gen_head_ctx hg
  obtain ⟨-, -, -, hAbs⟩ := Pattern.gen_eq_some hg
  have hpt := Params.pat_typed hP hg hci
  have hroot : StrongSound ((g.self ++ g.ctx).map (mkInst ls) ++ Γ₀) (mkInst ls g.rhsAbs)
      (mkInst ls (g.type.liftN g.self.length)) :=
    (LE_Interp.strongSoundS (((Params.strong_below hpt.1 hpt.2 ls).weak_append
      (Γ₀ := Γ₀)).mono (Params.env.below_le ..))).left
  have hsel : ∀ e, Pattern.sameRank Params.rank p.head e = true →
      ∃ c' us, e = .const c' us ∧ Params.rank c' = Params.rank c := fun e h => by
    obtain ⟨c', us, rfl, h'⟩ := Pattern.sameRank_eq_true.1 h; exact ⟨c', us, rfl, hhd ▸ h'⟩
  obtain ⟨sl, hlen, hfacts, hclaim⟩ := T.rhs_lower_core LIH hR (Pattern.sameRank Params.rank p.head)
    hsel g.self.length ((g.self ++ g.ctx).map (mkInst ls) ++ Γ₀) hRHS
  have hgs := Pattern.gen_self hg
  have hK : sl.length = g.self.length := hlen.trans hgs.1.symm
  refine ⟨sl, hK, fun j s hs => ?_, ?_⟩
  · have hj : j < (r.1.selfLeaves (Pattern.sameRank Params.rank p.head)).length :=
      hlen ▸ (List.getElem?_eq_some_iff.1 hs).1
    obtain ⟨e, he⟩ : ∃ e, (r.1.selfLeaves (Pattern.sameRank Params.rank p.head))[j]? = some e :=
      ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨c', us, ci', T', rfl, h1, h2, h3, -, h5⟩ := Pattern.gen_self_mkInst hg he ls
    have hgetD : g.self.getD j (.sort .zero) = T' := by simp [List.getD_eq_getElem?_getD, h3]
    have hmem : VExpr.const c' us ∈ r.1.fixedLeaves :=
      (Pattern.RHS.mem_selfLeaves.1 (List.mem_of_getElem? he)).1
    refine ⟨c', us, ci', he, hhd ▸ h2, h1, T.pat_leaf_levels hP hg hci ls Γ₀ hmem h1,
      by rw [hgetD, h5], ?_⟩
    rcases hfacts j s _ hs he with ⟨k, rfl⟩ | ⟨c'', us', ci'', me, he', h1', -, hR', hle, hty, hcg⟩
    · exact ⟨⟨k, .bot, .bot, rfl, .bot' (.bot' .sort), .bot⟩, .inl ⟨k, rfl⟩, .inl ⟨k, rfl⟩⟩
    · cases he'
      cases h1.symm.trans h1'
      exact ⟨hty, hcg, .inr ⟨me, hR', hle⟩⟩
  · have hΓ : (g.self ++ g.ctx).map (mkInst ls) ++ Γ₀ =
        g.self.map (mkInst ls) ++ (g.ctx.map (mkInst ls) ++ Γ₀) := by simp
    have W : Valuation.Fits Γ₀ ((g.self ++ g.ctx).map (mkInst ls) ++ Γ₀)
        (Valuation.lower sl fields ρ m) := by
      rw [hΓ]
      refine T.fits_foldr_push hfit _ sl (by simp [hK]) fun j A x hA hx => ?_
      rw [List.getElem?_map] at hA
      obtain ⟨Aj, hAj, rfl⟩ := Option.map_eq_some_iff.1 hA
      have hj : j < g.self.length := (List.getElem?_eq_some_iff.1 hAj).1
      obtain ⟨u, Hu⟩ := EnvStrongR.of_params.ctx ls hP hg hci j Aj
        (by rw [List.getElem?_append_left hj]; exact hAj)
      have hctx : ((g.self ++ g.ctx).drop (j + 1)).map (mkInst ls) ++ Γ₀ =
          (g.self.map (mkInst ls)).drop (j + 1) ++ (g.ctx.map (mkInst ls) ++ Γ₀) := by
        rw [List.drop_append_of_le_length (by omega)]; simp [List.map_drop]
      refine ⟨⟨u, hctx ▸ (LE_Interp.strongSoundS ((Hu.weak_append (Γ₀ := Γ₀)).mono
        (Params.env.below_le ..))).left⟩, ?_⟩
      have hj' : j < (r.1.selfLeaves (Pattern.sameRank Params.rank p.head)).length := hgs.1 ▸ hj
      obtain ⟨e, he⟩ : ∃ e, (r.1.selfLeaves (Pattern.sameRank Params.rank p.head))[j]? = some e :=
        ⟨_, List.getElem?_eq_getElem hj'⟩
      obtain ⟨c', us, ci', T', rfl, h1, -, h3, -, h5⟩ := Pattern.gen_self_mkInst hg he ls
      cases hAj.symm.trans h3
      rcases hfacts j x _ hx he with ⟨k, rfl⟩ | ⟨c'', us', ci'', me, he', h1', -, -, -, hty, -⟩
      · exact ⟨_, fun _ => .bot, WShape.HasType.T (.bot' (.bot' .sort))⟩
      · cases he'
        cases h1.symm.trans h1'
        obtain ⟨k, x', b, rfl, hxb, hb⟩ := hty
        refine ⟨b.T, fun ρ' => ?_, WShape.HasType.T hxb⟩
        rw [h5]; exact (LE_Interp.closed_iff (Params.henv.closedC h1).mkInstS).1 hb
    have hb : ∀ (i : Nat) (s : TShape), sl[i]? = some s →
        s ≤ (Valuation.lower sl fields ρ m) (0 + i) := fun i s h => by
      rw [Nat.zero_add, Valuation.lower, T.foldr_push_lt _ sl i s h]; exact .rfl
    have hshift : ∀ i, Valuation.lower sl fields ρ m (g.self.length + i) =
        Valuation.lowerCtx fields ρ m i := fun i => by
      rw [← hK]; exact T.foldr_push_add _ sl i
    have hΓi : ∀ i (hi : i < g.ctx.length),
        ((g.self ++ g.ctx).map (mkInst ls) ++ Γ₀)[g.self.length + i]? =
          some (mkInst ls g.ctx[i]) := by
      intro i hi
      rw [List.getElem?_append_left (by simp; omega), List.getElem?_map,
        List.getElem?_append_right (by omega)]
      simp [List.getElem?_eq_getElem hi]
    have hv1 : ∀ path {n} {y b : WShape n} {T'},
        Lookup ((g.self ++ g.ctx).map (mkInst ls) ++ Γ₀) (g.self.length + p.pathIdx path) T' →
        y.T ≤ m2 path → y.HasType b → LE_Interp (Valuation.lower sl fields ρ m) b.T T' →
        y.T ≤ (Valuation.lower sl fields ρ m) (g.self.length + p.pathIdx path) := by
      intro path n y b T' hL hy hty hbT
      have hi : p.pathIdx path < g.ctx.length := hctxlen ▸ T.pathIdx_lt p path
      obtain ⟨B, hB, rfl⟩ := T.lookup_eq hL
      rw [hΓi _ hi] at hB; cases hB
      rw [hshift]
      refine hvar path hy hty ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
        T.mkInst_liftN]
      have e1 : g.self.length + p.pathIdx path + 1 = (p.pathIdx path + 1) + sl.length := by omega
      rw [e1, T.liftK_add] at hbT
      exact (T.LE_Interp_foldr_push_liftK sl).1 hbT
    have hv2 : ∀ path, m2 path ≤ (Valuation.lower sl fields ρ m) (g.self.length + p.pathIdx path) ∨
        ∀ T', Lookup ((g.self ++ g.ctx).map (mkInst ls) ++ Γ₀) (g.self.length + p.pathIdx path) T' →
          ∃ I' ls' k, T' = .const I' ls' ∧ Params.classify I' = some (.indTy k) := by
      intro path
      rcases hhead path with h | ⟨I', us, k, hc, hI⟩
      · exact .inl (by rw [hshift]; exact h)
      · refine .inr fun T' hL => ?_
        have hi : p.pathIdx path < g.ctx.length := hctxlen ▸ T.pathIdx_lt p path
        obtain ⟨B, hB, rfl⟩ := T.lookup_eq hL
        rw [hΓi _ hi] at hB; cases hB
        rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hc
        rw [hc]
        exact ⟨I', _, k, T.liftK_const .., hI⟩
    intro hroot'
    rw [hAbs]
    exact (hclaim 0 W hb hv1 hv2 (hAbs ▸ hroot)).2 fun path e => by rw [hshift]; exact hroot' path e

end Lean4Lean.SExpr
