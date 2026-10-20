import Lean4Lean.Experimental.E6a.FieldLower
/-! E6 (docs/const-case/PLAN.md §2 row E6): helpers for the pattern leaf `T.pat_leaf_1a`.

* valuation/substitution plumbing (`T.substWF_val`, `T.range_foldr_self`);
* the weak typing of the identity telescope application (`T.spine_bvars_typed`, for
  `openSpine`);
* the ctor-spine bound (`T.ctor_spine_le`): interpretations of `c' Z₁ … Zₖ` for a ctor `c'` of
  arity `k` lie below `ctor' c' rs` for argument shapes `rs` interpreting the `Zᵢ`;
* `T.defEq_transfer` (the core of `LR.Adequate.mono_r`) and `T.substWF_push` (iterated
  `LR.Adequate.cons` for closed types);
* `T.rhs_lower2`: E6a's `LR.rhs_lower` with the second conjunct of `T.rhs_lower_core` kept. -/
namespace Lean4Lean.SExpr
variable [Params]

theorem T.substWF_len {Γ₀ Γ : List SExpr} {σ σ' ρ} (W : LR.SubstWF Γ₀ σ σ' Γ ρ) :
    Γ₀.length ≤ Γ.length := by
  induction W with
  | id => exact Nat.le_refl _
  | cons _ _ _ _ _ _ ih => simp only [List.length_cons]; omega

/-- A `SubstWF` over `Δ ++ Γ₀` holds `nil` beyond `Δ`. -/
theorem T.substWF_val {Γ₀ Γ : List SExpr} {σ σ' ρ} (W : LR.SubstWF Γ₀ σ σ' Γ ρ) :
    ∀ Δ : List SExpr, Γ = Δ ++ Γ₀ → ∀ i, ρ (Δ.length + i) = Valuation.nil i := by
  induction W with
  | id => intro Δ h i; have := congrArg List.length h; simp at this; subst this; rfl
  | @cons σ σ' Γ ρ A a x u W' _ _ _ _ _ ih =>
    intro Δ h i
    match Δ, h with
    | [], h =>
      have := T.substWF_len W'; simp at h; subst h; simp at this; omega
    | A' :: Δ', h =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [List.length_cons, Nat.add_right_comm]; exact ih Δ' rfl i

theorem T.range_foldr_push (f : Valuation) : ∀ (m j : Nat),
    ((List.range m).foldr (fun i ρ' => Valuation.push ρ' (f i)) Valuation.nil) j =
      if j < m then f j else Valuation.nil j
  | 0, j => by simp
  | m+1, j => by
    rw [List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
    cases j with
    | zero => simp [Valuation.push]
    | succ j =>
      simp only [Valuation.push]
      rw [T.range_foldr_push (fun i => f (i+1)) m j]
      by_cases h : j < m
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]; rfl

theorem T.range_foldr_self {m : Nat} {v : Valuation} (hv : ∀ i, v (m + i) = Valuation.nil i) :
    (List.range m).foldr (fun i ρ' => Valuation.push ρ' (v i)) Valuation.nil = v := by
  funext j
  refine (T.range_foldr_push v m j).trans ?_
  split
  · rfl
  · rename_i h
    have := hv (j - m); rw [Nat.add_sub_cancel' (by omega)] at this
    rw [this]; rfl

theorem T.lift_inst_bvar0 (R : SExpr) :
    (R.lift' (Lift.skip Lift.refl).cons).inst (.bvar 0) = R := by
  rw [SExpr.inst, subst_lift']
  conv => rhs; rw [← subst_id (e := R)]
  congr 1; funext i; cases i <;> rfl

theorem T.liftK_app (F X : SExpr) : ∀ k, liftK (.app F X) k = .app (liftK F k) (liftK X k)
  | 0 => rfl
  | k+1 => by simp only [liftK, T.liftK_app F X k]; rfl

theorem T.liftK_bvar (i : Nat) : ∀ k, liftK (.bvar i) k = .bvar (i + k)
  | 0 => rfl
  | k+1 => by simp only [liftK, T.liftK_bvar i k]; rfl

/-- The identity telescope application is typed (`openSpine`'s typing, in the weak judgment). -/
theorem T.spine_bvars_typed : ∀ (Ts : List SExpr) {Γ : List SExpr} {F B : SExpr},
    Γ ⊢ F : Ts.foldr .forallE B →
    Ts.reverse ++ Γ ⊢ spine (liftK F Ts.length) ((List.range Ts.length).reverse.map .bvar) : B
  | [], Γ, F, B, H => H
  | T₀ :: Ts, Γ, F, B, H => by
    have H1 := H.weak' (Ctx.Lift'.one (A := T₀))
    simp only [List.foldr_cons, SExpr.lift'] at H1
    have H2 := IsDefEq.appDF H1 (IsDefEq.bvar (Lookup.zero (ty := T₀) (Γ := Γ)))
    rw [T.lift_inst_bvar0] at H2
    have H3 := T.spine_bvars_typed Ts H2
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [T.liftK_app, liftK_lift, T.liftK_bvar, Nat.zero_add] at H3
    rw [List.length_cons, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, spine_cons]
    exact H3


/-- `lam'` of a graph with all outputs `⊥` is `⊥`. -/
theorem T.lam'_eq_bot {f : WShapeFun n} (h : ∀ x y, (x, y) ∈ f → y = .bot) :
    WShape.lam' f = .bot := by
  unfold WShape.lam'
  rw [dif_neg]
  rintro ⟨⟨x, y⟩, hm, hy⟩
  have hwf := f.2.2 _ hm
  have := h ⟨x, hwf.1⟩ ⟨y, hwf.2⟩ hm
  exact hy (by rw [show y = (WShape.bot (n := n)).1 from congrArg (·.1) this]; exact Shape.bot_le)

/-- A ctor-classified constant's `Const` derivation beyond its arity is `⊥`. -/
theorem T.const_beyond {c : Name} {k : Nat} (hc : Params.classify c = some (.ctor k))
    {ls : List SLevel} {R : TShape → SExpr → Prop} {n : Nat} {rargs : List (WShape n)} {m : TShape}
    (H : LE_Interp.Const c ls R rargs m) (hk : k < rargs.length) : m ≤ TShape.bot := by
  induction H with
  | bot => exact TShape.bot_eqv.1
  | @lam f rargs m h1 h2 ih =>
    rw [T.lam'_eq_bot fun x y h => TShape.le_bot.1 (ih x y h (by simp; omega))] at h2
    exact h2.trans TShape.bot_eqv.1
  | ctor h1 _ => cases hc.symm.trans h1; omega
  | indTy h1 _ => cases hc.symm.trans h1
  | pat hP hM _ =>
    obtain ⟨_, h⟩ := Params.Pat.head_symb hP
    rw [T.matches_head hM, hc] at h; cases h



theorem T.le_bot_T {f : WShape n} (h : f.T ≤ TShape.bot) : f = .bot := TShape.le_bot.1 h

/-- Interpretations of a partial spine headed by a ctor-classified constant come from a `Const`
derivation over argument shapes interpreting the arguments (`Ys` = the arguments, last first). -/
theorem T.ctor_spine_bound {ρ : Valuation} {c : Name} {k : Nat}
    (hc : Params.classify c = some (.ctor k)) {ls : List SLevel} :
    ∀ (Ys : List SExpr), Ys.length ≤ k → ∀ {s : TShape},
    LE_Interp ρ s (spine (.const c ls) Ys.reverse) →
    s ≤ TShape.bot ∨ ∃ (n : Nat) (rargs : List (WShape n)) (m' : TShape), s ≤ m' ∧
      LE_Interp.Const c ls (LE_Interp ρ) rargs m' ∧
      List.Forall₂ (fun r Z => LE_Interp ρ r.T Z) rargs Ys := by
  intro Ys
  induction Ys with
  | nil =>
    intro _ s H
    generalize eC : SExpr.const c ls = M at H
    rw [List.reverse_nil, spine_nil] at H
    cases H with
    | bot => exact .inl TShape.bot_eqv.1
    | const h1 h2 h3 h4 h5 h6 h7 =>
      injection eC with e1 e2; subst e1 e2
      exact .inr ⟨_, [], _, h3, h6.mono .rfl (fun hle hR => (h7 _ _ hR).mono hle), .nil⟩
    | bvar | sort | app | lam | forallE => cases eC
  | cons Z Ys ih =>
    intro hlen s H
    rw [List.reverse_cons, spine_snoc] at H
    simp only [List.length_cons] at hlen
    generalize eA : SExpr.app (spine (.const c ls) Ys.reverse) Z = M at H
    cases H with
    | bot => exact .inl TShape.bot_eqv.1
    | bvar | sort | lam | forallE | const => cases eA
    | @app _ n' f _ _ _ a hf hz hle =>
      injection eA with e1 e2; subst e1 e2
      rcases ih (by omega) hf with hb | ⟨n, rargs, m', hfm, hC, hF⟩
      · left; rw [T.le_bot_T hb, WShape.bot_app] at hle; exact hle.trans TShape.bot_eqv.1
      have hlenr : rargs.length = Ys.length := List.Forall₂.length_eq hF
      cases hC with
      | bot =>
        left; rw [T.le_bot_T (hfm.trans TShape.bot_eqv.1), WShape.bot_app] at hle
        exact hle.trans TShape.bot_eqv.1
      | ctor h1 _ => cases hc.symm.trans h1; omega
      | indTy h1 _ => cases hc.symm.trans h1
      | pat hP hM _ =>
        obtain ⟨_, h⟩ := Params.Pat.head_symb hP
        rw [T.matches_head hM, hc] at h; cases h
      | @lam f₂ _ _ hpairs hle₂ =>
        right
        have hK1 : n ≤ max n n' := Nat.le_max_left ..
        have hK2 : n' ≤ max n n' := Nat.le_max_right ..
        have hpK : ∀ x y : WShape (max n n'), (x, y) ∈ f₂.lift (max n n') →
            LE_Interp.Const c ls (LE_Interp ρ) (x :: rargs.map (WShape.lift (max n n'))) y.T := by
          intro x y hxy
          obtain ⟨x₀, y₀, h0, rfl, rfl⟩ := (WShapeFun.mem_lift hK1).1 hxy
          exact ((hpairs x₀ y₀ h0).lift hK1 (fun hle h => h.mono hle)).mono
            (TShape.lift_eqv hK1).1 (fun hle h => h.mono hle)
        have le₁ : f.T ≤ (WShape.lam' (f₂.lift (max n n'))).T := by
          rw [← WShape.lift_lam' hK1]
          exact (hfm.trans hle₂).trans (TShape.lift_eqv (Nat.succ_le_succ hK1)).2
        have le₂ : a.T ≤ (a.lift (max n n')).T := (TShape.lift_eqv hK2).2
        have happ := TShape.app_mono le₁ le₂
        rw [WShape.lam'_app] at happ
        obtain ⟨q, hq, hqm⟩ := (f₂.lift (max n n')).app_eq (a.lift (max n n'))
        refine ⟨max n n', q :: rargs.map (WShape.lift (max n n')), _, hle.trans happ,
          hpK _ _ hqm, .cons ?_ ?_⟩
        · exact hz.mono (hq.T.trans (TShape.lift_eqv hK2).1)
        · exact List.forall₂_map_left_iff.2 <|
            List.Forall₂.imp (fun r Z h => h.mono (TShape.lift_eqv hK1).1) hF

/-- A full ctor spine is interpreted below `ctor' c rs` for argument shapes `rs` (in spine
order) interpreting the arguments. -/
theorem T.ctor_spine_le {ρ : Valuation} {c : Name} {k : Nat}
    (hc : Params.classify c = some (.ctor k)) {ls : List SLevel} {Zs : List SExpr}
    (hlen : Zs.length = k) {s : TShape} (H : LE_Interp ρ s (spine (.const c ls) Zs)) :
    s ≤ TShape.bot ∨ ∃ (n : Nat) (rs : List (WShape n)), s ≤ (WShape.ctor' c rs).T ∧
      List.Forall₂ (fun r Z => LE_Interp ρ r.T Z) rs Zs := by
  rw [← List.reverse_reverse Zs] at H
  rcases T.ctor_spine_bound hc Zs.reverse (by simp [hlen]) H with hb | ⟨n, rargs, m', hsm, hC, hF⟩
  · exact .inl hb
  have hlenr : rargs.length = k := by have := List.Forall₂.length_eq hF; simp at this; omega
  cases hC with
  | bot => exact .inl (hsm.trans TShape.bot_eqv.1)
  | @lam f₂ _ _ hpairs hle₂ =>
    left
    rw [T.lam'_eq_bot fun x y h => TShape.le_bot.1 (T.const_beyond hc (hpairs x y h)
      (by simp; omega))] at hle₂
    exact (hsm.trans hle₂).trans TShape.bot_eqv.1
  | ctor _ h2 =>
    refine .inr ⟨n, rargs.reverse, hsm.trans h2, ?_⟩
    rw [← List.reverse_reverse Zs]; exact List.Forall₂.reverse.2 hF
  | indTy h1 _ => cases hc.symm.trans h1
  | pat hP hM _ =>
    obtain ⟨_, h⟩ := Params.Pat.head_symb hP
    rw [T.matches_head hM, hc] at h; cases h

/-- `ctor'` is monotone across levels. -/
theorem T.ctor'_le_T {c : Name} {n n' : Nat} {rs : List (WShape n)} {ls : List (WShape n')}
    (h : List.Forall₂ (fun r q => r.T ≤ q.T) rs ls) :
    (WShape.ctor' c rs).T ≤ (WShape.ctor' c ls).T := by
  have hK1 : n ≤ max n n' := Nat.le_max_left ..
  have hK2 : n' ≤ max n n' := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ hK1) (Nat.succ_le_succ hK2)]
  dsimp only [WShape.T]
  rw [WShape.lift_ctor' hK1, WShape.lift_ctor' hK2]
  refine WShape.ctor'_le_ctor' ?_
  exact List.forall₂_map_left_iff.2 <| List.forall₂_map_right_iff.2 <|
    List.Forall₂.imp (fun r q hrq => (TShape.LE.def hK1 hK2).1 hrq) h


/-- The core of `LR.Adequate.mono_r`: move a `DefEq` from `(m', a')` to `(m, a)` with `m ≤ m'`
and `a` compatible with `a'` (up through the join, across, down). -/
theorem T.defEq_transfer {Γ₀ : List SExpr} {M N A : SExpr}
    {n n' : Nat} {m a : WShape n} {m' a' : WShape n'}
    (le : m.T ≤ m'.T) (hmem : m.HasType a) (hmem' : m'.HasType a')
    (hc : a.T.Compat a'.T)
    (tyA : (LR Γ₀).TyDefEq A A a) (tyA' : (LR Γ₀).TyDefEq A A a')
    (H : (LR Γ₀).DefEq M N A m' a') : (LR Γ₀).DefEq M N A m a := by
  have hJ := TShape.Join.mk hc
  have ⟨hJ1, hJ2⟩ := (hJ _).1 .rfl
  have hkn : n ≤ max n n' := Nat.le_max_left ..
  have hkn' : n' ≤ max n n' := Nat.le_max_right ..
  have hjk : (a.T.join a'.T).1 ≤ max n n' := Nat.max_le.2 ⟨hkn, hkn'⟩
  have hJ1' := (TShape.LE.def hkn hjk).1 hJ1
  have hJ2' := (TShape.LE.def hkn' hjk).1 hJ2
  have hJ_t := (TShape.HasType.sort_r.2 hmem.isType).join' hJ (TShape.HasType.sort_r.2 hmem'.isType)
  have hmem_k := (WShape.HasType.lift hkn).2 hmem
  have hmem'_k := (WShape.HasType.lift hkn').2 hmem'
  have hJ_t' := TShape.HasType.sort_r.1 <|
    hJ_t.mono_l (TShape.lift_eqv hjk).2 (TShape.lift_eqv hjk).1
  have ha_kty : (WShape.lift (max n n') a).HasType .type := by
    simpa using (WShape.HasType.lift hkn).2 hmem.isType
  have ha'_kty : (WShape.lift (max n n') a').HasType .type := by
    simpa using (WShape.HasType.lift hkn').2 hmem'.isType
  have tyJ := (LR Γ₀).join_ty ((TShape.Compat.def hkn hkn').2 hc) ha_kty ha'_kty
    ((LR.TyDefEq.lift hkn hmem.isType).2 tyA)
    ((LR.TyDefEq.lift hkn' hmem'.isType).2 tyA')
  have tyJ' : (LR Γ₀).TyDefEq A A ((a.T.join a'.T).snd.lift (max n n')) :=
    WShape.lift_self ▸ tyJ
  refine (LR.DefEq.lift hkn hmem).1 <| (LR Γ₀).mono_r_2 hJ1' hmem_k hJ_t' <|
    (LR Γ₀).mono_l ((TShape.LE.def hkn hkn').1 le) (.mono_r hJ1' hJ_t' hmem_k)
      (.mono_r hJ2' hJ_t' hmem'_k) <|
    (LR Γ₀).mono_r_1 hJ2' hmem'_k (.mono_r hJ2' hJ_t' hmem'_k) tyJ' <|
      (LR.DefEq.lift hkn' hmem').2 H

/-- Push closed-type entries onto a `SubstWF` with `Adequate.cons`; each entry's type is strongly
typed in its own tail context in a rank prefix below the WF IH's bound. Entries `(A, x, x', p)`,
innermost first. -/
theorem T.substWF_push {Γ₀ Δ : List SExpr} {σ σ' : Subst} {ρ : Valuation} {K k : Nat}
    (WFIH : LR.WFIH Params.rank Γ₀ k) (hK : K < k) (W : LR.SubstWF Γ₀ σ σ' Δ ρ) :
    ∀ (es : List (SExpr × SExpr × SExpr × TShape)),
    (∀ (j : Nat) (e : SExpr × SExpr × SExpr × TShape), es[j]? = some e → e.1.ClosedN ∧
      (∃ u, IsDefEqStrong (Params.env.below Params.rank K)
        ((es.drop (j+1)).map (·.1) ++ Δ) e.1 e.1 (.sort u)) ∧
      ∃ (n : Nat) (a₁ q : WShape n), e.2.2.2 = q.T ∧ q.HasType a₁ ∧ LE_Interp .nil a₁.T e.1 ∧
        Γ₀ ⊢ e.2.1 ≡ e.2.2.1 : e.1 ∧ (LR Γ₀).DefEq e.2.1 e.2.2.1 e.1 q a₁) →
    LR.SubstWF Γ₀ (es.foldr (fun e τ => τ.cons e.2.1) σ) (es.foldr (fun e τ => τ.cons e.2.2.1) σ')
      (es.map (·.1) ++ Δ) (es.foldr (fun e ρ' => ρ'.push e.2.2.2) ρ)
  | [], _ => W
  | e :: es, H => by
    have W' := T.substWF_push WFIH hK W es fun j e' h => by
      have := H (j+1) e' (by simpa using h)
      simpa using this
    obtain ⟨hcl, ⟨u, HA⟩, n, a₁, q, hp, hq, hA₁, hx, hv⟩ := H 0 e rfl
    simp only [List.drop_succ_cons, List.drop_zero] at HA
    obtain ⟨A, x, x', p⟩ := e
    dsimp only at hcl HA hp hq hA₁ hx hv ⊢
    subst hp
    have hsub : ∀ τ : Subst, A.subst τ = A := fun τ => hcl.subst_eq .zero
    have := LR.Adequate.cons (Γ₀ := Γ₀) (A := A) (A' := A) (u := u)
      (fun hm ha hma => WFIH K hK HA hm ha hma) (HA.mono (Params.env.below_le ..))
      hq ((LE_Interp.closed_iff hcl).1 hA₁) (by rw [hsub]; exact hx) (by rw [hsub]; exact hv) W'
    simpa only [List.foldr_cons, List.map_cons, List.cons_append] using this


/-- `LR.rhs_lower` (E6a) with one more conclusion, read off the same `T.rhs_lower_core` call:
unless the RHS is a variable path not covered by `hhead`'s first disjunct, the RHS shape `mC`
itself is interpreted at `ρ_low`. The proof is `LR.rhs_lower`'s, with the second conjunct of
`T.rhs_lower_core`'s claim kept. -/
theorem T.rhs_lower2 {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name}
    {ls : List SLevel} {R : TShape → SExpr → Prop} (LIH : LR.LocalIH Params.rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e)
    {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} {mC : TShape}
    (hP : Params.Pat p r) (hMt : LE_Interp.Matches p c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1)
    (g : PatGen) (hg : Pattern.gen Params.env Params.rank Params.classify p r.1 = some g)
    {fields : List TShape} {ρ : Valuation} {m : Nat} (hm : g.ctx.length = fields.length + m)
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
      (∀ {n'} {y' a' : WShape n'}, y'.T ≤ mC → y'.HasType a' →
        LE_Interp (Valuation.lower selfs fields ρ m) a'.T
          (SExpr.mkInst ls (g.type.liftN g.self.length)) →
        LE_Interp (Valuation.lower selfs fields ρ m) y'.T (SExpr.mkInst ls g.rhsAbs)) ∧
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
    have C := hclaim 0 W hb hv1 hv2 (hAbs ▸ hroot)
    refine ⟨fun hy hty ha => ?_, fun hv => ?_⟩
    · rw [hAbs]; exact C.1 hy hty ha
    · rw [hAbs]; exact C.2 fun path h => by rw [hshift]; exact hv path h


end Lean4Lean.SExpr
