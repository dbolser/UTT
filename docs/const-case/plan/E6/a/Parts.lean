import Lean4Lean.Experimental.E6.RhsCore
/-! E6: the delta leaf (`T.pat_leaf_delta`) and the pieces of the iota leaf (`pat_defeq`'s
instance, the final `whr`/`conv`/transfer step, the `SExpr` form of (d), field lowering). -/
namespace Lean4Lean.SExpr
variable [Params]

/-- `T.strong_env` for a defeq (`pat_defeq`'s open equation, instantiated at `ls`). -/
theorem T.strong_env_defeq {U : Nat} {Γ : List VExpr} {e₁ e₂ A : VExpr}
    (hΓ : OnCtx Γ (fun Γ A => Params.env.IsType U Γ A))
    (H : Params.env.IsDefEq U Γ e₁ e₂ A) (ls : List SLevel) :
    IsDefEqStrong Params.env (Γ.map (mkInst ls)) (mkInst ls e₁) (mkInst ls e₂) (mkInst ls A) := by
  obtain ⟨vs, hvs, rfl⟩ := SLevel.exists_map_mk ls
  have hS := (VEnv.IsDefEq.strong Params.henv hΓ H).instL hvs
  have := hS.mkSE (CtorProviderE.synE VEnv.LE.rfl) (onCtx_map_instL_levelWF hvs Γ)
  have hctx : Γ.map (mkInst (vs.map SLevel.mk)) = (Γ.map (VExpr.instL vs)).map SExpr.mk := by
    rw [List.map_map]; congr 1; funext B; exact mkInst_map_mk hvs
  rw [hctx, mkInst_map_mk hvs, mkInst_map_mk hvs, mkInst_map_mk hvs]
  exact this

/-- `pat_defeq`'s open equation at `ls`, in `g.ctx` over `Γ₀`. -/
theorem T.pat_defeq_inst {p : Pattern} {r : p.RHS × p.Check} {g : PatGen} {ci : VConstant}
    (hP : Params.Pat p r) (hg : Pattern.gen Params.env Params.rank Params.classify p r.1 = some g)
    (hci : Params.env.constants p.head = some ci) (ls : List SLevel) (Γ₀ : List SExpr) :
    IsDefEqStrong Params.env (g.ctx.map (mkInst ls) ++ Γ₀) (mkInst ls g.lhs) (mkInst ls g.rhs)
      (mkInst ls g.type) := by
  have hΓ : OnCtx g.ctx (fun Γ A => Params.env.IsType ci.uvars Γ A) :=
    (T.onCtx_append_right g.self (Params.pat_typed hP hg hci).1).mono
      (fun h => h.mono (Params.env.below_le ..))
  exact (T.strong_env_defeq hΓ (Params.pat_defeq hP hg hci) ls).weak_append

/-- The last step of the pattern leaf: from the RHS instance's `DefEq` at a typed pair `(y, b)`
above `m`, with `b` compatible with `a`, and typed head reductions of both sides to the RHS
instances, the goal at `(m, a)` (`LogRel.whr`, `conv`, `T.defEq_transfer`). -/
theorem T.finish {Γ₀ : List SExpr} {L L' Rs Rs' A A₁ : SExpr} {n n' : Nat}
    {m a : WShape n} {y b : WShape n'}
    (hL : TWHRedS Γ₀ L Rs A) (hL' : TWHRedS Γ₀ L' Rs' A)
    (D : (LR Γ₀).DefEq Rs Rs' A₁ y b) (hconv : (LR Γ₀).TyDefEq A₁ A b)
    (tyA : (LR Γ₀).TyDefEq A A a)
    (hle : m.T ≤ y.T) (hmem : m.HasType a) (hyb : y.HasType b) (hc : a.T.Compat b.T) :
    (LR Γ₀).DefEq L L' A m a :=
  ((LR Γ₀).whr hL hL').2 <| T.defEq_transfer hle hmem hyb hc tyA
    ((LR Γ₀).left_ty ((LR Γ₀).symm_ty hconv)) ((LR Γ₀).conv hconv D)



/-- Type validity of a constant's (closed) type at every typed shape interpreting it
(`LR.const_local`'s `tyV`). -/
theorem T.tyV_const {Γ₀ : List SExpr} {k : Nat} (WFIH : LR.WFIH Params.rank Γ₀ k)
    (hΓ₀ : ⊢ Γ₀) {c : Name} {ci : VConstant} (hc : Params.rank c < k)
    (hci : Params.env.constants c = some ci) (ls : List SLevel) {n : Nat} {a₁ : WShape n}
    (hA : LE_Interp .nil a₁.T (mkInst ls ci.type)) (ha : a₁.HasType .type) :
    (LR Γ₀).TyDefEq (mkInst ls ci.type) (mkInst ls ci.type) a₁ := by
  obtain ⟨u, Hty₀⟩ := EnvStrongR.of_params.const ls hci
  have Hty := Hty₀.weak0 (Γ := Γ₀)
  obtain ⟨n', a', s, le_n, le_a, hA', hS, hmem'⟩ :=
    ((LE_Interp.soundSE (Params.env.below_le ..) Hty (LR.SubstWF.id hΓ₀).fits).2 hA).out
  have tyDE := (WFIH _ hc Hty hA' hS hmem').2 (LR.SubstWF.id hΓ₀)
  simp only [subst_id] at tyDE
  exact LR.toValTy le_n le_a ha hS hmem' tyDE

/-- The pattern leaf for a delta rule `p = .const c` (`ctx = []`, `Ts = []`). -/
theorem T.pat_leaf_delta {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
    (WFIH : LR.WFIH Params.rank Γ₀ k) {c : Name} {ci : VConstant} {ls : List SLevel}
    (hc : Params.rank c < k) (h1 : Params.env.constants c = some ci) (h2 : ls.length = ci.uvars)
    {R : TShape → SExpr → Prop} (LIH : LR.LocalIH Params.rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e)
    {c₀ : Name} {r : (Pattern.const c₀).RHS × (Pattern.const c₀).Check} {n : Nat}
    {rargs : List (WShape n)} {m2 : (Pattern.const c₀).Path → TShape} {mC : TShape}
    (hP : Params.Pat (.const c₀) r) (hMt : LE_Interp.Matches (.const c₀) c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1) (hchk : r.2 = .true)
    (g : PatGen) (hg : Pattern.gen Params.env Params.rank Params.classify (.const c₀) r.1 = some g)
    {Ts : List SExpr} {B : SExpr} (hT : mkInst ls ci.type = Ts.foldr .forallE B)
    (hk : rargs.length = Ts.length)
    {ρ : Valuation} {σ σ' : Subst}
    (W : LR.SubstWF Γ₀ σ σ' (Ts.reverse ++ Γ₀) ρ)
    {n'} {m a : WShape n'} (le : m.T ≤ mC) (hA : LE_Interp ρ a.T B) (hmem : m.HasType a) :
    (LR Γ₀).DefEq ((openSpine c ls Ts.length).subst σ) ((openSpine c ls Ts.length).subst σ')
      (B.subst σ) m a := by
  have hhd : c = c₀ := (T.matches_head hMt).symm
  subst hhd
  cases hMt
  cases Ts with
  | cons _ _ => cases hk
  | nil =>
  simp only [List.foldr_nil] at hT
  subst hT
  obtain ⟨ci₀, hci₀, hctx, hlhs, htype⟩ := Pattern.gen_delta hg
  cases hci₀.symm.trans h1
  have hcl : (mkInst ls ci.type).ClosedN := (Params.henv.closedC h1).mkInstS
  simp only [List.reverse_nil, List.nil_append] at W
  have hρ : ρ = Valuation.lowerCtx [] ρ 0 := by
    funext i
    have := T.substWF_val W [] rfl i
    simp only [List.length_nil, Nat.zero_add] at this
    rw [this]; rfl
  have Wc : LR.SubstWF Γ₀ σ σ' (g.ctx.map (mkInst ls) ++ Γ₀) (Valuation.lowerCtx [] ρ 0) := by
    rw [hctx, List.map_nil, List.nil_append, ← hρ]; exact W
  obtain ⟨n₁, y, b, hle, hyb, hb, D⟩ := T.rhs_core WFIH hc h1 LIH hR (rargs := ([] : List (WShape n))) hP .const hRHS g hg
    (by rw [hctx]; rfl) Wc (fun path => path.elim) (fun path => path.elim)
    (.inl ⟨le, fun path => path.elim⟩)
  rw [htype, hcl.subst_eq .zero] at D
  rw [htype] at hb
  have hb' : LE_Interp ρ b.T (mkInst ls ci.type) := (LE_Interp.closed_iff hcl).1 hb
  -- the typed reduction `c ls ⤳ rhs`
  have Hd := T.pat_defeq_inst hP hg h1 ls Γ₀
  rw [hctx, hlhs, htype] at Hd
  simp only [List.map_nil, List.nil_append] at Hd
  have hlhs' : mkInst ls (VExpr.const c (VLevel.params ci.uvars)) = .const c ls := by
    simp only [mkInst, SLevel.instV_params h2]
  rw [hlhs'] at Hd
  have hcl0 : (mkInst ls g.rhs).ClosedN := by
    have := (T.pat_defeq_inst hP hg h1 ls []).closedN.2.1
    rwa [hctx] at this
  have hrhs : ∀ τ : Subst, r.1.applyS ls (fun path => τ ((Pattern.const c).pathIdx path)) =
      mkInst ls g.rhs := by
    intro τ
    rw [← Pattern.gen_rhs hg ls _ τ (fun path => path.elim)]
    exact hcl0.subst_eq .zero
  rw [hrhs, hrhs] at D
  have hred : TWHRedS Γ₀ (.const c ls) (mkInst ls g.rhs) (mkInst ls ci.type) := by
    refine ⟨Hd.defeq, .tail .rfl ?_⟩
    have := WHRed.extra' (Γ := Γ₀) hP ((Pattern.MatchesS.const (c := c) (ls := ls)).congr
      (m2' := fun path => σ ((Pattern.const c).pathIdx path)) fun path => path.elim)
      (by rw [hchk]; exact nofun)
    rwa [hrhs] at this
  simp only [openSpine, List.length_nil, List.range_zero, List.reverse_nil, List.map_nil,
    spine_nil, SExpr.subst, hcl.subst_eq .zero]
  have tyb := T.tyV_const WFIH W.wf₀ hc h1 ls ((LE_Interp.closed_iff hcl).1 hb') hyb.isType
  have tya := T.tyV_const WFIH W.wf₀ hc h1 ls ((LE_Interp.closed_iff hcl).1 hA) hmem.isType
  exact T.finish hred hred D tyb tya hle hmem hyb (hA.compat hb')


theorem T.mkInst_subst (ls : List SLevel) : ∀ (e : VExpr) (σ : VExpr.Subst),
    mkInst ls (e.subst σ) = (mkInst ls e).subst (fun i => mkInst ls (σ i))
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .app f a, σ => by simp only [VExpr.subst, mkInst, SExpr.subst, T.mkInst_subst ls f, T.mkInst_subst ls a]
  | .lam A e, σ | .forallE A e, σ => by
    simp only [VExpr.subst, mkInst, SExpr.subst, T.mkInst_subst ls A, T.mkInst_subst ls e]
    congr 2; funext i; cases i with
    | zero => rfl
    | succ i =>
      simp only [VExpr.Subst.lift, SExpr.Subst.lift, VExpr.lift_eq_lift', mkInst_lift']

/-- (d) at the `SExpr` level: the generic type is the body under the substitution sending the
major to the generic ctor spine. -/
theorem T.type_subst (ls : List SLevel) (Bmaj : VExpr) (c' : Name) (us : List VLevel) (k : Nat) :
    mkInst ls ((Bmaj.liftN k 1).inst (VExpr.bvarSpine (.const c' us) k 0)) =
      (mkInst ls Bmaj).subst (Subst.cons (fun i => .bvar (i + k))
        (openSpine c' (us.map (SLevel.instV ls)) k)) := by
  rw [VExpr.inst_eq, VExpr.liftN_subst, T.mkInst_subst]
  congr 1; funext i
  cases i with
  | zero =>
    show mkInst ls (VExpr.bvarSpine (.const c' us) k 0) = _
    rw [mkInst_bvarSpine]; simp [openSpine, mkInst]; rfl
  | succ i =>
    show mkInst ls ((VExpr.Subst.one (VExpr.bvarSpine (.const c' us) k 0))
      ((Lift.consN (.skipN .refl k) 1).liftVar (i+1))) = _
    rw [Lift.liftVar_consN_skipN]
    simp [VExpr.Subst.one, VExpr.Subst.cons, VExpr.Subst.id, mkInst, Subst.cons, liftVar]
    omega

theorem T.hasType_ctor_inv {c : Name} {l : List (WShape n)} {h} {a : WShape (n+1)}
    (H : (WShape.ctor c l h).HasType a) : a = .indTy := by
  cases a using WShape.casesOn' <;> first
    | rfl
    | (exfalso; revert H; simp [WShape.HasType, Shape.HasType, Shape.hasType, WShape.ctor,
        WShape.bot, WShape.sort, WShape.forallE, WShape.lam, WShape.indTy])

theorem T.ctor'_eq_ctor {c : Name} {k : Nat} (hc : Params.classify c = some (.ctor k))
    (l : List (WShape n)) : ∃ h, WShape.ctor' c l = WShape.ctor c l h := by
  have hs : IsStruct c = false := by simp [IsStruct, hc]
  have h : IsStruct c → WShape.ListNonZero l := fun h' => by rw [hs] at h'; cases h'
  exact ⟨h, by rw [WShape.ctor', dif_pos h]⟩

theorem T.forall₂_get {α β : Type} {Rl : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ Rl as bs →
      ∀ (j : Nat) (a : α) (b : β), as[j]? = some a → bs[j]? = some b → Rl a b
  | _, _, .nil, _, _, _, h, _ => by simp at h
  | _, _, .cons h0 _, 0, _, _, ha, hb => by simp at ha hb; subst ha hb; exact h0
  | _, _, .cons _ h1, j+1, a, b, ha, hb => T.forall₂_get h1 j a b (by simpa using ha) (by simpa using hb)

theorem T.forall₂_of_get {α β : Type} {Rl : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, as.length = bs.length →
      (∀ (j : Nat) (a : α) (b : β), as[j]? = some a → bs[j]? = some b → Rl a b) →
      List.Forall₂ Rl as bs
  | [], [], _, _ => .nil
  | a :: as, b :: bs, hl, H => .cons (H 0 a b rfl rfl)
      (T.forall₂_of_get (by simpa using hl) fun j a' b' h1 h2 =>
        H (j+1) a' b' (by simpa using h1) (by simpa using h2))
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

theorem T.fieldsEq_get {Γ : List SExpr} {n : Nat} {IH : LogRel Γ n} :
    ∀ {Ts Xs Ys : List SExpr} {l : List (WShape n)}, LRS.FieldsEq IH Ts Xs Ys l →
      Xs.length = Ts.length ∧ Ys.length = Ts.length ∧ l.length = Ts.length ∧
      ∀ (i : Nat) (A : SExpr), Ts[i]? = some A → ∃ X Y q, Xs[i]? = some X ∧ Ys[i]? = some Y ∧
        l[i]? = some q ∧ Γ ⊢ X ≡ Y : A ∧ LRS.FieldRel IH X Y A q
  | _, _, _, _, .nil => ⟨rfl, rfl, rfl, fun _ _ h => by simp at h⟩
  | _, _, _, _, .cons hxy hrel H => by
    obtain ⟨l1, l2, l3, ih⟩ := T.fieldsEq_get H
    refine ⟨by simp [l1], by simp [l2], by simp [l3], fun i A hA => ?_⟩
    cases i with
    | zero => simp at hA; subst hA; exact ⟨_, _, _, rfl, rfl, rfl, hxy, hrel⟩
    | succ i => simpa using ih i A (by simpa using hA)

/-- A type-typed shape below a `lam'` shape is `⊥`. -/
theorem T.typeShape_le_lam' {m' : TShape} {r : Bool} {f : WShapeFun n}
    (hm : m'.HasType (TShape.sort r)) (hle : m' ≤ (WShape.lam' f).T) : m' ≤ TShape.bot := by
  obtain ⟨nm, w⟩ := m'
  have hw : w.HasType (.sort r) := TShape.HasType.sort_r.1 hm
  cases nm with
  | zero =>
    obtain ⟨⟨⟩ | ⟨⟩, _⟩ := w
    · exact TShape.bot_le'
    · exact absurd hle TShape.sort_not_le_lam'
  | succ nm =>
    cases w using WShape.casesOn' with
    | bot => exact TShape.bot_le'
    | sort => exact absurd hle TShape.sort_not_le_lam'
    | forallE => exact absurd hle TShape.forallE_not_le_lam'
    | indTy => exact absurd hle TShape.indTy_not_le_lam'
    | lam => exact absurd hw WShape.HasType.lam_isType
    | ctor => exact absurd hw WShape.HasType.ctor_isType

theorem T.indTy_T_le {n m : Nat} : (WShape.indTy (n := n)).T ≤ (WShape.indTy (n := m)).T := by
  rw [TShape.LE.def (Nat.succ_le_succ (Nat.le_max_left n m)) (Nat.succ_le_succ (Nat.le_max_right n m))]
  simp only [WShape.T, WShape.lift_indTy]; exact WShape.LE.rfl

/-- An inductive-type constant is interpreted below `indTy`. -/
theorem T.indTy_interp_le {ρ : Valuation} {I : Name} {ls : List SLevel} {j : Nat}
    (hI : Params.classify I = some (.indTy j)) {b : TShape} (H : LE_Interp ρ b (.const I ls)) :
    b ≤ (WShape.indTy (n := 0)).T := by
  generalize eC : SExpr.const I ls = M at H
  cases H with
  | bot => exact TShape.bot_le'
  | bvar | sort | app | lam | forallE => cases eC
  | const h1 h2 h3 h4 h5 h6 h7 =>
    injection eC with e1 e2; subst e1 e2
    obtain ⟨-, u, hty⟩ := Params.indTy_closed hI h1
    rw [hty] at h5
    have hm' := TShape.HasType.mono_r h5.le_sort (TShape.HasType.sort_r.2 .sort) h4
    cases h6 with
    | bot => exact h3.trans TShape.bot_le'
    | lam _ hle => exact h3.trans ((T.typeShape_le_lam' hm' hle).trans TShape.bot_le)
    | ctor h _ => cases hI.symm.trans h
    | indTy _ hle => exact h3.trans (hle.trans T.indTy_T_le)
    | pat hP hM _ =>
      obtain ⟨_, h⟩ := Params.Pat.head_symb hP
      rw [T.matches_head hM, hI] at h; cases h


/-- The lowered field shape (PLAN D4 step 1, E6a): the major's field shape `q` when it is typed
at `indTy` and `indTy` interprets the field type `A`, else `⊥` (a Prop-valued field type, or an
untyped field shape). -/
noncomputable def T.lowF (N : Nat) (A : SExpr) (q : WShape (N+1)) : TShape :=
  @ite _ (LE_Interp .nil (WShape.indTy (n := N)).T A ∧ q.HasType .indTy)
    (Classical.propDecidable _) q.T TShape.bot

theorem T.lowF_le {N : Nat} {A : SExpr} {q : WShape (N+1)} : T.lowF N A q ≤ q.T := by
  unfold T.lowF; split
  · exact .rfl
  · exact TShape.bot_le

/-- A lowered field entry is a typed `SubstWF` entry (`T.substWF_push`'s condition). -/
theorem T.lowF_entry {Γ₀ : List SExpr} {N : Nat} {A X Y : SExpr} {q : WShape (N+1)}
    (hxy : Γ₀ ⊢ X ≡ Y : A) (hrel : LRS.FieldRel (LR Γ₀ (n := N+1)) X Y A q) :
    ∃ (n : Nat) (a₁ q' : WShape n), T.lowF N A q = q'.T ∧ q'.HasType a₁ ∧
      LE_Interp .nil a₁.T A ∧ Γ₀ ⊢ X ≡ Y : A ∧ (LR Γ₀).DefEq X Y A q' a₁ := by
  unfold T.lowF; split
  · next h => exact ⟨N+1, .indTy, q, rfl, h.2, h.1, hxy, hrel q .rfl h.2⟩
  · exact ⟨0, .bot, .bot, rfl, rfl, .bot, hxy, (LR Γ₀).bot rfl⟩

/-- `hvar` at a constructor-field path: a typed shape below the raw field shape whose type
interprets the (inductive-constant) field type lies below the lowered entry. -/
theorem T.hvar_field {N n : Nat} {A : SExpr}
    (hA : ∃ (I : Name) (vs : List SLevel) (j : Nat), A = .const I vs ∧
      Params.classify I = some (.indTy j))
    {q : WShape (N+1)} {y b : WShape n} (hyq : y.T ≤ q.T) (hyb : y.HasType b) {ρ' : Valuation}
    (hb : LE_Interp ρ' b.T A) : y.T ≤ T.lowF N A q := by
  obtain ⟨I, vs, j, rfl, hI⟩ := hA
  have hb' := T.indTy_interp_le hI hb
  cases n with
  | zero =>
    obtain ⟨⟨⟩ | ⟨⟩, _⟩ := b
    · cases hyb.bot_r; exact TShape.bot_le'
    · exfalso
      rw [TShape.LE.def (Nat.zero_le 1) (Nat.le_refl 1)] at hb'
      simp only [WShape.T, WShape.lift_indTy] at hb'
      have := WShape.le_indTy.1 hb'
      rcases this with h | h <;> cases congrArg (·.1) h
  | succ n₁ =>
    rw [TShape.LE.def (Nat.le_refl (n₁+1)) (Nat.succ_le_succ (Nat.zero_le n₁))] at hb'
    simp only [WShape.T, WShape.lift_self, WShape.lift_indTy] at hb'
    rcases WShape.le_indTy.1 hb' with rfl | rfl
    · cases hyb.bot_r; exact TShape.bot_le'
    cases hyb.unfold with
    | bot _ => exact TShape.bot_le'
    | @ctor _ c l wf =>
      have hP1 : LE_Interp .nil (WShape.indTy (n := N)).T (.const I vs) :=
        ((LE_Interp.closed_iff (M := .const I vs) trivial).1 hb).mono T.indTy_T_le
      have hP2 : q.HasType .indTy := by
        have hK1 : n₁ ≤ max n₁ N := Nat.le_max_left ..
        have hK2 : N ≤ max n₁ N := Nat.le_max_right ..
        have h := (TShape.LE.def (Nat.succ_le_succ hK1) (Nat.succ_le_succ hK2)).1 hyq
        dsimp only [WShape.T] at h
        rw [WShape.lift_ctor hK1] at h
        obtain ⟨l', h', hq, -⟩ := WShape.ctor_le.1 h
        have hql : (q.lift (max n₁ N + 1)).HasType ((WShape.indTy (n := N)).lift (max n₁ N + 1)) := by
          rw [hq, WShape.lift_indTy]; exact .ctor
        exact (WShape.HasType.lift (Nat.succ_le_succ hK2)).1 hql
      unfold T.lowF; rw [if_pos ⟨hP1, hP2⟩]; exact hyq

end Lean4Lean.SExpr
