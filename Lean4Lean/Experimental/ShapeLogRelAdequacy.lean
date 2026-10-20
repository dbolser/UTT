import Lean4Lean.Experimental.ShapeLogRel
import Lean4Lean.Experimental.PatternGen

namespace Lean4Lean

namespace SExpr
variable [Params]


def LR.Adequate (Γ₀ Γ : List SExpr) (ρ : Valuation) (M N A : SExpr) (m a : WShape n) :=
  (∀ {{σ σ'}}, LR.SubstWF Γ₀ σ σ' Γ ρ →
    (LR Γ₀).DefEq (M.subst σ) (M.subst σ') (A.subst σ) m a ∧
    (LR Γ₀).DefEq (N.subst σ) (N.subst σ') (A.subst σ) m a) ∧
  ∀ {{σ}}, LR.SubstWF Γ₀ σ σ Γ ρ → (LR Γ₀).DefEq (M.subst σ) (N.subst σ) (A.subst σ) m a

theorem LR.Adequate.bot (ha : a.HasType .type) : Adequate Γ₀ Γ ρ M N A .bot a :=
  ⟨fun _ _ _ => ⟨(LR _).bot ha, (LR _).bot ha⟩, fun _ _ => (LR _).bot ha⟩

theorem LR.Adequate.fits
    (H : ρ.Fits Γ₀ Γ → Adequate Γ₀ Γ ρ M N A m a) : Adequate Γ₀ Γ ρ M N A m a :=
  ⟨fun _ _ W => (H W.fits).1 W, fun _ W => (H W.fits).2 W⟩

theorem LR.Adequate.refl
    (H : ∀ {{σ σ'}}, LR.SubstWF Γ₀ σ σ' Γ ρ →
      (LR Γ₀).DefEq (M.subst σ) (M.subst σ') (A.subst σ) m a) :
    Adequate Γ₀ Γ ρ M M A m a := ⟨fun _ _ W => ⟨H W, H W⟩, fun _ W => H W⟩

theorem LR.Adequate.left : Adequate Γ₀ Γ ρ M N A m a → Adequate Γ₀ Γ ρ M M A m a
  | ⟨h1, _⟩ => .refl fun _ _ W => (h1 W).1

theorem LR.Adequate.symm : Adequate Γ₀ Γ ρ M N A m a → Adequate Γ₀ Γ ρ N M A m a
  | ⟨h1, h2⟩ => ⟨fun _ _ W => (h1 W).symm, fun _ W => (LR _).symm (h2 W)⟩

theorem LR.Adequate.trans :
    Adequate Γ₀ Γ ρ M₁ M₂ A m a → Adequate Γ₀ Γ ρ M₂ M₃ A m a → Adequate Γ₀ Γ ρ M₁ M₃ A m a
  | ⟨a1, a2⟩, ⟨b1, b2⟩ =>
    ⟨fun _ _ W => ⟨(a1 W).1, (b1 W).2⟩, fun _ W => (LR _).trans (a2 W) (b2 W)⟩

theorem LR.Adequate.trans' : Adequate Γ₀ Γ ρ A₁ A₂ (.sort u) a s →
    Adequate Γ₀ Γ ρ A₂ A₃ (.sort v) a (.sort r) → Adequate Γ₀ Γ ρ A₁ A₃ (.sort u) a s
  | ⟨a1, a2⟩, ⟨b1, b2⟩ => by
    refine ⟨fun σ σ' W => ⟨(a1 W).1, ?_⟩, fun _ W => (LR _).trans' (a2 W) (b2 W)⟩
    have h1 := (LR _).trans' (a1 W.left).2 (b2 W.left)
    have h2 := (LR _).trans' (a1 W.symm.left).2 (b2 W.symm.left)
    exact (LR _).trans ((LR _).symm h1) <| (LR _).trans (a1 W).2 h2

theorem LR.Adequate.cons
    (ihA : ∀ {ρ n} {m a : WShape n}, LE_Interp ρ m.T A → LE_Interp ρ a.T (.sort u) →
      m.HasType a → Adequate Γ₀ Γ ρ A A' (sort u) m a)
    (HA : IsDefEqStrong Params.env Γ A A' (.sort u))
    {{k : Nat}} {{a₁ p : WShape k}} {{x x' σ σ' ρ}}
    (hp : p.HasType a₁) (hA₁ : LE_Interp ρ a₁.T A)
    (hx : Γ₀ ⊢ x ≡ x' : A.subst σ) (hv : (LR Γ₀).DefEq x x' (A.subst σ) p a₁)
    (W : SubstWF Γ₀ σ σ' Γ ρ) : SubstWF Γ₀ (σ.cons x) (σ'.cons x') (A :: Γ) (ρ.push p.T) := by
  refine W.cons (fun hA => ?_) hA₁ hp.T HA.defeq.hasType.1 ⟨hx, fun n a' ha' => ?_⟩
  · have ⟨_, _, le_a, hA', hSort, hmem'⟩ := (LE_Interp.soundS HA W.fits).2 hA
    exact ⟨_, le_a, hA', (TShape.HasType.mono_r hSort.le_sort .sort hmem').toType⟩
  have ha' := LE_Interp.weak_iff.1 ha'
  refine ⟨fun ht => ⟨⟨_, HA.defeq.hasType.1.subst W.wf₀ W.toSubstEq⟩, ?_⟩, fun m' hm' ht => ?_⟩
  · have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ := (LE_Interp.soundS HA W.fits).2 ha' |>.out
    refine (TyDefEq.lift le_n ht).1 <| (LR Γ₀).mono_r_2_ty ((TShape.LE.lift_l le_n).1 le_a)
      (WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ht)
      (WShape.HasType.mono_r hSort.le_sort' .sort hmem').toType ?_
    exact (LR Γ₀).toType <| (LR Γ₀).mono_r_1 hSort.le_sort' hmem'
      (.mono_r hSort.le_sort' .sort hmem') .sort ((ihA hA' hSort hmem').1 W).1
  · have le_k := Nat.le_max_left k n; have le_n := Nat.le_max_right k n
    have ht' := (WShape.HasType.lift le_n).2 ht
    have hp' := (WShape.HasType.lift le_k).2 hp
    have hle' := (TShape.LE.def le_n le_k).1 (LE_Interp.bvar_iff.1 hm')
    have hta₁ := WShape.lift_type ▸ (WShape.HasType.lift le_k).2 hp.isType
    have hta' := WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ht.isType
    have hc := hA₁.compat ha'
    have hj := (TShape.Join.def le_k le_n (Nat.le_refl _)).1 (.mk hc)
    rw [TShape.lift_join le_k le_n] at hj
    have ⟨hj1, hj2⟩ := hj.le
    have hJ := hta₁.join' hj hta'
    have hJ' := hJ.mono_r hj1 hp'
    refine (DefEq.lift le_n ht).1 <|
      (LR Γ₀).mono_r_2 hj2 ht' hJ <|
      (LR Γ₀).mono_l hle' (hJ.mono_r hj2 ht') hJ' <|
      (LR Γ₀).mono_r_1 hj1 hp' hJ' ?_ <| (DefEq.lift le_k hp).2 hv
    have valTyA {nd : Nat} {a : WShape nd} (hA : LE_Interp ρ a.T A) (ha : a.HasType .type) :
        (LR Γ₀).TyDefEq (A.subst σ) (A.subst σ) a :=
      have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ := (LE_Interp.soundS HA W.left.fits).2 hA |>.out
      have v2 := (ihA hA' hSort hmem').2 W.left
      have vt := (LR Γ₀).left_ty <| (LR Γ₀).toType <| (LR Γ₀).mono_r_1 hSort.le_sort' hmem'
        (.mono_r hSort.le_sort' .sort hmem') .sort v2
      (TyDefEq.lift le_n ha).1 <| (LR Γ₀).mono_r_2_ty ((TShape.LE.lift_l le_n).1 le_a)
        (WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ha)
        (WShape.HasType.mono_r hSort.le_sort' .sort hmem').toType vt
    refine (LR Γ₀).join_ty ((TShape.Compat.def le_k le_n).2 hc) hta₁ hta' ?_ ?_
    · exact (TyDefEq.lift le_k hp.isType).2 (valTyA hA₁ hp.isType)
    · exact (TyDefEq.lift le_n ht.isType).2 (valTyA ha' ht.isType)

/-- Extract `TyDefEq` from a `DefEq` at sort type. -/
theorem LR.toValTy {m : WShape n'} {b : WShape n} (le_n : n ≤ n') (le_a : b.T ≤ m.T)
    (ht : b.HasType .type) (hSort : LE_Interp ρ a.T (.sort u)) (hmem' : m.HasType a)
    (H : (LR Γ₀).DefEq M N (.sort u) m a) : (LR Γ₀).TyDefEq M N b := by
  have hle := hSort.le_sort'
  refine (LR.TyDefEq.lift le_n ht).1 ?_
  refine (LR Γ₀).mono_r_2_ty ((TShape.LE.lift_l le_n).1 le_a)
    (WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ht)
    (WShape.HasType.mono_r hle .sort hmem').toType ?_
  exact (LR Γ₀).toType <| (LR Γ₀).mono_r_1 hle hmem'
    (.mono_r hle .sort hmem') .sort H

/-- Retype an `Adequate` fact from `(m', a')` down to `(m, a)` with `a` compatible with `a'`
(port of the artifact's `LR.Adequate.mono_r`): up through the join by `mono_r_1`, across by
`mono_l`, down by `mono_r_2`. Type validity at `a'` is an explicit hypothesis (`hAty'`), since
this `LogRel` has no `isType` field. -/
theorem LR.Adequate.mono_r {Γ₀ Γ : List SExpr} {ρ : Valuation} {M N A : SExpr}
    {n n' : Nat} {m a : WShape n} {m' a' : WShape n'}
    (le : m.T ≤ m'.T) (hmem : m.HasType a) (hmem' : m'.HasType a')
    (hc : a.T.Compat a'.T)
    (hAty : ∀ {{σ σ'}}, LR.SubstWF Γ₀ σ σ' Γ ρ → (LR Γ₀).TyDefEq (A.subst σ) (A.subst σ) a)
    (hAty' : ∀ {{σ σ'}}, LR.SubstWF Γ₀ σ σ' Γ ρ → (LR Γ₀).TyDefEq (A.subst σ) (A.subst σ) a')
    (H : Adequate Γ₀ Γ ρ M N A m' a') : Adequate Γ₀ Γ ρ M N A m a := by
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
  have lower : ∀ {M0 N0 : SExpr} {{σ σ'}} (W : LR.SubstWF Γ₀ σ σ' Γ ρ),
      (LR Γ₀).DefEq M0 N0 (A.subst σ) m' a' → (LR Γ₀).DefEq M0 N0 (A.subst σ) m a := by
    intro M0 N0 σ σ' W hv
    have ha_kty : (WShape.lift (max n n') a).HasType .type := by
      simpa using (WShape.HasType.lift hkn).2 hmem.isType
    have ha'_kty : (WShape.lift (max n n') a').HasType .type := by
      simpa using (WShape.HasType.lift hkn').2 hmem'.isType
    have tyJ := (LR Γ₀).join_ty ((TShape.Compat.def hkn hkn').2 hc) ha_kty ha'_kty
      ((TyDefEq.lift hkn hmem.isType).2 (hAty W))
      ((TyDefEq.lift hkn' hmem'.isType).2 (hAty' W))
    have tyJ' : (LR Γ₀).TyDefEq (A.subst σ) (A.subst σ) ((a.T.join a'.T).snd.lift (max n n')) :=
      WShape.lift_self ▸ tyJ
    refine (LR.DefEq.lift hkn hmem).1 <| (LR Γ₀).mono_r_2 hJ1' hmem_k hJ_t' <|
      (LR Γ₀).mono_l ((TShape.LE.def hkn hkn').1 le) (.mono_r hJ1' hJ_t' hmem_k)
        (.mono_r hJ2' hJ_t' hmem'_k) <|
      (LR Γ₀).mono_r_1 hJ2' hmem'_k (.mono_r hJ2' hJ_t' hmem'_k) tyJ' <|
        (LR.DefEq.lift hkn' hmem').2 hv
  exact ⟨fun σ σ' W => ⟨lower W (H.1 W).1, lower W (H.1 W).2⟩, fun σ W => lower W (H.2 W)⟩

/-! ## `EnvStrongR`: rank-bounded strong typings, from `type_below` / `pat_typed` -/

/-- Rank-bounded strong typings of constant types and of each rule's generated RHS (and of its
generated context, entry by entry), all in the prefix `env.below rank (rank head)`. -/
structure EnvStrongR : Prop where
  const : ∀ {c : Name} {ci : VConstant} (ls : List SLevel), Params.env.constants c = some ci →
    ∃ u, IsDefEqStrong (Params.env.below Params.rank (Params.rank c)) []
      (mkInst ls ci.type) (mkInst ls ci.type) (.sort u)
  ctx : ∀ {p : Pattern} {r : p.RHS × p.Check} {g : PatGen} {ci : VConstant} (ls : List SLevel),
    Params.Pat p r → Pattern.gen Params.env Params.rank Params.classify p r.1 = some g →
    Params.env.constants p.head = some ci →
    ∀ (i : Nat) (A : VExpr), (g.self ++ g.ctx)[i]? = some A →
    ∃ u, IsDefEqStrong (Params.env.below Params.rank (Params.rank p.head))
      (((g.self ++ g.ctx).drop (i + 1)).map (mkInst ls)) (mkInst ls A) (mkInst ls A) (.sort u)
  rhs : ∀ {p : Pattern} {r : p.RHS × p.Check} {g : PatGen} {ci : VConstant} (ls : List SLevel),
    Params.Pat p r → Pattern.gen Params.env Params.rank Params.classify p r.1 = some g →
    Params.env.constants p.head = some ci →
    IsDefEqStrong (Params.env.below Params.rank (Params.rank p.head)) ((g.self ++ g.ctx).map (mkInst ls))
      (mkInst ls g.rhsAbs) (mkInst ls g.rhsAbs) (mkInst ls (g.type.liftN g.self.length))

omit [Params] in
theorem onCtx_map_instL_levelWF {U : Nat} {vs : List VLevel} (hvs : ∀ l ∈ vs, l.WF U) :
    ∀ Γ : List VExpr, OnCtx (Γ.map (VExpr.instL vs)) (fun _ A => A.LevelWF U)
  | [] => trivial
  | _ :: Γ => ⟨onCtx_map_instL_levelWF hvs Γ, VExpr.LevelWF.instL hvs⟩

omit [Params] in
theorem OnCtx.getElem? {P : List VExpr → VExpr → Prop} :
    ∀ {Γ : List VExpr} {i : Nat} {A : VExpr}, OnCtx Γ P → Γ[i]? = some A →
      OnCtx (Γ.drop (i + 1)) P ∧ P (Γ.drop (i + 1)) A
  | _ :: _, 0, _, ⟨h1, h2⟩, he => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he; subst he; exact ⟨h1, h2⟩
  | _ :: Γ, i + 1, _, ⟨h1, _⟩, he => OnCtx.getElem? (Γ := Γ) (i := i) h1 (by simpa using he)

/-- The `type_below`/`pat_typed` → strong chain in one prefix: `VEnv.IsDefEq.strong`
(`rank_ordered`), `instL`, then the repo's `mkSE` at `E = env.below rank k`. -/
theorem Params.strong_below {k U : Nat} {Γ : List VExpr} {e A : VExpr}
    (hΓ : OnCtx Γ (fun Γ A => (Params.env.below Params.rank k).IsType U Γ A))
    (H : (Params.env.below Params.rank k).HasType U Γ e A) (ls : List SLevel) :
    IsDefEqStrong (Params.env.below Params.rank k) (Γ.map (mkInst ls))
      (mkInst ls e) (mkInst ls e) (mkInst ls A) := by
  obtain ⟨vs, hvs, rfl⟩ := SLevel.exists_map_mk ls
  have hS := (VEnv.IsDefEq.strong (Params.rank_ordered k) hΓ H).instL hvs
  have := hS.mkSE (CtorProviderE.synE (Params.env.below_le ..)) (onCtx_map_instL_levelWF hvs Γ)
  have hctx : Γ.map (mkInst (vs.map SLevel.mk)) = (Γ.map (VExpr.instL vs)).map SExpr.mk := by
    rw [List.map_map]; congr 1; funext B; exact mkInst_map_mk hvs
  rw [hctx, mkInst_map_mk hvs, mkInst_map_mk hvs]
  exact this

/-- `EnvStrongR.of_params` (Measure6.lean:298), with the repo's `mkSE` (no `hE`). -/
theorem EnvStrongR.of_params : EnvStrongR where
  const := fun ls h1 => by
    obtain ⟨u, hu⟩ := Params.type_below h1
    exact ⟨_, Params.strong_below (Γ := []) trivial hu ls⟩
  ctx := fun ls hP hg h1 i A hA => by
    obtain ⟨h2, ⟨u, hu⟩⟩ := OnCtx.getElem? (Params.pat_typed hP hg h1).1 hA
    exact ⟨_, Params.strong_below h2 hu ls⟩
  rhs := fun ls hP hg h1 =>
    Params.strong_below (Params.pat_typed hP hg h1).1 (Params.pat_typed hP hg h1).2 ls

/-! ## The measure: WF IH, `ConstGoal`, local IH -/

/-- Telescope valuation (docs/const-case/CtorClause.lean:106). -/
def Valuation.ofRargs {n} (rargs : List (WShape n)) : Valuation :=
  rargs.foldr (fun x ρ => ρ.push x.T) .nil

/-- The WF IH of `LR.adequacy_rank` at bound `k`. -/
def LR.WFIH (rank : Name → Nat) (Γ₀ : List SExpr) (k : Nat) : Prop :=
  ∀ k' < k, ∀ {Γ M N A}, IsDefEqStrong (Params.env.below rank k') Γ M N A →
    ∀ {ρ n} {m a : WShape n}, LE_Interp ρ m.T M → LE_Interp ρ a.T A → m.HasType a →
      LR.Adequate Γ₀ Γ ρ M N A m a

/-- `LR.const_local`'s conclusion (PLAN D4) for `hM : LE_Interp ρ mT (.const c ls)`:
`⊥`, or the ∃-typed-upper-bound form. -/
def LR.ConstGoal (Γ₀ : List SExpr) (ρ : Valuation) (mT : TShape) (c : Name) (ls : List SLevel)
    (ci : VConstant) : Prop :=
  (∃ n, mT = (WShape.bot (n := n)).T) ∨
  ∃ (n : Nat) (m' a' : WShape n), mT ≤ m'.T ∧ m'.HasType a' ∧ LE_Interp ρ a'.T (mkInst ls ci.type) ∧
    ∀ {n'} (m a : WShape n'), m.T ≤ m'.T → LE_Interp ρ a.T (mkInst ls ci.type) → m.HasType a →
      (LR Γ₀).DefEq (.const c ls) (.const c ls) (mkInst ls ci.type) m a

/-- The local IH for the `R`-premise of `LE_Interp.const`: same-rank bare-constant leaves. -/
def LR.LocalIH (rank : Name → Nat) (Γ₀ : List SExpr) (ρ₀ : Valuation) (c : Name)
    (R : TShape → SExpr → Prop) : Prop :=
  ∀ m e, R m e → ∀ c' ls' ci', e = .const c' ls' → rank c' = rank c →
    Params.env.constants c' = some ci' → ls'.length = ci'.uvars → LR.ConstGoal Γ₀ ρ₀ m c' ls' ci'

/-- The E6 interface (R10 proves exactly this; R9 calls it at `Const.pat`), `PatLeafStmt2.lean:168`
with the real `Pattern.gen`, the repo's `IsDefEqStrong E`, and E6a's `hR`. -/
theorem LR.pat_leaf_1a {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
    (WFIH : LR.WFIH Params.rank Γ₀ k) {c : Name} {ci : VConstant} {ls : List SLevel}
    (hc : Params.rank c < k) (h1 : Params.env.constants c = some ci) (h2 : ls.length = ci.uvars)
    {R : TShape → SExpr → Prop} (LIH : LR.LocalIH Params.rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e)
    {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} {mC : TShape}
    (hP : Params.Pat p r) (hMt : LE_Interp.Matches p c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1) (hchk : r.2 = .true)
    (g : PatGen) (hg : Pattern.gen Params.env Params.rank Params.classify p r.1 = some g)
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
      (LR Γ₀).TyDefEq (B.subst τ) (B.subst τ') a) :
    (LR Γ₀).DefEq ((openSpine c ls Ts.length).subst σ) ((openSpine c ls Ts.length).subst σ')
      (B.subst σ) m a := by
  sorry -- SORRY(E3): pat leaf (E6/R10)

/-! ### The spine lemma (PLAN D4, R9) -/

/-- The head of a matched pattern is the constant matched. -/
theorem LE_Interp.Matches.head {p : Pattern} {n} {c : Name} {rargs : List (WShape n)} {m}
    (H : LE_Interp.Matches p c rargs m) : p.head = c := by
  induction H with
  | const => rfl
  | var _ ih => exact ih
  | app _ _ ih _ => exact ih

/-- A successor-level shape below `indTy` is `⊥` or `indTy`. -/
theorem le_indTy_succ {k j : Nat} {s : WShape (k+1)}
    (h : s.T ≤ (WShape.indTy : WShape (j+1)).T) : s = .bot ∨ s = .indTy := by
  have l1 : k + 1 ≤ max k j + 1 := Nat.succ_le_succ (Nat.le_max_left ..)
  have l2 : j + 1 ≤ max k j + 1 := Nat.succ_le_succ (Nat.le_max_right ..)
  have h' := (TShape.LE.def l1 l2).1 h
  rw [WShape.lift_indTy] at h'
  obtain e | e := WShape.le_indTy.1 h'
  · exact .inl ((WShape.lift_eq_bot l1).1 e)
  · refine .inr (WShape.indTy_le.1 ?_)
    rw [← WShape.lift_le_lift l1, e, WShape.lift_indTy]; exact WShape.LE.rfl

theorem sort_not_le_indTy {n j : Nat} {r : Bool} :
    ¬ (WShape.sort r : WShape n).T ≤ (WShape.indTy : WShape (j+1)).T := by
  intro h
  have l1 : n ≤ max n j + 1 := Nat.le_succ_of_le (Nat.le_max_left ..)
  have l2 : j + 1 ≤ max n j + 1 := Nat.succ_le_succ (Nat.le_max_right ..)
  have h' := (TShape.LE.def l1 l2).1 h
  rw [WShape.lift_sort, WShape.lift_indTy] at h'
  obtain e | e := WShape.le_indTy.1 h' <;> cases congrArg (·.1) e

/-- `foldr .forallE` injectivity at equal telescope lengths (`SExpr` form). -/
theorem foldr_forallE_inj : ∀ {Hs Hs' : List SExpr} {B B' : SExpr}, Hs.length = Hs'.length →
    Hs.foldr .forallE B = Hs'.foldr .forallE B' → Hs = Hs' ∧ B = B'
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | A :: Hs, A' :: Hs', _, _, hl, h => by
    simp only [List.foldr_cons, SExpr.forallE.injEq] at h
    obtain ⟨h1, h2⟩ := foldr_forallE_inj (by simpa using hl) h.2
    exact ⟨by rw [h.1, h1], h2⟩

/-- A telescope whose tail is not a Π is maximal: any other `foldr .forallE` decomposition of the
same expression is no longer. -/
theorem foldr_forallE_len_le : ∀ {Hs Ts : List SExpr} {B₁ B₂ : SExpr},
    (∀ X Y, B₂ ≠ .forallE X Y) → Hs.foldr .forallE B₁ = Ts.foldr .forallE B₂ →
    Hs.length ≤ Ts.length
  | [], _, _, _, _, _ => Nat.zero_le _
  | _ :: _, [], _, _, hB, h => by simp only [List.foldr_cons, List.foldr_nil] at h; cases hB _ _ h.symm
  | _ :: Hs, _ :: Ts, _, _, hB, h => by
    simp only [List.foldr_cons, SExpr.forallE.injEq] at h
    simpa using foldr_forallE_len_le (Hs := Hs) (Ts := Ts) hB h.2

omit [Params] in
/-- `VExpr` form: two telescopes with non-Π tails agree. -/
theorem vfoldr_forallE_inj : ∀ {Hs Hs' : List VExpr} {B B' : VExpr},
    (∀ X Y, B ≠ .forallE X Y) → (∀ X Y, B' ≠ .forallE X Y) →
    Hs.foldr .forallE B = Hs'.foldr .forallE B' → Hs = Hs' ∧ B = B'
  | [], [], _, _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, hB, _, h => by cases hB _ _ h
  | _ :: _, [], _, _, _, hB', h => by cases hB' _ _ h.symm
  | A :: Hs, A' :: Hs', _, _, hB, hB', h => by
    simp only [List.foldr_cons, VExpr.forallE.injEq] at h
    obtain ⟨h1, h2⟩ := vfoldr_forallE_inj hB hB' h.2
    exact ⟨by rw [h.1, h1], h2⟩

omit [Params] in
theorem vfoldr_app_ne_forallE {h : VExpr} (hh : ∀ X Y, h ≠ .forallE X Y) :
    ∀ (args : List VExpr) X Y, args.foldr (fun A acc => acc.app A) h ≠ .forallE X Y
  | [], _, _ => hh _ _
  | _ :: _, _, _ => by simp only [List.foldr_cons]; exact fun h => by cases h

omit [Params] in
theorem vfoldr_app_eq_const {I I' : Name} {us us' : List VLevel} :
    ∀ (args : List VExpr), args.foldr (fun A (acc : VExpr) => acc.app A) (VExpr.const I us) =
      VExpr.const I' us' →
      args = [] ∧ I = I'
  | [], h => by cases h; exact ⟨rfl, rfl⟩
  | _ :: _, h => nomatch h

/-- The stage-1a constructor data: the constructor's type is `Fs.foldr .forallE (.const I …)`
with `Fs` of the classified arity, `I` an inductive with no indices, each field type a closed
inductive constant. -/
theorem ctor_data {c : Name} {k : Nat} {ci : VConstant}
    (hcl : Params.classify c = some (.ctor k)) (h1 : Params.env.constants c = some ci) :
    ∃ (I : Name) (Fs : List VExpr), Fs.length = k ∧ Params.classify I = some (.indTy 0) ∧
      ci.type = Fs.foldr .forallE (.const I (VLevel.params ci.uvars)) ∧
      ∀ T ∈ Fs, ∃ (I' : Name) (us : List VLevel), T = .const I' us ∧
        Params.classify I' = some (.indTy 0) := by
  obtain ⟨I, Fs, e1, hF⟩ := Params.ctor_fields_closed (cl := .ctor k) rfl hcl h1
  obtain ⟨I₂, Fs₂, args, hl, hI₂, e2⟩ := Params.ctor_syn (cl := .ctor k) rfl hcl h1
  obtain ⟨rfl, e3⟩ := vfoldr_forallE_inj (fun _ _ h => by cases h)
    (vfoldr_app_ne_forallE (fun _ _ h => by cases h) args) (e1.symm.trans e2)
  obtain ⟨rfl, rfl⟩ := vfoldr_app_eq_const args e3.symm
  exact ⟨_, Fs, hl, hI₂, e1, hF⟩

theorem indTy_not_le_ctor' {n j : Nat} {c : Name} {l : List (WShape j)} :
    ¬ (WShape.indTy : WShape (n+1)).T ≤ (WShape.ctor' c l).T := by
  intro h
  have l1 : n + 1 ≤ max n j + 1 := Nat.succ_le_succ (Nat.le_max_left ..)
  have l2 : j + 1 ≤ max n j + 1 := Nat.succ_le_succ (Nat.le_max_right ..)
  have h' := (TShape.LE.def l1 l2).1 h
  rw [WShape.lift_indTy, WShape.lift_ctor' (Nat.le_max_right ..), WShape.indTy_le] at h'
  unfold WShape.ctor' at h'; split at h' <;> cases congrArg (·.1) h'

/-- A constructor shape below a `ctor'` shape: same constructor, fields pointwise below. -/
theorem ctor_le_ctor'_T {j n : Nat} {c c' : Name} {l : List (WShape j)} {h}
    {L : List (WShape n)} (H : (WShape.ctor c' l h).T ≤ (WShape.ctor' c L).T) :
    c' = c ∧ List.Forall₂ (fun x y => x.T ≤ y.T) l L := by
  have l1 : j ≤ max j n := Nat.le_max_left ..
  have l2 : n ≤ max j n := Nat.le_max_right ..
  have H' := (TShape.LE.def (Nat.succ_le_succ l1) (Nat.succ_le_succ l2)).1 H
  rw [WShape.lift_ctor l1, WShape.lift_ctor' l2, WShape.ctor_le] at H'
  obtain ⟨l', h', e, hle⟩ := H'
  unfold WShape.ctor' at e; split at e
  · rw [WShape.ctor.inj] at e; obtain ⟨rfl, rfl⟩ := e
    refine ⟨rfl, ?_⟩
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff] at hle
    exact Lean4Lean.List.Forall₂.imp (fun _ _ hxy => (TShape.LE.def l1 l2).2 hxy) hle
  · cases congrArg (·.1) e

/-- Above a typed constructor shape, the type is (above) `indTy`. -/
theorem indTy_le_of_ctor_le {j : Nat} {c : Name} {l : List (WShape j)} {h} {x a : TShape}
    (H : (WShape.ctor c l h).T ≤ x) (hx : x.HasType a) :
    (WShape.indTy : WShape (j+1)).T ≤ a := by
  let K := max j (max x.1 a.1)
  have hK := Nat.max_le.1 (Nat.le_refl K); rw [Nat.max_le] at hK
  have l1 : j + 1 ≤ K + 1 := Nat.succ_le_succ hK.1
  have lx : x.1 ≤ K + 1 := Nat.le_succ_of_le hK.2.1
  have la : a.1 ≤ K + 1 := Nat.le_succ_of_le hK.2.2
  have H' := (TShape.LE.def l1 lx).1 H
  rw [WShape.lift_ctor hK.1, WShape.ctor_le] at H'
  obtain ⟨l', h', e, _⟩ := H'
  have hx' := (TShape.HasType.def lx la).1 hx
  rw [e] at hx'
  refine (TShape.LE.def l1 la).2 ?_
  rw [WShape.lift_indTy]
  generalize a.2.lift (K+1) = a' at hx'
  cases a' using WShape.casesOn' with
  | indTy => exact WShape.LE.rfl
  | bot => cases congrArg (·.1) (WShape.HasType.bot_r hx')
  | sort => exact absurd hx' WShape.HasType.ctor_isType
  | forallE => exact absurd hx' WShape.HasType.ctor_not_forallE
  | lam => exact absurd hx' nofun
  | ctor => exact absurd hx' nofun

theorem LRS.FieldsEq.snoc {Γ : List SExpr} {j : Nat} {IH : LogRel Γ j} {X Y T : SExpr} {p : WShape j}
    (hXY : Γ ⊢ X ≡ Y : T) (hp : LRS.FieldRel IH X Y T p) :
    ∀ {Ts Xs Ys l}, LRS.FieldsEq IH Ts Xs Ys l →
      LRS.FieldsEq IH (Ts ++ [T]) (Xs ++ [X]) (Ys ++ [Y]) (l ++ [p])
  | _, _, _, _, .nil => .cons hXY hp .nil
  | _, _, _, _, .cons h1 h2 h3 => .cons h1 h2 (LRS.FieldsEq.snoc hXY hp h3)

theorem range_succ_map (σ : Subst) (k : Nat) :
    (List.range (k+1)).reverse.map σ = (List.range k).reverse.map σ.tail ++ [σ.head] := by
  simp [List.range_succ_eq_map, List.map_reverse, List.map_map, Function.comp_def, Subst.tail,
    Subst.head]

/-- One closed field of a `SubstWF` entry is a `FieldRel` at every shape below the entry's
valuation slot: typed `q' ≤ q` at `indTy` is `⊥` (trivial) or a constructor shape, which forces the
entry's type shape `a` above `indTy`, so `Subst1` applies at `indTy`. -/
theorem LR.fieldRel_of_entry {Γ₀ : List SExpr} {j : Nat} {G X X' : SExpr} {τ τ' : Subst}
    {ρ' : Valuation} {x a : TShape} {q : WShape j}
    (hG : ClosedN G) (hGa : LE_Interp ρ' a G) (hxa : x.HasType a)
    (hS1 : LR.Subst1 Γ₀ X X' G.lift (G.subst τ) (G.subst τ') (ρ'.push x))
    (hq : q.T ≤ x) : LRS.FieldRel (LR Γ₀ (n := j)) X X' G q := by
  cases j with
  | zero => trivial
  | succ j =>
    intro q' hq' ht'
    cases ht'.unfold with
    | bot h => exact (LR Γ₀).bot h
    | @ctor _ c l wf =>
      have hx := (WShape.LE.T hq').trans hq
      have hIa := indTy_le_of_ctor_le hx hxa
      have := ((hS1.2 (n := j+1) WShape.indTy (LE_Interp.weak (hGa.mono hIa))).2
        (m := WShape.ctor c l wf) (LE_Interp.bvar hx) WShape.HasType.ctor)
      rwa [hG.subst_eq .zero] at this

/-- The constructor fields of a telescope of closed types, read off a `SubstWF` entry by entry
(the context is `Gs ++ Γ₀`, newest entry first; the fields come out oldest first). -/
theorem LR.fieldsEq_of_W {Γ₀ : List SExpr} {j : Nat} :
    ∀ (Gs : List SExpr) {σ σ' : Subst} {ρ : Valuation} {n : Nat} {rargs : List (WShape n)}
      {L : List (WShape j)},
    (∀ T ∈ Gs, ClosedN T) →
    LR.SubstWF Γ₀ σ σ' (Gs ++ Γ₀) ρ → (Valuation.ofRargs rargs).LE ρ →
    List.Forall₂ (fun x y => x.T ≤ y.T) L rargs →
    rargs.length = Gs.length →
    LRS.FieldsEq (LR Γ₀ (n := j)) Gs.reverse ((List.range Gs.length).reverse.map σ)
      ((List.range Gs.length).reverse.map σ') L.reverse
  | [], _, _, _, _, rargs, L, _, _, _, hL, hlen => by
    obtain rfl : rargs = [] := List.eq_nil_of_length_eq_zero hlen
    cases hL; exact .nil
  | G :: Gs, σ, σ', ρ, n, rargs, L, hcl, W, hρ, hL, hlen => by
    obtain _ | ⟨r, rargs⟩ := rargs; · cases hlen
    obtain _ | ⟨hq, hL⟩ := hL
    generalize eΓ : (G :: Gs) ++ Γ₀ = Γ at W
    cases W with
    | id _ => exact absurd (congrArg List.length eΓ) (by simp; omega)
    | cons W' _ hGa hxa _ hS1 =>
      simp only [List.cons_append, List.cons.injEq] at eΓ; obtain ⟨rfl, rfl⟩ := eΓ
      have ⟨hρ', hrx⟩ := Valuation.LE.push.1 (show ((Valuation.ofRargs rargs).push r.T).LE _ from hρ)
      have hG := hcl G (.head _)
      have IH := LR.fieldsEq_of_W Gs (fun T h => hcl T (.tail _ h)) W' hρ' hL
        (by simpa using hlen)
      have hEq := hS1.1; rw [hG.subst_eq .zero] at hEq
      rw [List.reverse_cons, List.reverse_cons, List.length_cons, range_succ_map,
        range_succ_map]
      exact LRS.FieldsEq.snoc hEq (LR.fieldRel_of_entry hG hGa hxa hS1 (hq.trans hrx)) IH

theorem closedN_foldr {B : SExpr} (hB : ClosedN B) :
    ∀ {Ts : List SExpr}, (∀ T ∈ Ts, ClosedN T) → ClosedN (Ts.foldr .forallE B)
  | [], _ => hB
  | T0 :: _, h => ⟨h T0 (.head _), (closedN_foldr hB fun T' h' => h T' (.tail _ h')).mono
      (Nat.zero_le _)⟩

/-- A spine over a closed non-dependent telescope, from the fields' equations. -/
theorem spine_typed {Γ : List SExpr} {j : Nat} {IH : LogRel Γ j} {B : SExpr} (hB : ClosedN B) :
    ∀ {Ts Xs Ys : List SExpr} {l}, LRS.FieldsEq IH Ts Xs Ys l → (∀ T ∈ Ts, ClosedN T) →
    ∀ {h h' : SExpr}, Γ ⊢ h ≡ h' : Ts.foldr .forallE B → Γ ⊢ spine h Xs ≡ spine h' Ys : B
  | _, _, _, _, .nil, _, _, _, H => H
  | T0 :: Ts, _, _, _, .cons hXY _ hF, hcl, _, _, H => by
    have hcl' : ∀ T ∈ Ts, ClosedN T := fun T' h' => hcl T' (.tail _ h')
    have H' := IsDefEq.appDF H hXY
    rw [SExpr.inst, (closedN_foldr hB hcl').subst_eq .zero] at H'
    exact spine_typed hB hF hcl' H'

/-- Beyond the syntactic telescope every `Const` output is `⊥`, given the three arity bounds
(from docs/const-case/plan/historical/Beyond.lean, verbatim). -/
theorem Const.beyond {c : Name} {ls : List SLevel} {R : TShape → SExpr → Prop} {n N : Nat}
    (hctor : ∀ k, Params.classify c = some (.ctor k) → k ≤ N)
    (hind : ∀ k, Params.classify c = some (.indTy k) → k ≤ N)
    (hpat : ∀ {p : Pattern} {r : p.RHS × p.Check} {rargs' : List (WShape n)} {m'},
      Params.Pat p r → LE_Interp.Matches p c rargs' m' → rargs'.length ≤ N)
    {rargs : List (WShape n)} {m : TShape}
    (H : LE_Interp.Const c ls R rargs m) (hlen : N < rargs.length) : m ≤ TShape.bot := by
  induction H with
  | bot => exact TShape.bot_le'
  | @lam f rargs m _ h2 ih =>
    have hf : ¬ f.NonZero := by
      intro hnz
      obtain ⟨⟨x, y⟩, hmem, hy⟩ := WShapeFun.NonZero.iff.1 hnz
      have hy' := ih x y hmem (by simp; omega)
      exact hy (WShape.LE.of_T (hy'.trans TShape.bot_eqv.2))
    have : WShape.lam' f = .bot := by simp [WShape.lam', hf]
    rw [this] at h2; exact h2.trans TShape.bot_eqv.1
  | ctor h1 _ => have := hctor _ h1; omega
  | indTy h1 _ => have := hind _ h1; omega
  | pat h1 h2 _ => have := hpat h1 h2; omega

/-- The three arity bounds of `Const.beyond` at `N = Ts.length`, when the remaining type `B` is
not syntactically a Π: ctor arity by `ctor_syn`/`ctor_fields_closed` (via `ctor_data`, needs
only that the tails are not Π), indTy arity `0` by `indTy_closed`, pattern arity by
`Params.pat_arity` (spec lemma (e)). -/
theorem beyond_bounds {c : Name} {ci : VConstant} {ls : List SLevel} {Ts : List SExpr}
    {B : SExpr} (h1 : Params.env.constants c = some ci)
    (hT : mkInst ls ci.type = Ts.foldr .forallE B) (hB : ∀ X Y, B ≠ .forallE X Y) :
    (∀ k, Params.classify c = some (.ctor k) → k ≤ Ts.length) ∧
    (∀ k, Params.classify c = some (.indTy k) → k ≤ Ts.length) ∧
    (∀ {n} {p : Pattern} {r : p.RHS × p.Check} {rargs' : List (WShape n)} {m'},
      Params.Pat p r → LE_Interp.Matches p c rargs' m' → rargs'.length ≤ Ts.length) := by
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun hP hM => ?_⟩
  · obtain ⟨_, Fs, _, hl, _, e⟩ := Params.ctor_syn (cl := .ctor k) rfl hk h1
    rw [e, mkInst_foldr_forallE] at hT
    simpa [hl, Classification.arity] using foldr_forallE_len_le hB hT
  · exact (Params.indTy_closed hk h1).1 ▸ Nat.zero_le _
  · have e := LE_Interp.Matches.head hM
    have hA := hM.arity; rw [← e] at hA
    obtain ⟨Hs, B', hl, e'⟩ := Params.pat_arity hP (e ▸ h1) hA
    rw [e', mkInst_foldr_forallE] at hT
    simpa [hl] using foldr_forallE_len_le hB hT

/-- The last domain of a strongly typed telescope, in its telescope context. -/
theorem tel_last {E : VEnv} {A B : SExpr} :
    ∀ {Ts : List SExpr} {Γ : List SExpr}, TelStrongE E Γ (Ts ++ [A]) B →
      ∃ u, IsDefEqStrong E (Ts.reverse ++ Γ) A A (.sort u)
  | [], _, .cons hA _ => ⟨_, hA⟩
  | T0 :: Ts, Γ, .cons _ H => by
    obtain ⟨u, h⟩ := tel_last (Ts := Ts) H
    exact ⟨u, by simpa using h⟩

theorem subst_tail_cons_head (σ : Subst) : σ.tail.cons σ.head = σ := by
  funext i; cases i <;> rfl

theorem openSpine_succ (c : Name) (ls : List SLevel) (k : Nat) (σ : Subst) (x : SExpr) :
    (openSpine c ls (k+1)).subst (σ.cons x) = ((openSpine c ls k).subst σ).app x := by
  rw [openSpine_subst, openSpine_subst, range_succ_map, spine_snoc]; rfl

/-- The `f`-pair above a typed input: `lam' g ≤ lam' f` at levels `j`, `n`, and `p : WShape j`
give `(x₀, y₀) ∈ f` with `x₀ ≤ p` and `g p ≤ y₀` (as `TShape`s). -/
theorem lam_pair {j n : Nat} {g : WShapeFun j} {f : WShapeFun n}
    (H : (WShape.lam' g).T ≤ (WShape.lam' f).T) (p : WShape j) :
    ∃ x₀ y₀, (x₀, y₀) ∈ f ∧ x₀.T ≤ p.T ∧ (g.app p).T ≤ y₀.T := by
  have l1 : j ≤ max j n := Nat.le_max_left ..
  have l2 : n ≤ max j n := Nat.le_max_right ..
  have hgf := TShape.LE.lam'_decomp H
  obtain ⟨x'', hx'', hmem⟩ := WShapeFun.app_eq (f.lift (max j n)) (p.lift (max j n))
  obtain ⟨x₀, y₀, hm, rfl, e⟩ := (WShapeFun.mem_lift l2).1 hmem
  refine ⟨x₀, y₀, hm, (TShape.LE.def l2 l1).2 hx'', (TShape.LE.def l1 l2).2 ?_⟩
  rw [WShapeFun.lift_app l1, ← e]
  exact WShapeFun.app_mono_l hgf _

/-- `ValTyPi2` between syntactic Π types: the components, with the reflexive typed reduction. -/
theorem valTyPi2_forallE {Γ : List SExpr} {j : Nat} {IH : LogRel Γ j} {X₁ Y₁ X₂ Y₂ : SExpr}
    {b : WShape j} {f : WShapeFun j}
    (H : LRS.ValTyPi2 IH (.forallE X₁ Y₁) (.forallE X₂ Y₂) b f) :
    (∃ u, Γ ⊢ X₁ ≡ X₂ : .sort u) ∧ (∃ v, X₁ :: Γ ⊢ Y₁ ≡ Y₂ : .sort v) ∧
      IH.TyDefEq X₁ X₂ b ∧ LRS.PiDefEq IH X₁ Y₁ Y₂ b f ∧
      TyRedS Γ (.forallE X₁ Y₁) (.forallE X₁ Y₁) := by
  obtain ⟨_, _, _, _, u, v, r1, r2, e1, e2, t, P⟩ := H
  cases WHNF.forallE.whRedS r1.2; cases WHNF.forallE.whRedS r2.2
  exact ⟨⟨u, e1⟩, ⟨v, e2⟩, t, P, r1⟩

theorem push_inj {ρ ρ' : Valuation} {x x' : TShape} (h : ρ.push x = ρ'.push x') :
    ρ = ρ' ∧ x = x' := ⟨funext fun i => congrFun h (i+1), congrFun h 0⟩

/-- Type validity one binder further, from `PiDefEq` of the Π's type validity on the tail. -/
theorem LR.tyV_succ {Γ₀ Δ : List SExpr} {ρ : Valuation} {A' B' : SExpr} {j : Nat}
    {a₁ p : WShape j} {a₂ : WShapeFun j} (hp : p.HasType a₁) (hA₁ : LE_Interp ρ a₁.T A')
    (tyV : ∀ {τ τ'}, LR.SubstWF Γ₀ τ τ' (Δ ++ Γ₀) ρ →
      (LR Γ₀).TyDefEq ((SExpr.forallE A' B').subst τ) ((SExpr.forallE A' B').subst τ')
        (WShape.forallE a₁ a₂)) :
    ∀ {τ τ'}, LR.SubstWF Γ₀ τ τ' (A' :: (Δ ++ Γ₀)) (ρ.push p.T) →
      (LR Γ₀).TyDefEq (B'.subst τ) (B'.subst τ') (a₂.app p) := by
  intro τ τ' W₁
  generalize eρ : ρ.push p.T = ρ₁ at W₁
  generalize eΓ : A' :: (Δ ++ Γ₀) = Γ₁ at W₁
  cases W₁ with
  | id _ => exact absurd (congrArg List.length eΓ) (by simp; omega)
  | cons W₁' _ _ _ _ hS1 =>
    injection eΓ with eA eΓ'; subst eA eΓ'
    obtain ⟨rfl, rfl⟩ := push_inj eρ
    have hv := (hS1.2 a₁ (LE_Interp.weak hA₁)).2 (m := p) (.bvar .rfl) hp
    have hty := tyV W₁'
    simp only [LR, LRS, LRS.TyDefEq.forallE_iff, SExpr.subst] at hty
    obtain ⟨_, _, _, P, _⟩ := valTyPi2_forallE hty
    have t1 := (P.1 hp hS1.1 hv).1
    have t2 := P.2 hp hS1.1.hasType.2 ((LR Γ₀).left ((LR Γ₀).symm hv))
    rw [inst_lift_cons, inst_lift_cons] at t1 t2
    have := (LR Γ₀).trans_ty t1 t2
    rwa [subst_tail_cons_head, subst_tail_cons_head] at this

/-- The spine lemma (R9; PLAN D4, `PatLeafStmt2.lean`): induction on `Const`, at every valuation
above the telescope valuation that a `SubstWF` covers, goal at every typed shape below. `hR`
(the `R`-premise of `LE_Interp.const` is interpreted at `ρ₀`) was added by experiment E6a: without
it the pattern leaf is false (a fixed leaf that is not a self occurrence is unconstrained).

Proved by induction on the `Const` derivation (PLAN D4, "The spine lemma (item R9)"; §4 Q7):
* `bot`: `m = ⊥`.
* `lam`: if `B` is not syntactically a Π, every output of the graph is `⊥` (`Const.beyond`, with
  the three arity bounds `beyond_bounds`), so `m = ⊥`. If `B = .forallE A' B'`, the
  `(lam, forallE)` row: the Π data from `tyV` (`valTyPi2_forallE`), `LamDefEq` from the IH at the
  graph pair above each typed input (`lam_pair`), at `ρ.push p`, with `Adequate.cons` for the next
  domain `A'` (strong typing from `EnvStrongR.of_params.const` + `IsDefEqStrong.telescope` +
  `tel_last` + `weak_append`; its IH is the WF IH at `rank c < k`) and the next `tyV` from
  `PiDefEq` (`LR.tyV_succ`).
* `ctor`: the `(ctor c l, indTy)` row is `CtorDefEq`: the stage-1a type (`ctor_data`: `ctor_syn` +
  `ctor_fields_closed` + `indTy_closed`) fixes `B = .const I ls` and closed fields; the fields are
  read off `W` entry by entry (`LR.fieldsEq_of_W`, `LR.fieldRel_of_entry`), the spines are typed
  from the fields' equations (`spine_typed`), the ambient reduction is typed from `tyV`.
* `indTy`: `rargs = Ts = []`, `B` a sort, row `(indTy, sort)` through `LRS.TyDefEq`'s `indTy` row.
* `pat`: `LR.pat_leaf_1a`, the remaining stub (E6/R10). -/
theorem LR.const_spine {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
    (WFIH : LR.WFIH Params.rank Γ₀ k) {c : Name} {ci : VConstant} {ls : List SLevel}
    (hc : Params.rank c < k) (h1 : Params.env.constants c = some ci) (h2 : ls.length = ci.uvars)
    {R : TShape → SExpr → Prop} (LIH : LR.LocalIH Params.rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e)
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
  induction hC generalizing Ts B ρ σ σ' n' m a with
  | bot =>
    cases show m = .bot from TShape.le_bot.1 (le.trans TShape.bot_eqv.1)
    exact (LR _).bot hmem.isType
  | @lam f rargs mC hf hle ih =>
    by_cases hB : ∃ A' B', B = .forallE A' B'
    case neg =>
      -- (i) `B` is not syntactically a Π: every `f`-output is `⊥` (`Const.beyond`), so `m = ⊥`
      have hB' : ∀ X Y, B ≠ .forallE X Y := fun X Y h => hB ⟨X, Y, h⟩
      obtain ⟨hctor, hind, hpat⟩ := beyond_bounds h1 hT hB'
      have hfz : ¬ f.NonZero := by
        intro hnz
        obtain ⟨⟨x, y⟩, hm, hy⟩ := WShapeFun.NonZero.iff.1 hnz
        have := Const.beyond hctor hind hpat (hf x y hm) (by simp [hk])
        exact hy (WShape.LE.of_T (this.trans TShape.bot_eqv.2))
      rw [show WShape.lam' f = .bot by simp [WShape.lam', hfz]] at hle
      cases show m = .bot from TShape.le_bot.1 (le.trans (hle.trans TShape.bot_eqv.1))
      exact (LR _).bot hmem.isType
    -- (ii) `B = .forallE A' B'`
    obtain ⟨A', B', rfl⟩ := hB
    cases hmem.unfold with
    | bot h => exact (LR _).bot h
    | sort => exact absurd (le.trans hle) TShape.sort_not_le_lam'
    | forallE _ => exact absurd (le.trans hle) TShape.forallE_not_le_lam'
    | ctor => exact absurd (le.trans hle) TShape.ctor_not_le_lam'
    | indTy => exact absurd (le.trans hle) TShape.indTy_not_le_lam'
    | @lam j g a₁ a₂ hg =>
      by_cases hgz : g.NonZero
      case neg =>
        rw [show WShape.lam' g = .bot by simp [WShape.lam', hgz]]; exact (LR _).bot hmem.isType
      have hgf := le.trans hle
      rw [← WShape.lam_eq_lam' (hl := hgz)]
      -- the next domain `A'`, strongly typed in `below (rank c)` (type_below → telescope)
      have hT' : mkInst ls ci.type = (Ts ++ [A']).foldr .forallE B' := by
        rw [hT, List.foldr_append]; rfl
      obtain ⟨u₀, H₀⟩ := EnvStrongR.of_params.const ls h1
      rw [hT'] at H₀
      obtain ⟨u, HA₀⟩ := tel_last (IsDefEqStrong.telescope H₀)
      have HAb : IsDefEqStrong (Params.env.below Params.rank (Params.rank c)) (Ts.reverse ++ Γ₀)
          A' A' (.sort u) := by simpa using HA₀.weak_append (Γ₀ := Γ₀)
      have cons := LR.Adequate.cons (fun hm ha hma => WFIH _ hc HAb hm ha hma)
        (HAb.mono (Params.env.below_le ..))
      have hA₁ := hA.forallE_inv.1
      have eΓ : (Ts ++ [A']).reverse ++ Γ₀ = A' :: (Ts.reverse ++ Γ₀) := by simp
      -- one argument further: the IH at the `f`-pair above the typed input
      have key : ∀ {τ τ'}, LR.SubstWF Γ₀ τ τ' (Ts.reverse ++ Γ₀) ρ → ∀ {x x' : SExpr} {p : WShape j},
          p.HasType a₁ → Γ₀ ⊢ x ≡ x' : A'.subst τ → (LR Γ₀).DefEq x x' (A'.subst τ) p a₁ →
          (LR Γ₀).DefEq (((openSpine c ls Ts.length).subst τ).app x)
            (((openSpine c ls Ts.length).subst τ').app x') (B'.subst (τ.cons x)) (g.app p) (a₂.app p) := by
        intro τ τ' Wτ x x' p hp hx hv
        obtain ⟨x₀, y₀, hm₀, hx₀p, hgy⟩ := lam_pair hgf p
        have W' := cons hp hA₁ hx hv Wτ
        have H := ih x₀ y₀ hm₀ (Ts := Ts ++ [A']) (B := B') hT' (by simp [hk])
          (ρ := ρ.push p.T) (σ := τ.cons x) (σ' := τ'.cons x')
          (Valuation.LE.push.2 ⟨hρ, hx₀p⟩) (eΓ ▸ W') hgy (hA.forallE_inv'.2 p)
          ((WShape.HasTypeLam.iff.1 hg).2.2 p hp)
          (fun W₁ => LR.tyV_succ (Δ := Ts.reverse) hp hA₁ tyV (eΓ ▸ W₁))
        rwa [List.length_append, List.length_singleton, openSpine_succ, openSpine_succ] at H
      -- the Π row of the goal: components from `tyV` (the Π's type validity), `LamDefEq` from `key`
      have hty := tyV W
      simp only [LR, LRS, LRS.TyDefEq.forallE_iff, SExpr.subst] at hty
      obtain ⟨⟨u', e1⟩, ⟨v', e2⟩, tAA, P, rA⟩ := valTyPi2_forallE hty
      simp only [LR, LRS, LRS.DefEq.lam_forallE, SExpr.subst]
      refine ⟨_, _, u', v', rA, e1.hasType.1, (LR Γ₀).left_ty tAA, e2.hasType.1, P.left, ?_, ?_⟩
      · intro x x' p hp hx hv
        rw [inst_lift_cons]
        refine ⟨key W.left hp hx hv, ?_⟩
        have tB := P.2 hp hx.hasType.1 ((LR Γ₀).left hv)
        rw [inst_lift_cons, inst_lift_cons] at tB
        exact (LR Γ₀).conv ((LR Γ₀).symm_ty tB)
          (key W.symm.left hp (e1.defeqDF hx) ((LR Γ₀).conv tAA hv))
      · intro x p hp hx hv
        rw [inst_lift_cons]
        exact key W hp hx hv
  | @ctor mC rargs hcl hle =>
    obtain ⟨I, Fs, hFl, hI, hci, hF⟩ := ctor_data hcl h1
    have hT' : (Fs.map (mkInst ls)).foldr .forallE (.const I ls) = Ts.foldr .forallE B := by
      rw [← hT, hci, mkInst_foldr_forallE]; simp [mkInst, SLevel.instV_params h2]
    obtain ⟨rfl, rfl⟩ := foldr_forallE_inj (by simp [hFl, hk]) hT'
    have hclT : ∀ T ∈ Fs.map (mkInst ls), ClosedN T := by
      intro T hT; obtain ⟨F, hF', rfl⟩ := List.mem_map.1 hT
      obtain ⟨I', us, rfl, _⟩ := hF F hF'; trivial
    have hBσ : ∀ τ : Subst, (SExpr.const I ls).subst τ = .const I ls := fun _ => rfl
    rw [hBσ]
    cases hmem.unfold with
    | bot h => exact (LR _).bot h
    | sort => exact absurd (le.trans hle) TShape.sort_not_le_ctor'
    | forallE _ => exact absurd (le.trans hle) TShape.forallE_not_le_ctor'
    | @lam _ f _ _ _ =>
      by_cases hf : f.NonZero
      · rw [← WShape.lam_eq_lam' (hl := hf)] at le
        exact absurd (le.trans hle) TShape.lam_not_le_ctor'
      · rw [show WShape.lam' f = .bot by simp [WShape.lam', hf]]; exact (LR _).bot hmem.isType
    | indTy => exact absurd (le.trans hle) indTy_not_le_ctor'
    | @ctor j c' l wf =>
      obtain ⟨e, hl⟩ := ctor_le_ctor'_T (le.trans hle); subst c'

      simp only [LR, LRS]; rw [LRS.DefEq.ctor_indTy]
      have hlen : l.length = rargs.length := by
        simpa using Lean4Lean.List.Forall₂.length_eq hl
      have hL : List.Forall₂ (fun x y => x.T ≤ y.T) l.reverse rargs := by
        simpa using (Lean4Lean.List.Forall₂.reverse (l := l) (l' := rargs.reverse)).2 hl
      have FE := LR.fieldsEq_of_W (j := j) (Fs.map (mkInst ls)).reverse
        (fun T h => hclT T (List.mem_reverse.1 h)) W hρ hL (by simpa using hk)
      rw [List.reverse_reverse, List.reverse_reverse, List.length_reverse] at FE
      have hc0 : Γ₀ ⊢ SExpr.const c ls : (Fs.map (mkInst ls)).foldr .forallE (.const I ls) :=
        hT ▸ IsDefEq.const h1 h2
      have Hsp := spine_typed (show ClosedN (SExpr.const I ls) from trivial) FE hclT hc0
      have hty := tyV W
      rw [hBσ, hBσ] at hty
      simp only [LR, LRS, LRS.TyDefEq.indTy_m] at hty
      obtain ⟨_, _, _, ⟨⟨w, e⟩, _⟩, _⟩ := hty
      rw [openSpine_subst, openSpine_subst]
      exact ⟨I, ls, ci, _, _, _, hlen ▸ hcl, hI, h1, hT, ⟨⟨w, e.hasType.1⟩, .rfl⟩,
        ⟨Hsp.hasType.1, .rfl⟩, ⟨Hsp.hasType.2, .rfl⟩, FE⟩
  | indTy hcl hle =>
    obtain ⟨h0, u, hu⟩ := Params.indTy_closed hcl h1
    obtain rfl : Ts = [] := List.eq_nil_of_length_eq_zero (hk ▸ h0)
    simp only [List.foldr_nil] at hT
    rw [hu] at hT; subst hT
    simp only [openSpine, List.length_nil, List.range_zero, List.reverse_nil, List.map_nil,
      spine_nil, mkInst, SExpr.subst]
    cases hmem.unfold with
    | bot h => exact (LR _).bot h
    | sort => cases sort_not_le_indTy (le.trans hle)
    | forallE _ => obtain e | e := le_indTy_succ (le.trans hle) <;> cases congrArg (·.1) e
    | @lam _ f _ _ _ =>
      obtain e | e := le_indTy_succ (le.trans hle)
      · rw [e]; exact (LR _).bot hmem.isType
      · unfold WShape.lam' at e; split at e <;> cases congrArg (·.1) e
    | ctor => obtain e | e := le_indTy_succ (le.trans hle) <;> cases congrArg (·.1) e
    | indTy =>
      simp only [LR, LRS]
      rw [LRS.DefEq.sort_a (by intro e; cases congrArg (·.1) e), LRS.TyDefEq.indTy_m]
      have hty : Γ₀ ⊢ .const c ls : .sort (SLevel.instV ls u) := by
        have := IsDefEq.const (Γ := Γ₀) h1 h2; rwa [hu] at this
      exact ⟨⟨_, _, .sort⟩, c, ls, h0 ▸ hcl, ⟨⟨_, hty⟩, .rfl⟩, ⟨⟨_, hty⟩, .rfl⟩⟩
  | pat hP hMt hRHS =>
    obtain rfl := LE_Interp.Matches.head hMt
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 (Params.pat_gen hP)
    exact LR.pat_leaf_1a WFIH hc h1 h2 LIH hR hP hMt hRHS (Params.pat_check hP) g hg
      (Params.pat_typed hP hg h1) (Params.pat_defeq hP hg h1) hT hk hρ W le hA hmem tyV

/-- `LR.const_local` (PLAN D4): induction on `hM` through the `R`-closure. Its only recursive
calls are the local IH on the `Const` premise's sub-derivations (`ih7`) and the WF IH at
`rank c ≤ rank c₀ < k` (type validity, `tyV`); the rest is `LR.const_spine` at `rargs = []`. -/
theorem LR.const_local {Γ₀ : List SExpr} {k : Nat} {c₀ : Name}
    (WFIH : LR.WFIH Params.rank Γ₀ k) (hΓ₀ : ⊢ Γ₀) (hc₀ : Params.rank c₀ < k) :
    ∀ {ρ mT M} (_hM : LE_Interp ρ mT M) {c ls ci}, M = .const c ls → Params.rank c ≤ Params.rank c₀ →
      Params.env.constants c = some ci → ls.length = ci.uvars → LR.ConstGoal Γ₀ ρ mT c ls ci := by
  intro ρ mT M hM
  induction hM with
  | bot => intro _ _ _ _ _ _ _; exact .inl ⟨_, rfl⟩
  | @const _ c' ci' mT₀ m' ρ a ls' R h1 h2 h3 h4 h5 h6 h7 _ ih7 =>
    intro c ls ci eM hrk hci hlen
    injection eM with e1 e2; subst c' ls'
    have e3 := Option.some.inj (h1.symm.trans hci); subst ci'
    have hk : Params.rank c < k := Nat.lt_of_le_of_lt hrk hc₀
    -- (i) the local IH: same-rank bare-constant leaves of `R`, from `ih7` (strict sub-derivations)
    have LIH : LR.LocalIH Params.rank Γ₀ ρ c R := fun me e hR c'' ls'' ci'' he hr h1'' h2'' =>
      ih7 me e hR he (hr ▸ hrk) h1'' h2''
    -- (ii) type validity: the WF IH at `rank c < k` on `EnvStrongR.const`
    have hcl : (mkInst ls ci.type).ClosedN := (Params.henv.closedC hci).mkInstS
    have tyV : ∀ {n} {a₁ : WShape n}, LE_Interp .nil a₁.T (mkInst ls ci.type) →
        a₁.HasType .type → (LR Γ₀).TyDefEq (mkInst ls ci.type) (mkInst ls ci.type) a₁ := by
      intro n a₁ hA ha
      obtain ⟨u, Hty₀⟩ := EnvStrongR.of_params.const ls hci
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
    have H := LR.const_spine WFIH hk hci hlen LIH h7 h6 (Ts := []) (B := mkInst ls ci.type) rfl rfl
      Valuation.LE.rfl (LR.SubstWF.id hΓ₀) (hle.trans (TShape.lift_eqv hK1).1)
      ((LE_Interp.closed_iff hcl).1 hA₁) hmem₁ fun _ => by
        rw [hcl.subst_eq .zero, hcl.subst_eq .zero]
        exact tyV ((LE_Interp.closed_iff hcl).1 hA₁) hmem₁.isType
    simpa only [openSpine, List.length_nil, List.range_zero, List.reverse_nil, List.map_nil,
      spine_nil, subst_id] using H
  | _ => intro _ _ _ eM; cases eM

/-- The `const` case of `LR.adequacy_rank` from `LR.const_local` at `c₀ := c` (R8's wiring):
a `(env.below rank k)` constant node, at any `ρ`. -/
theorem LR.const_case {Γ₀ Γ : List SExpr} {k : Nat} (WFIH : LR.WFIH Params.rank Γ₀ k)
    {c : Name} {ci : VConstant} {ls : List SLevel}
    (h1 : (Params.env.below Params.rank k).constants c = some ci) (h2 : ls.length = ci.uvars)
    {ρ : Valuation} {n : Nat} {m a : WShape n} (hM : LE_Interp ρ m.T (.const c ls))
    (hA : LE_Interp ρ a.T (mkInst ls ci.type)) (hmem : m.HasType a) :
    LR.Adequate Γ₀ Γ ρ (.const c ls) (.const c ls) (mkInst ls ci.type) m a := by
  have hrk := VEnv.below_constants_lt h1
  have h1' := (Params.env.below_le ..).1 h1
  refine .refl fun σ _ W => ?_
  rw [(Params.henv.closedC h1').mkInstS.subst_eq .zero]
  obtain ⟨_, he⟩ | ⟨_, m', _, hle, _, _, H⟩ :=
    LR.const_local WFIH W.wf₀ hrk hM rfl (Nat.le_refl _) h1' h2
  · cases show m = .bot from TShape.le_bot.1 (he ▸ TShape.bot_le')
    exact (LR _).bot hmem.isType
  · exact H m a hle hA hmem

/-! ## The `extra` case for λ-wrapped rules (PLAN D5, R6; from E5)

A rule is the λ-closure over a telescope `Δ` of an open typed equation (`Params.extra_pat`).
`LR.lamRule` goes through one `LamDefEq` layer per binder, each a typed beta step from the open
equation (`typed_beta_rhs` on `lamDF_foldr`, substituted), then `WHRed.extra` on the open
instance. -/

/-- The typed reduction of a one-binder λ-rule instance, from the rule's open typed equation:
no λ-inversion and no `⊢ Γ` needed (docs/const-case/plan/historical/LamRuleTyped.lean). -/
theorem typed_beta_rule {Γ : List SExpr} {A L R T a : SExpr} {u}
    (hA : Γ ⊢ A : .sort u) (hLR : A::Γ ⊢ L ≡ R : T) (ha : Γ ⊢ a : A) :
    Γ ⊢ .app (.lam A L) a ≡ R.inst a : T.inst a :=
  .trans (.appDF (.lamDF hA hLR) ha) (.beta hLR.hasType.2 ha)

/-- The `N`-side step `(λA.R) a ≡ R[a]` from the same data. -/
theorem typed_beta_rhs {Γ : List SExpr} {A L R T a : SExpr}
    (hLR : A::Γ ⊢ L ≡ R : T) (ha : Γ ⊢ a : A) :
    Γ ⊢ .app (.lam A R) a ≡ R.inst a : T.inst a := .beta hLR.hasType.2 ha

/-- Well-formedness of a context gives that of each suffix. -/
theorem ctxWF_of_append : ∀ (Δ : List SExpr) {Γ : List SExpr}, ⊢ Δ ++ Γ → ⊢ Γ
  | [], _, h => h
  | _ :: Δ, _, h => ctxWF_of_append Δ h.1

/-- The λ-closure of an open typed equation over a well-formed telescope (`lamDF` per binder). -/
theorem lamDF_foldr {T : SExpr} : ∀ (Δ : List SExpr) {Ξ : List SExpr} {L R : SExpr},
    ⊢ Δ.reverse ++ Ξ → Δ.reverse ++ Ξ ⊢ L ≡ R : T →
    Ξ ⊢ Δ.foldr .lam L ≡ Δ.foldr .lam R : Δ.foldr .forallE T
  | [], _, _, _, _, h => h
  | A :: Δ, Ξ, L, R, hwf, h => by
    have hctx : (A :: Δ).reverse ++ Ξ = Δ.reverse ++ A :: Ξ := by simp
    rw [hctx] at hwf h
    have ⟨_, _, hA⟩ := ctxWF_of_append Δ.reverse hwf
    exact .lamDF hA (lamDF_foldr Δ hwf h)

/-- At element shapes, type validity of a `lam` with itself transfers to any right side
(every non-trivial row reduces the `lam` to a sort, a Π or a constant). -/
theorem tyDefEq_lam_l {IH : LogRel Γ n} {X F N : SExpr} {m : WShape (n+1)}
    (h : LRS.TyDefEq IH (.lam X F) (.lam X F) m) : LRS.TyDefEq IH (.lam X F) N m := by
  cases m using WShape.casesOn' with
  | bot => exact LRS.TyDefEq.bot
  | lam f hf => exact (LRS.TyDefEq.lam_m (f := f) (hf := hf)).2 trivial
  | ctor c l hc => exact (LRS.TyDefEq.ctor_m (c := c) (l := l) (h := hc)).2 trivial
  | sort r => obtain ⟨_, h, _⟩ := h; cases WHNF.lam.whRedS h.2
  | forallE b f => obtain ⟨_, _, _, _, _, _, h, _⟩ := h; cases WHNF.lam.whRedS h.2
  | indTy => obtain ⟨_, _, _, h, _⟩ := h; cases WHNF.lam.whRedS h.2

/-- Level 0: a `lam` related to itself is related to anything (only `⊥`/`sort` rows exist). -/
theorem lr0_lam_of {X F N Ty : SExpr} {m a : WShape 0}
    (h : LR0.DefEq Γ (.lam X F) (.lam X F) Ty m a) : LR0.DefEq Γ (.lam X F) N Ty m a := by
  obtain ⟨a, ha⟩ := a; obtain ⟨m, hm⟩ := m
  cases a <;> cases m <;> simp only [LR0.DefEq, LR0.TyDefEq] at h ⊢
  obtain ⟨_, _, h, _⟩ := h; cases WHNF.lam.whRedS h.2

/-- Level `n+1`, ambient a Π in whnf: the `(lam, forallE)` row is `LamDefEq`, whose
cross component is supplied by `key`; every other row is trivial or refuted by `hl`. -/
theorem lrs_lam_of {IH : LogRel Γ n} {X F G B : SExpr} {m a : WShape (n+1)}
    (key : ∀ {x} {p : WShape n} {mf a₂ : WShapeFun n}, Γ ⊢ x : X →
      IH.DefEq ((SExpr.lam X F).app x) ((SExpr.lam X F).app x) (B.inst x) (mf.app p) (a₂.app p) →
      IH.DefEq ((SExpr.lam X G).app x) ((SExpr.lam X G).app x) (B.inst x) (mf.app p) (a₂.app p) →
      IH.DefEq ((SExpr.lam X F).app x) ((SExpr.lam X G).app x) (B.inst x) (mf.app p) (a₂.app p))
    (hl : LRS.DefEq IH (.lam X F) (.lam X F) (.forallE X B) m a)
    (hr : LRS.DefEq IH (.lam X G) (.lam X G) (.forallE X B) m a) :
    LRS.DefEq IH (.lam X F) (.lam X G) (.forallE X B) m a := by
  cases a using WShape.casesOn' with
  | bot => trivial
  | sort r =>
    by_cases hm : m = .bot
    · subst hm; trivial
    rw [LRS.DefEq.sort_a hm] at hl ⊢
    exact ⟨hl.1, tyDefEq_lam_l hl.2⟩
  | forallE a₁ a₂ =>
    cases m using WShape.casesOn' with
    | bot => trivial
    | lam f hf =>
      rw [LRS.DefEq.lam_forallE] at hl hr ⊢
      obtain ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩ := hl
      obtain ⟨_, _, _, _, rA', _, _, _, _, hP'⟩ := hr
      cases WHNF.forallE.whRedS rA.2
      cases WHNF.forallE.whRedS rA'.2
      exact ⟨_, _, u, v, rA, hA1, hA2, hA₂, hE,
        fun _ _ _ hp hab hv => ⟨(hP.1 hp hab hv).1, (hP'.1 hp hab hv).2⟩,
        fun _ _ hp hx hv => key hx (hP.2 hp hx hv) (hP'.2 hp hx hv)⟩
    | sort | forallE | ctor | indTy => exact (hl : False).elim
  | indTy =>
    cases m using WShape.casesOn' with
    | bot => trivial
    | ctor c l hc =>
      rw [LRS.DefEq.ctor_indTy] at hl
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hTy, _⟩ := hl
      cases WHNF.forallE.whRedS hTy.2
    | sort | forallE | lam | indTy => exact (hl : False).elim
  | lam | ctor => exact (hl : False).elim

/-- The `extra` case for a λ-rule, generalized over the binders already instantiated (`τ`, a
substitution from `Ξ` into `Γ₀`) and over the level: given the open equation `L ≡ R : T` and the
open step `L ⤳ R` in `Δ.reverse ++ Ξ`, the instantiated closures `(λΔ.L)[τ]`, `(λΔ.R)[τ]` are
related as soon as each is related to itself. One `LamDefEq` layer per binder, each typed beta
step from the open equation (`typed_beta_rhs` on `lamDF_foldr`, substituted); at `Δ = []`,
`WHRed.extra` on the open instance (substituted), typed by the substituted open equation. -/
theorem LR.lamRule {Γ₀ : List SExpr} (hΓ₀ : ⊢ Γ₀) {T : SExpr} :
    ∀ (Δ : List SExpr) {Ξ : List SExpr} {τ : Subst} {L R : SExpr},
    ⊢ Δ.reverse ++ Ξ → Δ.reverse ++ Ξ ⊢ L ≡ R : T → Δ.reverse ++ Ξ ⊢ L ⤳ R →
    Ctx.SubstEq Γ₀ τ τ Ξ → ∀ {n} {m a : WShape n},
    (LR Γ₀).DefEq ((Δ.foldr .lam L).subst τ) ((Δ.foldr .lam L).subst τ)
      ((Δ.foldr .forallE T).subst τ) m a →
    (LR Γ₀).DefEq ((Δ.foldr .lam R).subst τ) ((Δ.foldr .lam R).subst τ)
      ((Δ.foldr .forallE T).subst τ) m a →
    (LR Γ₀).DefEq ((Δ.foldr .lam L).subst τ) ((Δ.foldr .lam R).subst τ)
      ((Δ.foldr .forallE T).subst τ) m a
  | [], Ξ, τ, L, R, _, hLR, hred, W, n, m, a, hl, _ => by
    have tE : Γ₀ ⊢ L.subst τ ≡ R.subst τ : T.subst τ := IsDefEq.subst hΓ₀ W hLR
    have rE : Γ₀ ⊢ L.subst τ ⤳ R.subst τ := WHRed.subst (fun h => IsDefEq.subst hΓ₀ W h) hred
    exact ((LR Γ₀).whr ⟨tE.hasType.1, .rfl⟩ ⟨tE, .tail .rfl rE⟩).1 hl
  | A :: Δ, Ξ, τ, L, R, hwf, hLR, hred, W, n, m, a, hl, hr => by
    have hctx : (A :: Δ).reverse ++ Ξ = Δ.reverse ++ A :: Ξ := by simp
    rw [hctx] at hwf hLR hred
    have ⟨_, _, hA⟩ := ctxWF_of_append Δ.reverse hwf
    have hAτ := IsDefEq.subst hΓ₀ W hA
    have hFG := IsDefEq.subst (Ctx.WF.cons hΓ₀ hAτ) (W.lift hA) (lamDF_foldr Δ hwf hLR)
    -- the typed beta step of one layer, from the (substituted) λ-closure of the open equation
    have step {Y x : SExpr}
        (hY : A.subst τ :: Γ₀ ⊢ Y.subst τ.lift : (Δ.foldr .forallE T).subst τ.lift)
        (hx : Γ₀ ⊢ x : A.subst τ) :
        TWHRedS Γ₀ (.app (.lam (A.subst τ) (Y.subst τ.lift)) x) (Y.subst (τ.cons x))
          (((Δ.foldr .forallE T).subst τ.lift).inst x) := by
      have h := typed_beta_rhs hY hx
      rw [inst_lift_cons (e := Y)] at h
      exact ⟨h, inst_lift_cons (x := x) ▸ .tail .rfl .beta⟩
    cases n with
    | zero => exact lr0_lam_of hl
    | succ n =>
      refine lrs_lam_of (fun {x _ _ _} hx dl dr => ?_) hl hr
      have W' : Ctx.SubstEq Γ₀ (τ.cons x) (τ.cons x) (A :: Ξ) := .cons W hA hx
      have tl := step hFG.hasType.1 hx; have tr := step hFG.hasType.2 hx
      refine ((LR Γ₀).whr tl tr).2 ?_
      rw [inst_lift_cons]
      refine lamRule hΓ₀ Δ hwf hLR hred W' ?_ ?_
      · have := ((LR Γ₀).whr tl tl).1 dl; rwa [inst_lift_cons] at this
      · have := ((LR Γ₀).whr tr tr).1 dr; rwa [inst_lift_cons] at this

/-! ## Adequacy, by well-founded induction on the rank bound (PLAN D4)

`LR.adequacy_rank` is adequacy for derivations in the prefix `env.below rank k`, assuming it at
every smaller bound (`LR.WFIH`); only its `const` case uses the assumption, through
`LR.const_case`. `LR.adequacy_rank_wf` closes the loop by strong induction on `k`, and
`LR.adequacy` follows through `IsDefEqStrong.exists_below`. -/

/-- Adequacy at rank bound `k`, given it below `k`. -/
theorem LR.adequacy_rank {k : Nat} (WFIH : LR.WFIH Params.rank Γ₀ k)
    (H : IsDefEqStrong (Params.env.below Params.rank k) Γ M N A)
    (hM : LE_Interp ρ m.T M) (hA : LE_Interp ρ a.T A) (hmem : m.HasType a) :
    Adequate (n := n) Γ₀ Γ ρ M N A m a := by
  have hE := VEnv.below_le Params.env Params.rank k
  induction H generalizing ρ n m a with
  | @bvar Γ i A _ h h2 ih =>
    refine .refl fun _ _ W => ?_; clear h2 ih
    have hle := LE_Interp.bvar_iff.1 hM; clear hM
    induction W generalizing i A with
    | id =>
      cases show m = .bot from TShape.le_bot.1 (hle.trans TShape.bot_le)
      exact (LR _).bot hmem.isType
    | cons W' _ _ _ _ h0 ih =>
      cases h with
      | zero => exact lift_subst ▸ (h0.2 a hA).2 (.bvar hle) hmem
      | succ h' => exact lift_subst ▸ ih h' (LE_Interp.weak_iff.1 hA) hle
  | symm H ih => exact .fits fun W => (ih ((LE_Interp.soundSE hE H W).1.2 hM) hA hmem).symm
  | trans _ H1 H2 ihA ih1 ih2 =>
    exact .fits fun W => (ih1 hM hA hmem).trans (ih2 ((LE_Interp.soundSE hE H1 W).1.1 hM) hA hmem)
  | trans' H1 H2 ih1 ih2 =>
    by_cases hm : m ≤ .bot; · exact WShape.le_bot.1 hm ▸ .bot hmem.isType
    rename_i A B u C v
    refine .fits fun W => ?_
    refine (ih1 hM hA hmem).trans' (v := v) (r := v ≠ .zero) ?_
    refine have ihs1 := LE_Interp.soundSE hE H1 W; have hM₂ := ihs1.1.1 hM; ?_
    have ihs2 := LE_Interp.soundSE hE H2 W (m := m.T)
    have ⟨a₂, s₂, b1, b2, b3, b4⟩ := ihs2.2 hM₂
    replace b4 := TShape.HasType.sort.mono_r b3.le_sort b4
    have := TShape.HasType.mono_r hA.le_sort .sort hmem.T
    refine ih2 (ihs1.1.1 hM) (.sort TShape.sort_eqv.1) ?_
    exact WShape.HasType.T_iff.1 <| .mono_r TShape.sort_eqv.2 .sort_T <| this.retype b4 b1
  | @sort _ l =>
    suffices (LR Γ₀).DefEq (.sort l) (.sort l) (.sort l.succ) m a from
      ⟨fun _ _ _ => ⟨this, this⟩, fun _ _ => this⟩
    cases hmem.unfold with
    | bot hm => exact (LR _).bot hm
    | sort => exact (LR _).sort_iff.2 ⟨⟨_, _, .sort⟩, _, .sort, .sort⟩
    | _ =>
      obtain h | h := WShape.le_sort.1 hM.le_sort'
      · dsimp only at h; rw [h]; exact (LR _).bot hmem.isType
      · simp [WShape.ext_iff, WShape.forallE, WShape.sort, Shape.sort,
          WShape.lam', WShape.lam, WShape.bot, WShape.ctor, WShape.indTy,
          Shape.bot] at h <;> first | split at h <;> simp_all only [reduceCtorEq] | simp_all
  | const h1 h2 => exact LR.const_case WFIH h1 h2 hM hA hmem
  | @appDF Γ A u B v F F' X X' _ _ Hf Ha HBa _ _ ihf iha ihBa =>
    cases hM with | bot => exact .bot hmem.isType | @app _ nf_app f _ _ _ x hif hia le_m
    suffices ∀ {F F' X X' σ σ'}, SubstWF Γ₀ σ σ' Γ ρ →
        Γ ⊢ F ≡ F' : A.forallE B → Γ ⊢ X ≡ X' : A → Γ ⊢ B.inst X ≡ B.inst X' : .sort v →
        LE_Interp ρ f.T F → LE_Interp ρ x.T X → LE_Interp ρ a.T (B.inst X) →
        (∀ {n'} {mf af : WShape n'}, LE_Interp ρ mf.T F → LE_Interp ρ af.T (.forallE A B) →
          mf.HasType af → Adequate Γ₀ Γ ρ F F' (.forallE A B) mf af) →
        (∀ {n'} {ma aa : WShape n'}, LE_Interp ρ ma.T X → LE_Interp ρ aa.T A →
          ma.HasType aa → Adequate Γ₀ Γ ρ X X' A ma aa) →
        (∀ {n'} {mb av : WShape n'}, LE_Interp ρ mb.T (B.inst X) → LE_Interp ρ av.T (.sort v) →
          mb.HasType av → Adequate Γ₀ Γ ρ (B.inst X) (B.inst X') (.sort v) mb av) →
        (LR Γ₀).DefEq (.subst (.app F X) σ) (.subst (.app F' X') σ')
          (.subst (B.inst X) σ) m a by
      refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W =>
        this W (Hf.defeqE hE) (Ha.defeqE hE) (HBa.defeqE hE) hif hia hA ihf iha ihBa⟩
      · refine this W (Hf.defeqE hE).hasType.1 (Ha.defeqE hE).hasType.1 (HBa.defeqE hE).hasType.1
          hif hia hA ?_ ?_ ?_
        · exact fun hf hPi hmf => (ihf hf hPi hmf).left
        · exact fun ha hA hma => (iha ha hA hma).left
        · exact fun hB hv hmb => (ihBa hB hv hmb).left
      · refine (LR _).conv ((LR _).symm_ty ?_) <| this W
          (Hf.defeqE hE).hasType.2 (Ha.defeqE hE).hasType.2 (HBa.defeqE hE).hasType.2
          ((LE_Interp.soundSE hE Hf W.fits).1.1 hif) ((LE_Interp.soundSE hE Ha W.fits).1.1 hia)
          ((LE_Interp.soundSE hE HBa W.fits).1.1 hA)
          (fun hf hPi hmf => ?_) (fun ha hA hma => ?_) (fun hB hv hmb => ?_)
        · have ⟨_, _, _, le, le', iB, iv, hmb⟩ := (LE_Interp.soundSE hE HBa W.fits).2 hA |>.out
          exact toValTy le le' hmem.isType iv hmb ((ihBa iB iv hmb).2 W.left)
        · exact (ihf ((LE_Interp.soundSE hE Hf W.left.fits).1.2 hf) hPi hmf).symm.left
        · exact (iha ((LE_Interp.soundSE hE Ha W.left.fits).1.2 ha) hA hma).symm.left
        · exact (ihBa ((LE_Interp.soundSE hE HBa W.left.fits).1.2 hB) hv hmb).symm.left
    intro F F' X X' σ σ' W hF hX hBa hif hia hA ihf iha ihBa
    have ⟨_, mf, _, le_nf, le_mf, hf', hPi, hmf⟩ := (LE_Interp.sound W.wf hF W.left.fits).2 hif |>.out
    have Af := ihf hf' hPi hmf
    by_cases hm0 : mf = .bot
    · simp only [hm0] at le_mf hmf
      refine (?_ : m = .bot) ▸ (LR _).bot hmem.isType
      cases show f = .bot from TShape.le_bot.1 (le_mf.trans TShape.bot_le')
      exact TShape.le_bot.1 ((WShape.bot_app ▸ le_m).trans TShape.bot_eqv.1)
    cases hPi with | bot => cases hm0 hmf.bot_r | forallE haA hbA hd hiB le
    cases hmf.unfold with | bot => cases hm0 rfl | lam hg => ?_ | _ =>
      refine have le₂ := Nat.succ_le_succ (Nat.le_max_right ..)
        have := (TShape.LE.def (Nat.le_succ_of_le (Nat.le_max_left ..)) le₂).1 le; ?_
      simp only [WShape.lift_sort, WShape.LE.def, WShape.lift_val le₂] at this; cases this
    rename_i n₁ b₁' b₂' f' n₂ b₁ b₂ f
    simp at le_nf
    let k := max n (max n₁ n₂); have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
    have le_nf_k : nf_app ≤ k := Nat.le_trans le_nf hk.2.2
    have hA' := hA.lift hk.1
    have ⟨_, le_x', hx'_a₁, hgx2⟩ := WShape.HasDom.iff.1 hg.2.1 (x.lift _)
    have hia' := (hia.lift le_nf).mono le_x'.T
    have hax' := LE_Interp.forallE' haA hbA hd hiB |>.mono le |>.forallE_inv.2 hia'
    have hJ := TShape.Join.mk (hA.compat hax')
    have ⟨hJ1, hJ2⟩ := (hJ _).1 .rfl
    have hk' := Nat.max_le.2 ⟨hk.1, hk.2.2⟩
    have hJ1' := (TShape.LE.def hk.1 hk').1 hJ1
    have hJ2' := (TShape.LE.def hk.2.2 hk').1 hJ2
    have hgx' := (WShape.HasTypeLam.iff.1 hg).2.2 _ hx'_a₁
    have hJ_t := TShape.HasType.sort_r.2 hmem.isType
      |>.join' hJ <| TShape.HasType.sort_r.2 hgx'.isType
    have hmem_k := (WShape.HasType.lift hk.1).2 hmem
    rw [subst_inst]
    have hJ_t' := TShape.HasType.sort_r.1 <|
      hJ_t.mono_l (TShape.lift_eqv hk').2 (TShape.lift_eqv hk').1
    refine (LR.DefEq.lift hk.1 hmem).1 <| (LR Γ₀).mono_r_2 hJ1' hmem_k hJ_t' ?_
    have hgx'' := (WShape.HasType.lift hk.2.2).2 hgx'
    refine (LR Γ₀).mono_l ?_ (.mono_r hJ1' hJ_t' hmem_k) (.mono_r hJ2' hJ_t' hgx'') ?_
    · exact (TShape.LE.def hk.1 hk.2.2).1 <| le_m.trans <|
        (TShape.app_mono le_mf (TShape.lift_eqv le_nf).2).trans (WShape.lam'_app ▸ hgx2.T)
    refine (LR Γ₀).mono_r_1 hJ2' hgx'' (.mono_r hJ2' hJ_t' hgx'') ?_ ?_
    · have ⟨_, _, _, le_j, le_j', hBj, hSj, hmj⟩ :=
        (LE_Interp.sound W.wf hBa W.left.fits).2 (hA.join hJ hax') |>.out
      exact (LR Γ₀).left_ty <| (TyDefEq.lift hk' (TShape.HasType.sort_r.1 hJ_t)).2 <|
        subst_inst ▸ toValTy le_j le_j' (TShape.HasType.sort_r.1 hJ_t) hSj hmj
          ((ihBa hBj hSj hmj).2 W.left)
    · have hAf := (LR _).trans (Af.2 W.left) (Af.1 W).2
      dsimp only [LR, LRS] at hAf
      unfold WShape.lam' at hAf; split at hAf
      · rw [LRS.DefEq.lam_forallE] at hAf
        obtain ⟨_, _, _, _, red, _, _, _, _, valPi⟩ := hAf
        cases WHNF.forallE.whRedS red.2
        have le' := (TShape.LE.def (Nat.succ_le_succ hk.2.2) (Nat.succ_le_succ hk.2.1)).1 le
        simp only [WShape.T, WShape.lift_forallE hk.2.2, WShape.lift_forallE hk.2.1,
          WShape.forallE_le_forallE] at le'
        have Aa := iha hia' (haA.mono ((TShape.LE.def hk.2.2 hk.2.1).2 le'.1)) hx'_a₁
        have := (LR _).trans (Aa.2 W.left) (Aa.1 W).2
        exact (DefEq.lift hk.2.2 hgx').2 <| (LR _).trans
          (valPi.2 hx'_a₁ (hX.subst W.wf₀ W.toSubstEq).hasType.1 <| (LR _).left this)
          (valPi.1 hx'_a₁ (hX.subst W.wf₀ W.toSubstEq) this).2
      · refine (hm0 ?_).elim; unfold WShape.lam'; simp_all
  | @lamDF Γ A A' u B v body body' HA HB HBody HBody' ihA ihB ihBody =>
    suffices ∀ {X Y X' Y' σ σ'},
        LE_Interp ρ m.T (.lam X Y) → SubstWF Γ₀ σ σ' Γ ρ →
        -- D6: typings of both lambdas, for the typed beta steps below
        Γ ⊢ A ≡ X : .sort u → X::Γ ⊢ Y : B → Γ ⊢ A ≡ X' : .sort u → X'::Γ ⊢ Y' : B →
        (∀ {k np} {p : WShape np} {mb ab : WShape k},
          (ρ.push p.T).Fits Γ₀ (A :: Γ) →
          LE_Interp (ρ.push p.T) mb.T Y → LE_Interp (ρ.push p.T) ab.T B → mb.HasType ab →
          Adequate Γ₀ (A :: Γ) (ρ.push p.T) Y Y' B mb ab) →
        (LR Γ₀).DefEq (.subst (.lam X Y) σ) (.subst (.lam X' Y') σ')
          (.subst (.forallE A B) σ) m a by
      have tA := (HA.defeqE hE).hasType.1; have tb := (HBody.defeqE hE).hasType.1
      have tb' := (HBody'.defeqE hE).hasType.2
      refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => this hM W tA tb (HA.defeqE hE) tb' fun _ => ihBody⟩
      · exact this hM W tA tb tA tb fun _ hMb hBb hmb => (ihBody hMb hBb hmb).left
      · refine this ?_ W (HA.defeqE hE) tb' (HA.defeqE hE) tb' fun W hMb' hBb hmb => ?_
        · exact (LE_Interp.soundSE hE (.lamDF HA HB HBody HBody') W.fits).1.1 hM
        · exact (ihBody ((LE_Interp.soundSE hE HBody W).1.2 hMb') hBb hmb).symm.left
    intro X Y X' Y' σ σ' hTerm W HX HY HX' HY' IH
    suffices ∀ n' b (f : WShapeFun _), n = n' + 1 → a ≍ (.forallE b f : WShape (n'+1)) →
        (LR Γ₀).DefEq (.subst (.lam X Y) σ) (.subst (.lam X' Y') σ')
          (.subst (.forallE A B) σ) m a by
      cases hmem.unfold with
      | bot hm =>
        cases hm.unfold with
        | bot | sort => cases n <;> trivial | indTy => trivial
        | forallE => exact this _ _ _ rfl .rfl
      | sort => cases n <;> let .lam _ _ _ h := hTerm <;> cases TShape.sort_not_le_lam' h
      | forallE => let .lam _ _ _ h := hTerm <;> cases TShape.forallE_not_le_lam' h
      | lam => exact this _ _ _ rfl .rfl
      | ctor => let .lam _ _ _ h := hTerm; cases TShape.ctor_not_le_lam' h
      | indTy => let .lam _ _ _ h := hTerm; cases TShape.indTy_not_le_lam' h
    rintro k a₁ a₂ rfl ⟨⟩
    have ⟨_, aty, _⟩ := WShape.HasType.forallE_l.1 hmem.isType
    have hTypA : Γ₀ ⊢ A.subst σ : .sort u :=
      (HA.defeqE hE).hasType.1.subst W.wf₀ W.left.toSubstEq
    have hTypB : A.subst σ :: Γ₀ ⊢ B.subst σ.lift : .sort v :=
      (HB.defeqE hE).subst (Ctx.WF.cons W.wf₀ hTypA) (W.left.toSubstEq.lift (HA.defeqE hE).hasType.1)
    have hA1 := hA.forallE_inv.1
    have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ :=
      (LE_Interp.soundSE hE HA W.left.fits).2 hA1 |>.out
    have cons := Adequate.cons ihA (HA.mono hE)
    obtain ⟨g, hg, htm⟩ := WShape.HasType.forallE_inv hmem
    unfold WShape.lam' at hg; split at hg <;> [skip; (subst hg; exact (LR _).bot hmem.isType)]
    rename_i hlam; subst hg
    simp only [LR, LRS, LRS.DefEq.lam_forallE]
    have aty := WShape.HasTypePi.iff.1 aty
    refine ⟨A.subst σ, B.subst σ.lift, u, v, ⟨⟨_, .forallEDF hTypA hTypB⟩, .rfl⟩, hTypA, ?_, hTypB,
      ?_, ?_⟩
    · exact (LR Γ₀).left_ty <| toValTy le_n le_a aty.1.isType hSort hmem'
        ((ihA hA' hSort hmem').2 W.left)
    · simp [LRS.PiDefEq, inst_lift_cons]
      refine have := ?_; ⟨this, fun _ _ hp ha hv => this hp ha hv⟩
      intro x x' p hp ha hv
      have W' := cons hp hA1 ha hv W.left
      have ⟨n', ab, _, le, le', iB, iv, hmb⟩ :=
        (LE_Interp.soundSE hE HB W'.fits).2 (hA.forallE_inv'.2 p) |>.out
      exact toValTy le le' (aty.2 _ hp).toType iv hmb ((ihB iB iv hmb).1 W').1
    have beta {X Y t : SExpr} {σ} : Γ₀ ⊢ .app (.lam (X.subst σ) (Y.subst σ.lift)) t ⤳*
        Y.subst (σ.cons t) := inst_lift_cons (x := t) ▸ .tail .rfl .beta
    -- D6: typed beta steps, from the body typings `HY`/`HY'` (substituted) and `IsDefEq.beta`
    have bodyTy {X Y : SExpr} {τ τ' : SExpr.Subst} (Wτ : SubstWF Γ₀ τ τ' Γ ρ)
        (HX : Γ ⊢ A ≡ X : .sort u) (HY : X::Γ ⊢ Y : B) :
        X.subst τ :: Γ₀ ⊢ Y.subst τ.lift : B.subst τ.lift :=
      have hX : Γ₀ ⊢ X.subst τ : .sort u := (HX.subst Wτ.wf₀ Wτ.left.toSubstEq).hasType.2
      HY.subst (Ctx.WF.cons Wτ.wf₀ hX) (Wτ.left.toSubstEq.lift HX.hasType.2)
    have tbeta {X Y x T : SExpr} {τ : SExpr.Subst}
        (hY : X.subst τ :: Γ₀ ⊢ Y.subst τ.lift : B.subst τ.lift) (hx : Γ₀ ⊢ x : X.subst τ)
        (hT : Γ₀ ⊢ B.subst (τ.cons x) ≡ T : .sort v) :
        TWHRedS Γ₀ (.app (.lam (X.subst τ) (Y.subst τ.lift)) x) (Y.subst (τ.cons x)) T := by
      have h := IsDefEq.beta hY hx; rw [inst_lift_cons, inst_lift_cons] at h
      exact ⟨hT.defeqDF h, beta⟩
    have hBsub {τ τ'} {ρ'} (W' : SubstWF Γ₀ τ τ' (A :: Γ) ρ') :
        Γ₀ ⊢ B.subst τ ≡ B.subst τ' : .sort v := (HB.defeqE hE).subst W.wf₀ W'.toSubstEq
    have HXσ : Γ₀ ⊢ A.subst σ ≡ X.subst σ : .sort u := HX.subst W.wf₀ W.left.toSubstEq
    have HX'σ : Γ₀ ⊢ A.subst σ ≡ X'.subst σ' : .sort u := HX'.subst W.wf₀ W.toSubstEq
    refine ⟨fun x x' p hp ha hv => ?_, fun x p hp ha hv => ?_⟩
    all_goals
      rw [inst_lift_cons]
      have hBb_sd := hA.forallE_inv'.2 p
      replace IH W := IH W (hTerm.lam_inv' p) hBb_sd ((WShape.HasTypeLam.iff.1 htm).2.2 p hp)
    · have W' := cons hp hA1 ha hv W.left
      constructor
      · have hB' := hBsub W'
        exact ((LR Γ₀).whr (tbeta (bodyTy W HX HY) (HXσ.defeqDF ha.hasType.1) hB'.hasType.1)
          (tbeta (bodyTy W HX HY) (HXσ.defeqDF ha.hasType.2) hB'.symm)).2 <| ((IH W'.fits).1 W').1
      · have vtAA' := toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
        have ha' : Γ₀ ⊢ x ≡ x' : A.subst σ' := ((HA.defeqE hE).hasType.1.subst W.wf₀ W.toSubstEq).defeqDF ha
        have hv' := (LR Γ₀).conv vtAA' hv
        have ⟨n', _, _, le, le', iB, iv, hmb⟩ := (LE_Interp.soundSE hE HB W'.fits).2 hBb_sd |>.out
        have W2 := cons hp hA1 ha.hasType.1 ((LR Γ₀).left hv) W
        have vtBB := toValTy le le' (aty.2 _ hp).toType iv hmb ((ihB iB iv hmb).1 W2).1
        have W3 := cons hp hA1 ha hv W
        refine ((LR Γ₀).whr
          (tbeta (bodyTy W.symm HX' HY') (HX'σ.defeqDF ha.hasType.1) (hBsub W2).symm)
          (tbeta (bodyTy W.symm HX' HY') (HX'σ.defeqDF ha.hasType.2) (hBsub W3).symm)).2 <|
          (LR Γ₀).conv ((LR Γ₀).symm_ty vtBB) ?_
        exact ((IH W'.fits).1 (cons hp hA1 ha' hv' W.symm.left)).2
    · have W' := cons hp hA1 ha hv W
      have hB' := hBsub W'
      exact ((LR Γ₀).whr (tbeta (bodyTy W HX HY) (HXσ.defeqDF ha) hB'.hasType.1)
          (tbeta (bodyTy W.symm HX' HY') (HX'σ.defeqDF ha) hB'.symm)).2 <|
        (LR _).trans ((IH W'.fits).2 W'.left) ((IH W'.fits).1 W').2
  | @forallEDF Γ A A' u body body' v HA HBody _ ihA ihBody =>
    cases hmem.unfold with
    | bot hm =>
      cases hm.unfold with
      | forallE => let .sort h := hA; cases (TShape.LE.lift_r (by simp [TShape.sort])).1 h
      | _ => exact .bot hmem.isType
    | sort => cases n <;> have .forallE _ _ _ _ h := hM <;> cases TShape.sort_not_le_forallE h
    | @lam _ f₀ =>
      revert hM; unfold WShape.lam'; split <;> [skip; exact fun _ => .bot hmem.isType]
      intro | .forallE _ _ _ _ h => cases TShape.lam_not_le_forallE h
    | ctor => have .forallE _ _ _ _ h := hM; cases TShape.ctor_not_le_forallE h
    | indTy => have .forallE _ _ _ _ h := hM; cases TShape.indTy_not_le_forallE h
    | @forallE k a₂ a₁ r aty
    have aty := WShape.HasTypePi.iff.1 aty
    have hA1 := hM.forallE_inv.1
    have cons := Adequate.cons ihA (HA.mono hE)
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;> (
      have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ :=
        (LE_Interp.soundSE hE HA W.left.fits).2 hA1 |>.out
      have HAAσ := (HA.defeqE hE).subst W.wf₀ W.left.toSubstEq
      have S' := W.toSubstEq.lift (HA.defeqE hE).hasType.1
      -- D6: the typed ambient and the typed (reflexive) Π reductions, from the rule itself
      have Hf := IsDefEq.forallEDF (HA.defeqE hE) (HBody.defeqE hE)
      have HFl := Hf.subst W.wf₀ W.left.toSubstEq)
    · have HAσ := (HA.defeqE hE).hasType.1.subst W.wf₀ W.toSubstEq
      have HA'σ := (HA.defeqE hE).hasType.2.subst W.wf₀ W.toSubstEq
      constructor
      · refine ⟨⟨_, _, .sort⟩, A.subst σ, body.subst σ.lift, A.subst σ', body.subst σ'.lift, u, v,
          ⟨⟨_, HFl.hasType.1⟩, .rfl⟩, ⟨⟨_, (Hf.hasType.1.subst W.wf₀ W.toSubstEq).hasType.2⟩, .rfl⟩,
          HAσ, (HBody.defeqE hE).hasType.1.subst (Ctx.WF.cons W.wf₀ HAAσ.hasType.1) S', ?_, ?_⟩
        · exact toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
        simp [LRS.PiDefEq, inst_lift_cons]
        refine ⟨fun _ _ p hp ha hv => ?_, fun _ p hp ha hv => ?_⟩ <;>
          have hB := hM.forallE_inv'.2 p <;> [constructor <;> [
            have W' := cons hp hA1 ha hv W.left;
            ( have := toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
              have W' := cons hp hA1 (HAσ.defeqDF ha) ((LR Γ₀).conv this hv) W.symm.left )];
            have W' := cons hp hA1 ha.hasType.1 ((LR Γ₀).left hv) W] <;>
        · have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
            (LE_Interp.soundSE hE HBody W'.fits).2 hB |>.out
          exact toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).1 W').1
      · refine ⟨⟨_, _, .sort⟩, A'.subst σ, body'.subst σ.lift, A'.subst σ', body'.subst σ'.lift, u, v,
          ⟨⟨_, HFl.hasType.2⟩, .rfl⟩, ⟨⟨_, (Hf.hasType.2.subst W.wf₀ W.toSubstEq).hasType.2⟩, .rfl⟩,
          HA'σ, HAAσ.defeqDF_l
            ((HBody.defeqE hE).hasType.2.subst (Ctx.WF.cons W.wf₀ HAAσ.hasType.1) S'), ?_, ?_⟩
        · exact toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).2
        simp [LRS.PiDefEq, inst_lift_cons]
        have := toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').2 W.left)
        refine ⟨fun _ _ p hp ha hv => ?_, fun _ p hp ha hv => ?_⟩ <;> (
          have hv := (LR Γ₀).conv ((LR Γ₀).symm_ty this) hv
          have ha := HAAσ.symm.defeqDF ha
          have hB := hM.forallE_inv'.2 p) <;> [constructor <;> [
            have W' := cons hp hA1 ha hv W.left;
            ( have := toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
              have W' := cons hp hA1 (HAσ.defeqDF ha) ((LR Γ₀).conv this hv) W.symm.left )];
            have W' := cons hp hA1 ha ((LR Γ₀).left hv) W] <;>
        · have ⟨_, _, _, le, le', iB, iv, hmb⟩ := (LE_Interp.soundSE hE HBody W'.fits).2 hB |>.out
          exact toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).1 W').2
    · refine ⟨⟨_, _, .sort⟩, A.subst σ, body.subst σ.lift, A'.subst σ, body'.subst σ.lift, u, v,
        ⟨⟨_, HFl.hasType.1⟩, .rfl⟩, ⟨⟨_, HFl.hasType.2⟩, .rfl⟩,
        HAAσ, (HBody.defeqE hE).subst (Ctx.WF.cons W.wf₀ HAAσ.hasType.1) S', ?_, ?_⟩
      · exact toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').2 W)
      simp [LRS.PiDefEq, inst_lift_cons]
      refine ⟨fun _ _ p hp ha hv => ?_, fun _ p hp ha hv => ?_⟩ <;> (
        have hB := hM.forallE_inv'.2 p
        have W' := cons hp hA1 ha hv W
        have ⟨_, _, _, le, le', iB, iv, hmb⟩ := (LE_Interp.soundSE hE HBody W'.fits).2 hB |>.out)
      · exact ⟨toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).1 W').1,
               toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).1 W').2⟩
      · exact toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).2 W')
  | @defeqDF Γ A' B' u' _ _ Hty He ihTy ihE =>
    have tyConv {σ} (W : SubstWF Γ₀ σ σ Γ ρ) :=
      have hA' := (LE_Interp.soundSE hE Hty W.fits).1.2 hA
      have ⟨_, a', _, le_n, le_a, hA'', hSort, hmem'⟩ :=
        (LE_Interp.soundSE hE Hty W.fits).2 hA' |>.out
      toValTy le_n le_a hmem.isType hSort hmem' ((ihTy hA'' hSort hmem').2 W)
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;>
      have hA' := (LE_Interp.soundSE hE Hty W.left.fits).1.2 hA
    · exact ⟨(LR Γ₀).conv (tyConv W.left) ((ihE hM hA' hmem).1 W).1,
             (LR Γ₀).conv (tyConv W.left) ((ihE hM hA' hmem).1 W).2⟩
    · exact (LR Γ₀).conv (tyConv W) ((ihE hM hA' hmem).2 W)
  | beta He Ha Happ Hinst _ihe _iha ihapp ihinst =>
    refine ⟨fun _ _ W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · exact ((ihapp hM hA hmem).1 W).1
    · exact ((ihinst ((LE_Interp.soundSE hE (.beta He Ha Happ Hinst) W.fits).1.1 hM) hA hmem).1 W).2
    · -- D6: both reductions typed at the ambient, from `Happ` and the `beta` rule, substituted
      have tM := (Happ.defeqE hE).subst W.wf₀ W.toSubstEq
      have tN := (IsDefEq.beta (He.defeqE hE) (Ha.defeqE hE)).subst W.wf₀ W.toSubstEq
      exact ((LR _).whr ⟨tM, .rfl⟩ ⟨tN, subst_inst ▸ .tail .rfl .beta⟩).1 ((ihapp hM hA hmem).2 W)
  | @eta _ e0 A0 B0 He Hlam ihe ihlam =>
    refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · exact ((ihlam hM hA hmem).1 W).1
    · exact ((ihe ((LE_Interp.soundSE hE (.eta He Hlam) W.fits).1.1 hM) hA hmem).1 W).2
    have hM' := (LE_Interp.soundSE hE (.eta He Hlam) W.fits).1.1 hM
    cases hmem.unfold with
    | bot hm => exact (LR _).bot hm
    | sort => cases n <;> let .lam _ _ _ h := hM <;> cases TShape.sort_not_le_lam' h
    | forallE => let .lam _ _ _ h := hM; cases TShape.forallE_not_le_lam' h
    | ctor => let .lam _ _ _ h := hM; cases TShape.ctor_not_le_lam' h
    | indTy => let .lam _ _ _ h := hM; cases TShape.indTy_not_le_lam' h
    | lam htm
    revert hM hM' hmem; unfold WShape.lam'
    split <;> intro hM hM' hmem <;> [skip; exact (LR _).bot hmem.isType]
    have ⟨A₁, A₂, u, v, whr_t, htA₁, vtyA₁, htA₂, edge, vpi_M⟩ := (ihlam hM hA hmem).2 W
    have ⟨_, _, _, _, whr_N, _, _, _, _, vpi_N⟩ := (ihe hM' hA hmem).2 W
    cases whr_t.2.determ .forallE whr_N.2 .forallE
    refine ⟨A₁, A₂, u, v, whr_t, htA₁, vtyA₁, htA₂, edge, ?_, fun a p hp ha hv => ?_⟩
    · exact fun a b p hp ha hv => ⟨(vpi_M.1 hp ha hv).1, (vpi_N.1 hp ha hv).2⟩
    -- D6: the eta step typed at `A₂.inst a`, from the substituted `eta` rule and `whr_t`
    obtain ⟨_, tA⟩ := whr_t.1
    have tE : Γ₀ ⊢ (SExpr.lam A0 (.app e0.lift (.bvar 0))).subst σ ≡ e0.subst σ : .forallE A₁ A₂ :=
      tA.defeqDF ((IsDefEq.eta (He.defeqE hE)).subst W.wf₀ W.toSubstEq)
    refine ((LR _).whr ⟨.appDF tE ha, ?_⟩ ⟨.appDF tE.hasType.2 ha, .rfl⟩).2 (vpi_N.2 hp ha hv)
    rw [(?_ : (e0.subst σ).app a = _)]; · exact .tail .rfl .beta
    rw [inst_lift_cons, subst, lift_subst_cons]; rfl
  | proofIrrel Hp =>
    refine .fits fun W => ?_
    have ⟨_, _, s, le_n, le_a, _, hSort, hmem'⟩ := (LE_Interp.soundSE hE Hp W).2 hA |>.out
    have hS := WShape.HasType.mono_r hSort.le_sort' .sort hmem'; simp at hS
    have ha' := hS.mono_r ((TShape.LE.lift_l le_n).1 le_a) ((WShape.HasType.lift le_n).2 hmem)
    cases (WShape.lift_eq_bot le_n).1 (hS.proofIrrel ha')
    exact .bot hmem.isType
  | extra h1 h2 Hl Hr ihl ihr =>
    -- R6 (E5): the soundness transport is the λ-rule `extra` case of `strongSoundS`
    have hS := strongSoundS_extra_lam (hE.2 h1) h2 (LE_Interp.strongSoundS (Hl.mono hE))
      (LE_Interp.strongSoundS (Hr.mono hE))
    refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · exact ((ihl hM hA hmem).1 W).1
    · exact ((ihr ((hS.sound W.fits).1 hM) hA hmem).1 W).2
    · have ⟨⟨hA1, _⟩, hA2, hA3⟩ := Params.henv.closed.2 (hE.2 h1)
      have Dl := (ihl hM hA hmem).2 W
      have Dr := (ihr ((hS.sound W.fits).1 hM) hA hmem).2 W
      rw [hA1.mkInstS.subst_eq .zero, hA3.mkInstS.subst_eq .zero] at Dl
      rw [hA2.mkInstS.subst_eq .zero, hA3.mkInstS.subst_eq .zero] at Dr
      rw [hA1.mkInstS.subst_eq .zero, hA2.mkInstS.subst_eq .zero, hA3.mkInstS.subst_eq .zero]
      -- D5: the rule is a λ-closure over `Δ` of an open typed equation `L ≡ R : Ty`
      obtain ⟨Δ, L, R, Ty, hl, hr, hTy, hwf, hLR, p, r, m1, m2, dfs, a1, a2, a3, a4, a5⟩ :=
        Params.extra_pat Γ₀ (hE.2 h1) h2
      -- `WHRed.extra` on the open instance
      have hred : Δ.reverse ++ Γ₀ ⊢ L ⤳ R := a5 ▸ .extra a1 a2 a3 a4
      rw [hl, hTy] at Dl; rw [hr, hTy] at Dr; rw [hl, hr, hTy]
      -- through `LamDefEq`, one typed beta layer per binder, then the open step (`LR.lamRule`)
      simpa only [subst_id] using LR.lamRule W.wf₀ Δ (hwf W.wf₀) hLR hred .nil
        (by simpa only [subst_id] using Dl) (by simpa only [subst_id] using Dr)

/-- `LR.adequacy_rank` at every bound, by strong induction on `k` (D4 measure level (1)). -/
theorem LR.adequacy_rank_wf :
    ∀ k {Γ M N A}, IsDefEqStrong (Params.env.below Params.rank k) Γ M N A →
      ∀ {ρ n} {m a : WShape n}, LE_Interp ρ m.T M → LE_Interp ρ a.T A → m.HasType a →
        Adequate Γ₀ Γ ρ M N A m a := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro _ _ _ _ H _ _ _ _ hM hA hmem
    exact adequacy_rank (fun k' hk => ih k' hk) H hM hA hmem

/-- Main adequacy theorem for the logical relation. -/
theorem LR.adequacy (hΓ : ⊢ Γ) (H : Γ ⊢ M ≡ N : A)
    (hM : LE_Interp ρ m.T M) (hA : LE_Interp ρ a.T A) (hmem : m.HasType a) :
    Adequate (n := n) Γ₀ Γ ρ M N A m a :=
  let ⟨_, H'⟩ := (H.strong hΓ).exists_below Params.rank
  adequacy_rank_wf _ H' hM hA hmem

theorem forallE_whRed_l (hΓ : ⊢ Γ) (d : Γ ⊢ A₀ ≡ SExpr.forallE B₁ F₁ : .sort s) :
    ∃ B₀ F₀, Γ ⊢ A₀ ⤳* .forallE B₀ F₀ ∧ ∃ u v,
      Γ ⊢ B₀ ≡ B₁ : .sort u ∧ B₀::Γ ⊢ F₀ ≡ F₁ : .sort v := by
  have hPi : LE_Interp .nil (WShape.T (n := 1) (.forallE .bot WShapeFun.bot)) (.forallE B₁ F₁) := by
    refine .forallE' .bot .bot (.bot <| .bot' .sort) fun _ h => ?_
    cases h.bot_r; exact WShapeFun.bot_app.symm ▸ .bot
  have hmem : WShape.HasType (n := 1) (.forallE .bot WShapeFun.bot) (.sort (s ≠ .zero)) := by
    refine WShape.HasType.forallE_l.2 ⟨_, ?_, rfl⟩
    refine WShape.HasTypePi.iff.2 ⟨.bot (.bot' .sort), fun x hx => ?_⟩
    cases WShape.HasType.bot_r hx; exact WShapeFun.bot_app.symm ▸ .bot .sort
  have := (LR.adequacy hΓ d ((LE_Interp.sound hΓ d .nil).1.2 hPi) (.sort TShape.sort_eqv.1) hmem).2 (.id hΓ)
  have ⟨_, _, _, _, _, _, _, redA₀, redPi, convB, convF, _⟩ :=
    subst_id ▸ subst_id ▸ subst_id ▸ this
  cases WHNF.forallE.whRedS redPi.2; exact ⟨_, _, redA₀.2, _, _, convB, convF⟩

/-- Pi–Pi injectivity: if two Pi types are definitionally equal,
their domains and codomains are each definitionally equal. -/
theorem forallE_inv (hΓ : ⊢ Γ) (H : Γ ⊢ SExpr.forallE A₀ B₀ ≡ SExpr.forallE A₁ B₁ : .sort s) :
    ∃ u v, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ A₀::Γ ⊢ B₀ ≡ B₁ : .sort v := by
  have ⟨_, _, red, H⟩ := forallE_whRed_l hΓ H
  cases WHNF.forallE.whRedS red; exact H

theorem sort_forallE_inv (hΓ : ⊢ Γ) : ¬Γ ⊢ .sort u ≡ SExpr.forallE A₁ B₁ : .sort s :=
  fun H => have ⟨_, _, H⟩ := forallE_whRed_l hΓ H; nomatch WHNF.sort.whRedS H.1

/-- Sort injectivity: if two sorts are definitionally equal, their levels are equal. -/
theorem sort_inv (hΓ : ⊢ Γ) (d : Γ ⊢ SExpr.sort u ≡ SExpr.sort v : V) : u = v := by
  have hM : LE_Interp .nil (WShape.T (n := 1) (.sort (decide (u ≠ .zero)))) (.sort u) :=
    .sort TShape.sort_eqv.1
  have ⟨n, mU, mV, h1, h2, h3, hA, h5⟩ := (LE_Interp.sound hΓ d .nil).2 hM |>.out
  have h2' := WShape.lift_sort ▸ (TShape.LE.lift_l h1).1 h2; dsimp only at h2'
  cases WShape.sort_le.1 h2'
  cases show mV = (.sort true : WShape 1).lift n by
    let _+1 := n
    simp only [WShape.HasType, WShape.sort] at h5
    ext1; generalize mV.val = mv at h5
    let .sort := Shape.HasType.unfold_iff.1 h5; rfl
  have h1' : (1 : Nat) ≤ n := h1
  have := (LR.adequacy hΓ d hM (hA.unlift h1') .sort).2 (.id hΓ)
  have ⟨_, w, h1, h2⟩ := (LR _).sort_iff.1 (subst_id ▸ subst_id ▸ subst_id ▸ this)
  cases WHNF.sort.whRedS h1.2; cases WHNF.sort.whRedS h2.2; rfl
