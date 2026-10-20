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

/-! ### Field lowering for the pattern leaf (E6a)

PLAN D4 "RHS step" steps 1-2, from experiment E6a (`docs/const-case/plan/E6a/E6a-REPORT.md`): the
lowered valuation `ρ_low` (`Valuation.lowerCtx`, `Valuation.lower`) and the lowering lemma
`LR.rhs_lower` (proved as `LR.rhs_lower2`, which keeps one more conclusion). `LR.rhs_lower` is
E6a's corrected statement; the pinned one (`historical/RhsLowerStmt.lean:208-234`) is false
(E6a-REPORT: `T.pinned_false_const`, `T.pinned_false_iota`). Differences, each needed:
* `gen := Pattern.gen`, `idx := Pattern.pathIdx p`, `rank := Params.rank` (`Params.pat_typed` /
  `pat_defeq` give the RHS typing, without which an ill-typed RHS breaks the main conjunct);
* `hR : ∀ m e, R m e → LE_Interp ρ₀ m e` (`LE_Interp.const`'s last premise; without it the
  non-self fixed leaves are unconstrained);
* `hhead`: each path is a function-position-safe variable (`m2 path ≤` its entry; the recursor
  arguments, from the spine lemma's `hρ`) or has an inductive-type constant as its context type
  (the constructor fields, from `gen_head_ctor` + `ctor_fields_closed`);
* self clause: the `R`-witness `R me (.const c' ls') ∧ me ≤ s` is required only when `s ≠ ⊥` (an
  occurrence under an `RHS.bot` node has none); in exchange the clause names the occurrence
  (`selfLeaves[j] = .const c' us`, `ls' = us.map (instV ls)`) and keeps `us.length = ci'.uvars`
  unconditionally (from `pat_defeq`).
`hm` is kept from the pinned statement and is unused.

The proof of the main conjunct is D4's argument [A]: by induction on `LE_Interp.RHS`
(`LR.rhs_lower_core`), with the strong typing of `rhsAbs` (from `pat_typed`) inverted along the
term by `StrongSoundCore`. Every function position is interpreted at `ρ_low` (fixed leaves by `hR`,
self leaves by the `LocalIH` bound, recursor arguments by `hhead`), so it has a typed upper bound by
soundness (`SoundTy`), whose `HasDom` collapses an untyped argument shape to a typed one below it
(`app_collapse`); arguments then only need the downward claim, which `hvar` gives at variables. A
constructor-field variable never sits in function position (`const_indTy_not_forallE`). -/

/-! #### The lowered valuation (`historical/RhsLowerStmt.lean:195-201`, verbatim) -/

/-- ρ_low's pattern-context part (PLAN D4 step 1), over `.nil` (the valuation of `SubstWF.id`,
base context `Γ₀`), innermost first: the lowered field entries `fields`, then the recursor
arguments `ρ 1 … ρ m` (`ρ 0` is the major). `fields[i]` is `l_i.T` when the ctor shape's field
`l_i` is `⊥` or a ctor shape, else `⊥`; `⊥` when the field type is Prop-valued. -/
def Valuation.lowerCtx (fields : List TShape) (ρ : Valuation) (m : Nat) : Valuation :=
  fields.foldr (fun x ρ' => ρ'.push x) <|
    (List.range m).foldr (fun i ρ' => ρ'.push (ρ (i + 1))) .nil

/-- ρ_low (PLAN D4 step 1): the self entries (index `j` = `j`-th self) on top of `lowerCtx`. -/
def Valuation.lower (selfs fields : List TShape) (ρ : Valuation) (m : Nat) : Valuation :=
  selfs.foldr (fun x ρ' => ρ'.push x) (Valuation.lowerCtx fields ρ m)

/-! #### Valuation, lifting and lookup plumbing -/
/-- Pushing a list shifts the old valuation by its length. -/
theorem foldr_push_add (ρ : Valuation) : ∀ (xs : List TShape) (i : Nat),
    (xs.foldr (fun x ρ' => ρ'.push x) ρ) (xs.length + i) = ρ i
  | [], i => by simp
  | x :: xs, i => by
    rw [List.length_cons, Nat.add_right_comm]
    exact foldr_push_add ρ xs i

/-- The pushed entries come first, `xs[0]` at index `0`. -/
theorem foldr_push_lt (ρ : Valuation) : ∀ (xs : List TShape) (i : Nat) (s : TShape),
    xs[i]? = some s → (xs.foldr (fun x ρ' => ρ'.push x) ρ) i = s
  | [], _, _, h => by simp at h
  | x :: xs, 0, s, h => by simpa [Valuation.push] using h
  | x :: xs, i+1, s, h => foldr_push_lt ρ xs i s (by simpa using h)

theorem liftK_add (M : SExpr) (a : Nat) : ∀ b, liftK M (a + b) = liftK (liftK M a) b
  | 0 => rfl
  | b+1 => congrArg SExpr.lift (liftK_add M a b)

/-- `mkInst` commutes with `VExpr.liftN k` (as `liftK`). -/
theorem mkInst_liftN (ls : List SLevel) (Y : VExpr) : ∀ k, mkInst ls (Y.liftN k) = liftK (mkInst ls Y) k
  | 0 => by simp [liftK]
  | k+1 => by
    rw [VExpr.liftN_succ, VExpr.lift_eq_lift', mkInst_lift', mkInst_liftN ls Y k]; rfl

theorem liftK_const (c : Name) (ls : List SLevel) : ∀ k, liftK (.const c ls) k = .const c ls
  | 0 => rfl
  | k+1 => by rw [liftK, liftK_const c ls k]; rfl

/-- Weakening of `LE_Interp` over a pushed list (`LE_Interp.weak_iff`, iterated). -/
theorem LE_Interp_foldr_push_liftK {ρ : Valuation} {m : TShape} {M : SExpr} :
    ∀ (xs : List TShape), LE_Interp (xs.foldr (fun x ρ' => ρ'.push x) ρ) m (liftK M xs.length) ↔
      LE_Interp ρ m M
  | [] => Iff.rfl
  | _ :: xs => LE_Interp.weak_iff.trans (LE_Interp_foldr_push_liftK xs)

/-- A lookup is the `i`-th entry lifted `i+1` times. -/
theorem lookup_eq : ∀ {Γ : List SExpr} {i : Nat} {A : SExpr}, Lookup Γ i A →
    ∃ B, Γ[i]? = some B ∧ A = liftK B (i+1)
  | _ :: _, 0, _, .zero => ⟨_, rfl, rfl⟩
  | _ :: _, _+1, _, .succ h => by
    obtain ⟨B, h1, rfl⟩ := lookup_eq h
    exact ⟨B, by simpa using h1, rfl⟩

/-! #### Shape lemmas -/

/-- The shape `Π (_ : ⊥), ⊥` interprets every Π-type. -/
theorem forallE_bot_interp {ρ : Valuation} {A B : SExpr} :
    LE_Interp ρ (WShape.forallE (n := 0) .bot .bot).T (.forallE A B) :=
  .forallE' .bot .bot (WShape.HasDom.bot (.bot' .sort)) fun x _ => by
    rw [WShapeFun.bot_app]; exact .bot

theorem forallE_not_le_indTy {a : WShape n} {f : WShapeFun n} :
    ¬(.forallE a f : WShape (n+1)).T ≤ (WShape.indTy : WShape (n'+1)).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_forallE le₁, WShape.lift_indTy, WShape.le_indTy]
  rintro (h | h) <;> cases congrArg (·.1) h

theorem forallE_not_le_bot {a : WShape n} {f : WShapeFun n} :
    ¬(.forallE a f : WShape (n+1)).T ≤ TShape.bot := by
  rw [TShape.le_bot]; intro h; cases congrArg (·.1) h

/-- An inductive-type constant is never interpreted by a Π-shape. -/
theorem const_indTy_not_forallE {ρ : Valuation} {I : Name} {ls : List SLevel} {k : Nat}
    (hI : Params.classify I = some (.indTy k)) :
    ¬LE_Interp ρ (WShape.forallE (n := 0) .bot .bot).T (.const I ls) := by
  intro h
  generalize eM : (WShape.forallE (n := 0) .bot .bot).T = mT at h
  generalize eC : SExpr.const I ls = M at h
  cases h with
  | bot =>
    injection eM with e1 e2
    subst e1
    cases congrArg (·.1) (eq_of_heq e2)
  | bvar | sort | app | lam | forallE => cases eC
  | const h1 h2 h3 h4 h5 h6 h7 =>
    injection eC with e1 e2; subst e1 e2; subst eM
    cases h6 with
      | bot => exact forallE_not_le_bot (h3.trans TShape.bot_eqv.1)
      | lam _ hle => exact TShape.forallE_not_le_lam' (h3.trans hle)
      | ctor hc => cases hI.symm.trans hc
      | indTy _ hle => exact forallE_not_le_indTy (h3.trans hle)
      | pat hP hM => cases hI.symm.trans (pat_arity hP hM.arity)

/-- The function-position collapse ([A] of PLAN D4 step 2): a typed upper bound of the
function shape has `HasDom`, so the argument shape may be replaced by a typed one below it. -/
theorem app_collapse {ρ : Valuation} {F X A B : SExpr} {k : Nat} {f : WShape (k+1)}
    {a : WShape k} {ms : TShape}
    (H1 : InterpTyped ρ f.T F (.forallE A B))
    (hX : ∀ {n} {y b : WShape n}, y.T ≤ a.T → y.HasType b → LE_Interp ρ b.T A →
      LE_Interp ρ y.T X)
    (hms : ms ≤ (f.app a).T) : LE_Interp ρ ms (F.app X) := by
  by_cases hm : ms ≤ .bot
  · exact TShape.le_bot'.1 hm ▸ .bot
  obtain ⟨U, u, le_f, hU, hu, hUu⟩ := H1
  have hf : ¬ U ≤ .bot := fun h => by
    rw [show f = .bot from TShape.le_bot.1 (le_f.trans h), WShape.bot_app] at hms
    exact hm (hms.trans TShape.bot_le')
  have hs : ¬ u ≤ .bot := fun h => hf (hUu.bot_r' h)
  cases hu with
  | bot => exact absurd TShape.bot_le' hs
  | forallE b1 _ _ _ b5 =>
    cases b5.le_forall with
    | bot b5 => exact absurd b5 hs
    | @forallE m₀ _ _ b'' _ b5 _ =>
      obtain c1 | ⟨n₂, g, rfl, c1⟩ := hUu.ty_forallE_inv
      · exact absurd (c1 ▸ .rfl) hf
      have hk1 : k ≤ max k (max n₂ m₀) := Nat.le_max_left ..
      have hk2 : n₂ ≤ max k (max n₂ m₀) := Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)
      have hk3 : m₀ ≤ max k (max n₂ m₀) := Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)
      have c1 := (TShape.HasTypeLam.def hk2 hk3).1 c1
      obtain ⟨x', e1, e2, e3⟩ := WShape.HasDom.iff.1 c1.2.1 (a.lift _)
      have hb : LE_Interp ρ (b''.lift (max k (max n₂ m₀))).T A := (b1.mono b5).lift hk3
      have hx' : LE_Interp ρ x'.T X := hX (e1.T.trans (TShape.lift_eqv hk1).1) e2 hb
      have hg : LE_Interp ρ (WShape.lam' (g.lift (max k (max n₂ m₀)))).T F := by
        have := hU.lift (Nat.succ_le_succ hk2)
        rwa [WShape.lift_lam' hk2] at this
      refine .mono ?_ (hg.app' hx')
      rw [WShape.lam'_app]
      refine hms.trans ((TShape.app_mono (f' := WShape.lam' (g.lift (max k (max n₂ m₀))))
        (a' := a.lift _) ?_ (TShape.lift_eqv hk1).2).trans ?_)
      · have := (TShape.lift_eqv (a := (WShape.lam' g).T) (Nat.succ_le_succ hk2)).2
        rw [WShape.lift_lam' hk2] at this
        exact le_f.trans this
      · rw [WShape.lam'_app]; exact e3.T

/-! #### `Pattern.gen` plumbing -/

/-- The head of a matched pattern is the constant matched. -/
theorem LE_Interp.Matches.head {p : Pattern} {n} {c : Name} {rargs : List (WShape n)} {m}
    (H : LE_Interp.Matches p c rargs m) : p.head = c := by
  induction H with
  | const => rfl
  | var _ ih => exact ih
  | app _ _ ih _ => exact ih

omit [Params] in
theorem pathIdx_lt : ∀ (p : Pattern) (x : p.Path), p.pathIdx x < p.nvars
  | .const _, x => x.elim
  | .app f a, .inl x => by
    have := pathIdx_lt f x; simp only [Pattern.pathIdx_inl, Pattern.nvars]; omega
  | .app f a, .inr x => by
    have := pathIdx_lt a x; simp only [Pattern.pathIdx_inr, Pattern.nvars]; omega
  | .var f, none => by simp [Pattern.nvars]
  | .var f, some x => by
    have := pathIdx_lt f x; simp only [Pattern.pathIdx_some, Pattern.nvars]; omega

omit [Params] in
/-- `Pattern.gen` succeeds only at a head with a declaration, and its context has one entry
per path. -/
theorem gen_head_ctx {env : VEnv} {rank : Name → Nat} {classify : Name → Option Classification}
    {p : Pattern} {r : p.RHS} {g : PatGen} (hg : Pattern.gen env rank classify p r = some g) :
    (∃ ci, env.constants p.head = some ci) ∧ g.ctx.length = p.nvars := by
  obtain ⟨-, h2, -⟩ := Pattern.gen_eq_some hg
  match p, h2 with
  | .const c, h2 =>
    simp only [Pattern.genCore, Option.map_eq_some_iff, Prod.mk.injEq] at h2
    obtain ⟨ci, h1, h2, -⟩ := h2
    exact ⟨⟨ci, h1⟩, by rw [← h2]; rfl⟩
  | .app f a, h2 =>
    simp only [Pattern.genCore] at h2
    split at h2
    · next rec m c' n hf ha =>
      cases Pattern.eq_varN_of_asVarN hf; cases Pattern.eq_varN_of_asVarN ha
      obtain ⟨ci, ci', Hs, I, us, Bmaj, Fs, R', h1, -, -, t4, t5, h6, -, -⟩ :=
        Pattern.genIota_eq_some h2
      obtain ⟨l4, -⟩ := VExpr.piTelescope_eq_some t4
      obtain ⟨l5, -⟩ := VExpr.piTelescope_eq_some t5
      refine ⟨⟨ci, ?_⟩, ?_⟩
      · show env.constants (Pattern.varN (.const rec) m).head = some ci
        rw [Pattern.head_varN]; exact h1
      · rw [h6, Pattern.nvars, Pattern.nvars_varN, Pattern.nvars_varN]
        simp [l4, l5, Pattern.nvars]; omega
    · cases h2
  | .var _, h2 => cases h2

/-! #### The lowering lemma -/

/-- Pushing typed entries for closed, well-typed types keeps `Fits` (`Valuation.Fits.cons`). -/
theorem fits_foldr_push {Γ₀ Δ : List SExpr} {ρ : Valuation} (W : Valuation.Fits Γ₀ Δ ρ) :
    ∀ (As : List SExpr) (xs : List TShape), As.length = xs.length →
    (∀ j A x, As[j]? = some A → xs[j]? = some x →
      (∃ u, StrongSound (As.drop (j+1) ++ Δ) A (.sort u)) ∧
      ∃ a, (∀ ρ', LE_Interp ρ' a A) ∧ x.HasType a) →
    Valuation.Fits Γ₀ (As ++ Δ) (xs.foldr (fun x ρ' => ρ'.push x) ρ)
  | [], [], _, _ => W
  | A :: As, x :: xs, hl, H => by
    have IH := fits_foldr_push W As xs (by simpa using hl) fun j A' x' h1 h2 =>
      H (j+1) A' x' (by simpa using h1) (by simpa using h2)
    obtain ⟨⟨u, hA⟩, a, ha, hx⟩ := H 0 A x rfl rfl
    exact .cons IH (InterpTyped.hsort (hA.sound IH)) (ha _) hx

/-- Inversion of an interpretation of a constant (`⊥`, or the `LE_Interp.const` data). -/
theorem const_inv {ρ : Valuation} {m : TShape} {c : Name} {ls : List SLevel}
    (H : LE_Interp ρ m (.const c ls)) :
    (∃ k, m = (WShape.bot (n := k)).T) ∨
      ∃ ci, Params.env.constants c = some ci ∧ ls.length = ci.uvars := by
  generalize eC : SExpr.const c ls = M at H
  cases H with
  | bot => exact .inl ⟨_, rfl⟩
  | bvar | sort | app | lam | forallE => cases eC
  | const h1 h2 => injection eC with e1 e2; subst e1 e2; exact .inr ⟨_, h1, h2⟩

/-- What the lowering induction records for the self entry `s` of the leaf occurrence `e`:
`⊥`, or `LocalIH`'s typed upper bound of an `R`-witness. -/
def LR.SelfFact (Γ₀ : List SExpr) (ρ₀ : Valuation) (ls : List SLevel) (R : TShape → SExpr → Prop)
    (e : VExpr) (s : TShape) : Prop :=
  (∃ k, s = (WShape.bot (n := k)).T) ∨
  ∃ (c' : Name) (us : List VLevel) (ci' : VConstant) (me : TShape), e = .const c' us ∧
    Params.env.constants c' = some ci' ∧ us.length = ci'.uvars ∧ R me (mkInst ls e) ∧ me ≤ s ∧
    (∃ (k : Nat) (x b : WShape k), s = x.T ∧ x.HasType b ∧
      LE_Interp ρ₀ b.T (mkInst (us.map (SLevel.instV ls)) ci'.type)) ∧
    LR.ConstGoal Γ₀ ρ₀ s c' (us.map (SLevel.instV ls)) ci'

/-- A self entry for an `R`-witnessed leaf, from `hR` and `LR.LocalIH`. -/
theorem LR.selfFact_exists {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name} {ls : List SLevel}
    {R : TShape → SExpr → Prop} {rank : Name → Nat} (LIH : LR.LocalIH rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e) {e : VExpr} {c' : Name} {us : List VLevel}
    (he : e = .const c' us) (hrk : rank c' = rank c) {ms : TShape} (hms : R ms (mkInst ls e)) :
    ∃ s, LR.SelfFact Γ₀ ρ₀ ls R e s ∧ ms ≤ s := by
  subst he
  obtain ⟨k, rfl⟩ | ⟨ci', h1, h2⟩ := const_inv (hR _ _ hms)
  · exact ⟨_, .inl ⟨k, rfl⟩, .rfl⟩
  · rcases LIH _ _ hms c' _ ci' rfl hrk h1 h2 with ⟨k, rfl⟩ | ⟨n, m', a', le, ty, ha, H⟩
    · exact ⟨_, .inl ⟨k, rfl⟩, .rfl⟩
    · exact ⟨m'.T, .inr ⟨c', us, ci', _, rfl, h1, by simpa using h2, hms, le,
        ⟨n, m', a', rfl, ty, ha⟩, .inr ⟨n, m', a', .rfl, ty, ha, H⟩⟩, le⟩

/-- The lowering induction (on `LE_Interp.RHS`). For the subterm `t = mkInst ls (r.toVExpr sel K j)`
of the abstracted RHS, it produces the subtree's self entries `sl` and, at every fitting `ρ'`
holding them at `j, j+1, …`: the downward claim (every typed shape below the RHS shape whose type
interprets `t`'s type is interpreted at `ρ'`), and, unless `r` is a variable not covered by
`hhead`'s first disjunct, the RHS shape itself is interpreted at `ρ'`. -/
theorem LR.rhs_lower_core {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name} {ls : List SLevel}
    {R : TShape → SExpr → Prop} {rank : Name → Nat} (LIH : LR.LocalIH rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e) {p : Pattern} {m2 : p.Path → TShape}
    (sel : VExpr → Bool) (hsel : ∀ e, sel e = true → ∃ c' us, e = .const c' us ∧ rank c' = rank c)
    (K : Nat) (Γ : List SExpr) :
    ∀ {ms : TShape} {r : p.RHS}, LE_Interp.RHS ls m2 R ms r →
    ∃ sl : List TShape, sl.length = (r.selfLeaves sel).length ∧
      (∀ (i : Nat) (s : TShape) (e : VExpr), sl[i]? = some s → (r.selfLeaves sel)[i]? = some e →
        LR.SelfFact Γ₀ ρ₀ ls R e s) ∧
      ∀ (j : Nat) {Γb : List SExpr} {ρ' : Valuation}, Valuation.Fits Γb Γ ρ' →
        (∀ (i : Nat) (s : TShape), sl[i]? = some s → s ≤ ρ' (j + i)) →
        (∀ path {n} {y b : WShape n} {T'}, Lookup Γ (K + p.pathIdx path) T' → y.T ≤ m2 path →
          y.HasType b → LE_Interp ρ' b.T T' → y.T ≤ ρ' (K + p.pathIdx path)) →
        (∀ path, m2 path ≤ ρ' (K + p.pathIdx path) ∨ ∀ T', Lookup Γ (K + p.pathIdx path) T' →
          ∃ I' ls' k, T' = .const I' ls' ∧ Params.classify I' = some (.indTy k)) →
        ∀ {T}, StrongSound Γ (mkInst ls (r.toVExpr sel K j)) T →
          (∀ {n} {y b : WShape n}, y.T ≤ ms → y.HasType b → LE_Interp ρ' b.T T →
            LE_Interp ρ' y.T (mkInst ls (r.toVExpr sel K j))) ∧
          ((∀ path, r = .var path → m2 path ≤ ρ' (K + p.pathIdx path)) →
            LE_Interp ρ' ms (mkInst ls (r.toVExpr sel K j))) := by
  intro ms r hRHS
  induction hRHS with
  | @bot _ r =>
    refine ⟨List.replicate (r.selfLeaves sel).length (WShape.bot (n := 0)).T, by simp,
      fun i s e h1 _ => ?_, fun j Γb ρ' _ _ _ _ T _ =>
        ⟨fun hy _ _ => .mono hy .bot, fun _ => .bot⟩⟩
    rw [List.getElem?_replicate] at h1; split at h1 <;> cases h1
    exact .inl ⟨0, rfl⟩
  | @const ms e cl hms =>
    by_cases hs : sel e = true
    · obtain ⟨c', us, he, hrk⟩ := hsel e hs
      obtain ⟨s, hsf, hle⟩ := LR.selfFact_exists LIH hR he hrk hms
      have hsl : (Pattern.RHS.fixed (p := p) e cl).selfLeaves sel = [e] := by
        simp [Pattern.RHS.selfLeaves, Pattern.RHS.fixedLeaves, hs]
      have ht : ∀ j, mkInst ls ((Pattern.RHS.fixed (p := p) e cl).toVExpr sel K j) = .bvar j := by
        intro j; simp [Pattern.RHS.toVExpr, hs, mkInst]
      refine ⟨[s], by simp [hsl], fun i s' e' h1 h2 => ?_, fun j Γb ρ' _ hb _ _ T _ => ?_⟩
      · rw [hsl] at h2
        match i, h1, h2 with
        | 0, h1, h2 => cases h1; cases h2; exact hsf
      · have H : LE_Interp ρ' ms (mkInst ls ((Pattern.RHS.fixed (p := p) e cl).toVExpr sel K j)) := by
          rw [ht]; exact .bvar (hle.trans (by simpa using hb 0 s rfl))
        exact ⟨fun hy _ _ => H.mono hy, fun _ => H⟩
    · have hsl : (Pattern.RHS.fixed (p := p) e cl).selfLeaves sel = [] := by
        simp [Pattern.RHS.selfLeaves, Pattern.RHS.fixedLeaves, hs]
      have ht : ∀ j, mkInst ls ((Pattern.RHS.fixed (p := p) e cl).toVExpr sel K j) = mkInst ls e := by
        intro j; simp [Pattern.RHS.toVExpr, hs]
      refine ⟨[], by simp [hsl], fun i s' e' h1 _ => by simp at h1,
        fun j Γb ρ' _ _ _ _ T _ => ?_⟩
      have H : LE_Interp ρ' ms (mkInst ls ((Pattern.RHS.fixed (p := p) e cl).toVExpr sel K j)) := by
        rw [ht]; exact (LE_Interp.closed_iff cl.mkInstS).1 (hR _ _ hms)
      exact ⟨fun hy _ _ => H.mono hy, fun _ => H⟩
  | @var ms path hms =>
    refine ⟨[], by simp [Pattern.RHS.selfLeaves, Pattern.RHS.fixedLeaves],
      fun i s' e' h1 _ => by simp at h1, fun j Γb ρ' W _ hv1 _ T hT => ?_⟩
    have ht : mkInst ls ((Pattern.RHS.var (p := p) path).toVExpr sel K j) =
        .bvar (K + p.pathIdx path) := rfl
    rw [ht] at hT ⊢
    refine ⟨fun {n y b} hy hty hb => ?_, fun hh => .bvar (hms.trans (hh path rfl))⟩
    obtain ⟨-, -, hc, hTeq⟩ := hT
    cases hc with
    | bvar hL => exact .bvar (hv1 path hL (hy.trans hms) hty ((hTeq W).2 hb))
  | @app n f F A ms a _ _ hms ihf iha =>
    obtain ⟨slF, lF, fF, cF⟩ := ihf
    obtain ⟨slA, lA, fA, cA⟩ := iha
    refine ⟨slF ++ slA, by simp [Pattern.RHS.selfLeaves_app, lF, lA], fun i s e h1 h2 => ?_,
      fun j Γb ρ' W hb hv1 hv2 Ty hT => ?_⟩
    · rw [Pattern.RHS.selfLeaves_app] at h2
      by_cases hi : i < slF.length
      · rw [List.getElem?_append_left hi] at h1
        rw [List.getElem?_append_left (lF ▸ hi)] at h2
        exact fF i s e h1 h2
      · rw [List.getElem?_append_right (by omega)] at h1
        rw [List.getElem?_append_right (by omega), ← lF] at h2
        exact fA _ s e h1 h2
    · have ht : mkInst ls ((Pattern.RHS.app F A).toVExpr sel K j) =
          .app (mkInst ls (F.toVExpr sel K j))
            (mkInst ls (A.toVExpr sel K (j + slF.length))) := by
        rw [lF]; rfl
      rw [ht] at hT ⊢
      obtain ⟨-, -, hc, hTeq⟩ := hT
      cases hc with
      | app hA0 hFt hAt =>
      have bF : ∀ i s, slF[i]? = some s → s ≤ ρ' (j + i) := fun i s h =>
        hb i s (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]; exact h)
      have bA : ∀ i s, slA[i]? = some s → s ≤ ρ' (j + slF.length + i) := fun i s h => by
        rw [Nat.add_assoc]
        exact hb _ s (by rw [List.getElem?_append_right (by omega)]; simpa using h)
      have CF := cF j W bF hv1 hv2 hFt
      have CA := cA (j + slF.length) W bA hv1 hv2 hAt
      have GF : LE_Interp ρ' f.T (mkInst ls (F.toVExpr sel K j)) := by
        match F, CF, hFt with
        | .var path, CF, hFt =>
          rcases hv2 path with h | h
          · exact CF.2 fun _ e => by cases e; exact h
          · exfalso
            obtain ⟨-, -, hc', hTeq'⟩ := hFt
            cases hc' with
            | bvar hL =>
              obtain ⟨I', ls', k, rfl, hI⟩ := h _ hL
              exact const_indTy_not_forallE hI ((hTeq' W).2 forallE_bot_interp)
        | .fixed .., CF, _ => exact CF.2 fun _ e => by cases e
        | .app .., CF, _ => exact CF.2 fun _ e => by cases e
      have G : LE_Interp ρ' ms _ := app_collapse (hFt.sound W GF) CA.1 hms
      exact ⟨fun hy _ _ => G.mono hy, fun _ => G⟩

omit [Params] in
theorem onCtx_append_right {P : List VExpr → VExpr → Prop} :
    ∀ (Γ₁ : List VExpr) {Γ₂ : List VExpr}, OnCtx (Γ₁ ++ Γ₂) P → OnCtx Γ₂ P
  | [], _, h => h
  | _ :: Γ₁, _, h => onCtx_append_right Γ₁ h.1

/-- `Params.strong_below` for the whole environment (`Params.henv`). -/
theorem strong_env {U : Nat} {Γ : List VExpr} {e A : VExpr}
    (hΓ : OnCtx Γ (fun Γ A => Params.env.IsType U Γ A))
    (H : Params.env.HasType U Γ e A) (ls : List SLevel) :
    IsDefEqStrong Params.env (Γ.map (mkInst ls)) (mkInst ls e) (mkInst ls e) (mkInst ls A) := by
  obtain ⟨vs, hvs, rfl⟩ := SLevel.exists_map_mk ls
  have hS := (VEnv.IsDefEq.strong Params.henv hΓ H).instL hvs
  have := hS.mkSE (CtorProviderE.synE VEnv.LE.rfl) (onCtx_map_instL_levelWF hvs Γ)
  have hctx : Γ.map (mkInst (vs.map SLevel.mk)) = (Γ.map (VExpr.instL vs)).map SExpr.mk := by
    rw [List.map_map]; congr 1; funext B; exact mkInst_map_mk hvs
  rw [hctx, mkInst_map_mk hvs, mkInst_map_mk hvs]
  exact this

/-- Every bare-constant leaf of a well-typed unabstracted RHS has the right number of levels
(`StrongSoundCore.const`). -/
theorem leaf_levels {Γ : List SExpr} {ls : List SLevel} {p : Pattern} :
    ∀ (r : p.RHS) (j : Nat) {T : SExpr}, StrongSound Γ (mkInst ls (r.toVExpr (fun _ => false) 0 j)) T →
    ∀ {c' : Name} {us : List VLevel} {ci' : VConstant}, VExpr.const c' us ∈ r.fixedLeaves →
      Params.env.constants c' = some ci' → us.length = ci'.uvars
  | .fixed e _, j, T, hT, c', us, ci', hm, hc => by
    simp only [Pattern.RHS.fixedLeaves, List.mem_singleton] at hm; subst hm
    obtain ⟨-, -, hcore, -⟩ := hT
    cases hcore with
    | const h1 h2 => cases h1.symm.trans hc; simpa using h2
  | .var _, _, _, _, _, _, _, hm, _ => by simp [Pattern.RHS.fixedLeaves] at hm
  | .app F A, j, T, hT, c', us, ci', hm, hc => by
    obtain ⟨-, -, hcore, -⟩ := hT
    cases hcore with
    | app _ hF hA =>
      simp only [Pattern.RHS.fixedLeaves, List.mem_append] at hm
      rcases hm with hm | hm
      · exact leaf_levels F j hF hm hc
      · exact leaf_levels A _ hA hm hc

/-- From `pat_defeq`: every bare-constant leaf of the RHS has the right number of levels. -/
theorem pat_leaf_levels {p : Pattern} {r : p.RHS × p.Check} {g : PatGen}
    {ci : VConstant} (hP : Params.Pat p r)
    (hg : Pattern.gen Params.env Params.rank Params.classify p r.1 = some g)
    (hci : Params.env.constants p.head = some ci) (ls : List SLevel) (Γ₀ : List SExpr)
    {c' : Name} {us : List VLevel} {ci' : VConstant} (hm : VExpr.const c' us ∈ r.1.fixedLeaves)
    (hc : Params.env.constants c' = some ci') : us.length = ci'.uvars := by
  have hΓ : OnCtx g.ctx (fun Γ A => Params.env.IsType ci.uvars Γ A) :=
    (onCtx_append_right g.self (Params.pat_typed hP hg hci).1).mono
      (fun h => h.mono (Params.env.below_le ..))
  have H := (strong_env hΓ (Params.pat_defeq hP hg hci).hasType.2 ls).weak_append (Γ₀ := Γ₀)
  have hrhs := (Pattern.gen_eq_some hg).2.2.1
  rw [hrhs] at H
  exact leaf_levels r.1 0 (LE_Interp.strongSoundS H).left hm hc

/-- `LR.rhs_lower` (E6a) with one more conclusion, read off the same `LR.rhs_lower_core` call:
unless the RHS is a variable path not covered by `hhead`'s first disjunct, the RHS shape `mC`
itself is interpreted at `ρ_low`. The proof is E6a's proof of `LR.rhs_lower`, with the second
conjunct of `LR.rhs_lower_core`'s claim kept; `LR.rhs_lower` is read off it. `_hm` (kept from the
pinned statement) is unused. -/
theorem LR.rhs_lower2 {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name}
    {ls : List SLevel} {R : TShape → SExpr → Prop} (LIH : LR.LocalIH Params.rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e)
    {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} {mC : TShape}
    (hP : Params.Pat p r) (hMt : LE_Interp.Matches p c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1)
    (g : PatGen) (hg : Pattern.gen Params.env Params.rank Params.classify p r.1 = some g)
    {fields : List TShape} {ρ : Valuation} {m : Nat} (_hm : g.ctx.length = fields.length + m)
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
  have hhd : p.head = c := LE_Interp.Matches.head hMt
  obtain ⟨⟨ci, hci⟩, hctxlen⟩ := gen_head_ctx hg
  obtain ⟨-, -, -, hAbs⟩ := Pattern.gen_eq_some hg
  have hpt := Params.pat_typed hP hg hci
  have hroot : StrongSound ((g.self ++ g.ctx).map (mkInst ls) ++ Γ₀) (mkInst ls g.rhsAbs)
      (mkInst ls (g.type.liftN g.self.length)) :=
    (LE_Interp.strongSoundS (((Params.strong_below hpt.1 hpt.2 ls).weak_append
      (Γ₀ := Γ₀)).mono (Params.env.below_le ..))).left
  have hsel : ∀ e, Pattern.sameRank Params.rank p.head e = true →
      ∃ c' us, e = .const c' us ∧ Params.rank c' = Params.rank c := fun e h => by
    obtain ⟨c', us, rfl, h'⟩ := Pattern.sameRank_eq_true.1 h; exact ⟨c', us, rfl, hhd ▸ h'⟩
  obtain ⟨sl, hlen, hfacts, hclaim⟩ := LR.rhs_lower_core LIH hR (Pattern.sameRank Params.rank p.head)
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
    refine ⟨c', us, ci', he, hhd ▸ h2, h1, pat_leaf_levels hP hg hci ls Γ₀ hmem h1,
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
      refine fits_foldr_push hfit _ sl (by simp [hK]) fun j A x hA hx => ?_
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
      rw [Nat.zero_add, Valuation.lower, foldr_push_lt _ sl i s h]; exact .rfl
    have hshift : ∀ i, Valuation.lower sl fields ρ m (g.self.length + i) =
        Valuation.lowerCtx fields ρ m i := fun i => by
      rw [← hK]; exact foldr_push_add _ sl i
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
      have hi : p.pathIdx path < g.ctx.length := hctxlen ▸ pathIdx_lt p path
      obtain ⟨B, hB, rfl⟩ := lookup_eq hL
      rw [hΓi _ hi] at hB; cases hB
      rw [hshift]
      refine hvar path hy hty ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
        mkInst_liftN]
      have e1 : g.self.length + p.pathIdx path + 1 = (p.pathIdx path + 1) + sl.length := by omega
      rw [e1, liftK_add] at hbT
      exact (LE_Interp_foldr_push_liftK sl).1 hbT
    have hv2 : ∀ path, m2 path ≤ (Valuation.lower sl fields ρ m) (g.self.length + p.pathIdx path) ∨
        ∀ T', Lookup ((g.self ++ g.ctx).map (mkInst ls) ++ Γ₀) (g.self.length + p.pathIdx path) T' →
          ∃ I' ls' k, T' = .const I' ls' ∧ Params.classify I' = some (.indTy k) := by
      intro path
      rcases hhead path with h | ⟨I', us, k, hc, hI⟩
      · exact .inl (by rw [hshift]; exact h)
      · refine .inr fun T' hL => ?_
        have hi : p.pathIdx path < g.ctx.length := hctxlen ▸ pathIdx_lt p path
        obtain ⟨B, hB, rfl⟩ := lookup_eq hL
        rw [hΓi _ hi] at hB; cases hB
        rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hc
        rw [hc]
        exact ⟨I', _, k, liftK_const .., hI⟩
    have C := hclaim 0 W hb hv1 hv2 (hAbs ▸ hroot)
    refine ⟨fun hy hty ha => ?_, fun hv => ?_⟩
    · rw [hAbs]; exact C.1 hy hty ha
    · rw [hAbs]; exact C.2 fun path h => by rw [hshift]; exact hv path h

/-- E6a (PLAN D4 step 2), proved: the self entries of `W_p` and `LE_Interp ρ_low y' rhsAbs`
for every typed `y'` below the RHS shape whose type interprets `g.type`. Statement changes from
`historical/RhsLowerStmt.lean:208-234` (section header): `gen`/`idx`/`rank` instantiated, `hR`,
`hhead`, and the self clause's `⊥`-or-`R`-witness disjunct (with the occurrence named and the level
count unconditional). The first three conjuncts of `LR.rhs_lower2`. -/
theorem LR.rhs_lower {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name}
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
      ∀ {n'} {y' a' : WShape n'}, y'.T ≤ mC → y'.HasType a' →
        LE_Interp (Valuation.lower selfs fields ρ m) a'.T
          (SExpr.mkInst ls (g.type.liftN g.self.length)) →
        LE_Interp (Valuation.lower selfs fields ρ m) y'.T (SExpr.mkInst ls g.rhsAbs) :=
  let ⟨selfs, h1, h2, h3, _⟩ := LR.rhs_lower2 LIH hR hP hMt hRHS g hg hm hfit hvar hhead
  ⟨selfs, h1, h2, h3⟩

/-! ### The pattern leaf (PLAN D4, E6/R10)

Experiment E6 (attempt a), landed by R10: `LR.pat_leaf_1a`. By `Params.pat_simple` the pattern is
a delta rule `.const c` (`LR.pat_leaf_delta`) or an iota rule `rec x₁ … xₘ (c' z₁ … zₖ)`
(`LR.pat_leaf_iota`). Both go through `LR.rhs_core` (D4 steps 1-4: push the self entries of
`LR.rhs_lower2` onto the pattern-context part of `W_p`, interpret the RHS shape at `ρ_low`, take a
typed pair above it by soundness, apply the WF IH to the RHS typing, rewrite by
`Pattern.gen_rhsAbs`) and `LR.finish` (D4 steps 5-6: typed head reductions of both sides to the
RHS instances, `LogRel.whr`, `conv`, `LR.defEq_transfer`). The iota leaf needs two facts about the
rule, `pat_leaf_gap`, from the `Params` fields `rec_major_indTy` and `rhs_not_field`.

Helpers: valuation/substitution plumbing (`LR.substWF_val`, `range_foldr_self`); the weak typing of
the identity telescope application (`spine_bvars_typed`, for `openSpine`); the ctor-spine bound
(`ctor_spine_le`: interpretations of `c' Z₁ … Zₖ` for a ctor `c'` of arity `k` lie below
`ctor' c' rs` for argument shapes `rs` interpreting the `Zᵢ`); `LR.defEq_transfer` (the core of
`LR.Adequate.mono_r`) and `LR.substWF_push` (iterated `LR.Adequate.cons` for closed types); the
lowered field shape `lowF`; the iota data (`hhead_supply`, `gen_lhs_matches`). -/

/-! #### Helpers -/

theorem LR.substWF_len {Γ₀ Γ : List SExpr} {σ σ' ρ} (W : LR.SubstWF Γ₀ σ σ' Γ ρ) :
    Γ₀.length ≤ Γ.length := by
  induction W with
  | id => exact Nat.le_refl _
  | cons _ _ _ _ _ _ ih => simp only [List.length_cons]; omega

/-- A `SubstWF` over `Δ ++ Γ₀` holds `nil` beyond `Δ`. -/
theorem LR.substWF_val {Γ₀ Γ : List SExpr} {σ σ' ρ} (W : LR.SubstWF Γ₀ σ σ' Γ ρ) :
    ∀ Δ : List SExpr, Γ = Δ ++ Γ₀ → ∀ i, ρ (Δ.length + i) = Valuation.nil i := by
  induction W with
  | id => intro Δ h i; have := congrArg List.length h; simp at this; subst this; rfl
  | @cons σ σ' Γ ρ A a x u W' _ _ _ _ _ ih =>
    intro Δ h i
    match Δ, h with
    | [], h =>
      have := LR.substWF_len W'; simp at h; subst h; simp at this; omega
    | A' :: Δ', h =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [List.length_cons, Nat.add_right_comm]; exact ih Δ' rfl i

theorem range_foldr_push (f : Valuation) : ∀ (m j : Nat),
    ((List.range m).foldr (fun i ρ' => Valuation.push ρ' (f i)) Valuation.nil) j =
      if j < m then f j else Valuation.nil j
  | 0, j => by simp
  | m+1, j => by
    rw [List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
    cases j with
    | zero => simp [Valuation.push]
    | succ j =>
      simp only [Valuation.push]
      rw [range_foldr_push (fun i => f (i+1)) m j]
      by_cases h : j < m
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]; rfl

theorem range_foldr_self {m : Nat} {v : Valuation} (hv : ∀ i, v (m + i) = Valuation.nil i) :
    (List.range m).foldr (fun i ρ' => Valuation.push ρ' (v i)) Valuation.nil = v := by
  funext j
  refine (range_foldr_push v m j).trans ?_
  split
  · rfl
  · rename_i h
    have := hv (j - m); rw [Nat.add_sub_cancel' (by omega)] at this
    rw [this]; rfl

theorem lift_inst_bvar0 (R : SExpr) :
    (R.lift' (Lift.skip Lift.refl).cons).inst (.bvar 0) = R := by
  rw [SExpr.inst, subst_lift']
  conv => rhs; rw [← subst_id (e := R)]
  congr 1; funext i; cases i <;> rfl

theorem liftK_app (F X : SExpr) : ∀ k, liftK (.app F X) k = .app (liftK F k) (liftK X k)
  | 0 => rfl
  | k+1 => by simp only [liftK, liftK_app F X k]; rfl

theorem liftK_bvar (i : Nat) : ∀ k, liftK (.bvar i) k = .bvar (i + k)
  | 0 => rfl
  | k+1 => by simp only [liftK, liftK_bvar i k]; rfl

/-- The identity telescope application is typed (`openSpine`'s typing, in the weak judgment). -/
theorem spine_bvars_typed : ∀ (Ts : List SExpr) {Γ : List SExpr} {F B : SExpr},
    Γ ⊢ F : Ts.foldr .forallE B →
    Ts.reverse ++ Γ ⊢ spine (liftK F Ts.length) ((List.range Ts.length).reverse.map .bvar) : B
  | [], Γ, F, B, H => H
  | T₀ :: Ts, Γ, F, B, H => by
    have H1 := H.weak' (Ctx.Lift'.one (A := T₀))
    simp only [List.foldr_cons, SExpr.lift'] at H1
    have H2 := IsDefEq.appDF H1 (IsDefEq.bvar (Lookup.zero (ty := T₀) (Γ := Γ)))
    rw [lift_inst_bvar0] at H2
    have H3 := spine_bvars_typed Ts H2
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [liftK_app, liftK_lift, liftK_bvar, Nat.zero_add] at H3
    rw [List.length_cons, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, spine_cons]
    exact H3


/-- `lam'` of a graph with all outputs `⊥` is `⊥`. -/
theorem lam'_eq_bot {f : WShapeFun n} (h : ∀ x y, (x, y) ∈ f → y = .bot) :
    WShape.lam' f = .bot := by
  unfold WShape.lam'
  rw [dif_neg]
  rintro ⟨⟨x, y⟩, hm, hy⟩
  have hwf := f.2.2 _ hm
  have := h ⟨x, hwf.1⟩ ⟨y, hwf.2⟩ hm
  exact hy (by rw [show y = (WShape.bot (n := n)).1 from congrArg (·.1) this]; exact Shape.bot_le)

/-- A ctor-classified constant's `Const` derivation beyond its arity is `⊥`. -/
theorem const_beyond {c : Name} {k : Nat} (hc : Params.classify c = some (.ctor k))
    {ls : List SLevel} {R : TShape → SExpr → Prop} {n : Nat} {rargs : List (WShape n)} {m : TShape}
    (H : LE_Interp.Const c ls R rargs m) (hk : k < rargs.length) : m ≤ TShape.bot := by
  induction H with
  | bot => exact TShape.bot_eqv.1
  | @lam f rargs m h1 h2 ih =>
    rw [lam'_eq_bot fun x y h => TShape.le_bot.1 (ih x y h (by simp; omega))] at h2
    exact h2.trans TShape.bot_eqv.1
  | ctor h1 _ => cases hc.symm.trans h1; omega
  | indTy h1 _ => cases hc.symm.trans h1
  | pat hP hM _ =>
    obtain ⟨_, h⟩ := Params.Pat.head_symb hP
    rw [LE_Interp.Matches.head hM, hc] at h; cases h



theorem le_bot_T {f : WShape n} (h : f.T ≤ TShape.bot) : f = .bot := TShape.le_bot.1 h

/-- Interpretations of a partial spine headed by a ctor-classified constant come from a `Const`
derivation over argument shapes interpreting the arguments (`Ys` = the arguments, last first). -/
theorem ctor_spine_bound {ρ : Valuation} {c : Name} {k : Nat}
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
      · left; rw [le_bot_T hb, WShape.bot_app] at hle; exact hle.trans TShape.bot_eqv.1
      have hlenr : rargs.length = Ys.length := List.Forall₂.length_eq hF
      cases hC with
      | bot =>
        left; rw [le_bot_T (hfm.trans TShape.bot_eqv.1), WShape.bot_app] at hle
        exact hle.trans TShape.bot_eqv.1
      | ctor h1 _ => cases hc.symm.trans h1; omega
      | indTy h1 _ => cases hc.symm.trans h1
      | pat hP hM _ =>
        obtain ⟨_, h⟩ := Params.Pat.head_symb hP
        rw [LE_Interp.Matches.head hM, hc] at h; cases h
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
theorem ctor_spine_le {ρ : Valuation} {c : Name} {k : Nat}
    (hc : Params.classify c = some (.ctor k)) {ls : List SLevel} {Zs : List SExpr}
    (hlen : Zs.length = k) {s : TShape} (H : LE_Interp ρ s (spine (.const c ls) Zs)) :
    s ≤ TShape.bot ∨ ∃ (n : Nat) (rs : List (WShape n)), s ≤ (WShape.ctor' c rs).T ∧
      List.Forall₂ (fun r Z => LE_Interp ρ r.T Z) rs Zs := by
  rw [← List.reverse_reverse Zs] at H
  rcases ctor_spine_bound hc Zs.reverse (by simp [hlen]) H with hb | ⟨n, rargs, m', hsm, hC, hF⟩
  · exact .inl hb
  have hlenr : rargs.length = k := by have := List.Forall₂.length_eq hF; simp at this; omega
  cases hC with
  | bot => exact .inl (hsm.trans TShape.bot_eqv.1)
  | @lam f₂ _ _ hpairs hle₂ =>
    left
    rw [lam'_eq_bot fun x y h => TShape.le_bot.1 (const_beyond hc (hpairs x y h)
      (by simp; omega))] at hle₂
    exact (hsm.trans hle₂).trans TShape.bot_eqv.1
  | ctor _ h2 =>
    refine .inr ⟨n, rargs.reverse, hsm.trans h2, ?_⟩
    rw [← List.reverse_reverse Zs]; exact List.Forall₂.reverse.2 hF
  | indTy h1 _ => cases hc.symm.trans h1
  | pat hP hM _ =>
    obtain ⟨_, h⟩ := Params.Pat.head_symb hP
    rw [LE_Interp.Matches.head hM, hc] at h; cases h

/-- `ctor'` is monotone across levels. -/
theorem ctor'_le_T {c : Name} {n n' : Nat} {rs : List (WShape n)} {ls : List (WShape n')}
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
theorem LR.defEq_transfer {Γ₀ : List SExpr} {M N A : SExpr}
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
theorem LR.substWF_push {Γ₀ Δ : List SExpr} {σ σ' : Subst} {ρ : Valuation} {K k : Nat}
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
    have W' := LR.substWF_push WFIH hK W es fun j e' h => by
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

/-! #### The shared RHS part -/

theorem foldr_cons_lt {α : Type} (f : α → SExpr) (σ : Subst) :
    ∀ (xs : List α) (j : Nat) (x : α), xs[j]? = some x →
      (xs.foldr (fun e τ => τ.cons (f e)) σ) j = f x
  | [], _, _, h => by simp at h
  | y :: xs, 0, x, h => by simp at h; subst h; rfl
  | y :: xs, j+1, x, h => foldr_cons_lt f σ xs j x (by simpa using h)

theorem foldr_cons_add {α : Type} (f : α → SExpr) (σ : Subst) :
    ∀ (xs : List α) (i : Nat), (xs.foldr (fun e τ => τ.cons (f e)) σ) (xs.length + i) = σ i
  | [], i => by simp
  | y :: xs, i => by
    rw [List.length_cons, Nat.add_right_comm]; exact foldr_cons_add f σ xs i

theorem liftK_subst_foldr {α : Type} (f : α → SExpr) (σ : Subst) (e : SExpr) :
    ∀ (xs : List α), (liftK e xs.length).subst (xs.foldr (fun e τ => τ.cons (f e)) σ) = e.subst σ
  | [] => rfl
  | y :: xs => by
    rw [List.length_cons, liftK, List.foldr_cons, lift_subst_cons]
    exact liftK_subst_foldr f σ e xs


theorem le_of_eq' {a b : TShape} (h : a = b) : a ≤ b := h ▸ .rfl

/-- The shared RHS part of the pattern leaf (D4 steps 1-4): given the pattern-context part `Wc`
of `W_p` (over `lowerCtx`), push the self entries (`LR.rhs_lower2`'s `selfs`), interpret the RHS
shape at `ρ_low`, take a typed pair `(y, b)` above it by soundness, and apply the WF IH to the
RHS typing (`EnvStrongR.rhs`); rewrite with (c) `gen_rhsAbs`. -/
theorem LR.rhs_core {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
    (WFIH : LR.WFIH Params.rank Γ₀ k) {c : Name} {ci : VConstant} {ls : List SLevel}
    (hc : Params.rank c < k) (h1 : Params.env.constants c = some ci)
    {R : TShape → SExpr → Prop} (LIH : LR.LocalIH Params.rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e)
    {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} {mC : TShape}
    (hP : Params.Pat p r) (hMt : LE_Interp.Matches p c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1)
    (g : PatGen) (hg : Pattern.gen Params.env Params.rank Params.classify p r.1 = some g)
    {fields : List TShape} {ρ : Valuation} {mm : Nat} (hm : g.ctx.length = fields.length + mm)
    {σc σc' : Subst}
    (Wc : LR.SubstWF Γ₀ σc σc' (g.ctx.map (mkInst ls) ++ Γ₀) (Valuation.lowerCtx fields ρ mm))
    (hvar : ∀ path {n} {y b : WShape n}, y.T ≤ m2 path → y.HasType b →
      LE_Interp (Valuation.lowerCtx fields ρ mm) b.T
        (SExpr.mkInst ls ((g.ctx.getD (p.pathIdx path) (.sort .zero)).liftN (p.pathIdx path + 1))) →
      y.T ≤ Valuation.lowerCtx fields ρ mm (p.pathIdx path))
    (hhead : ∀ path, m2 path ≤ Valuation.lowerCtx fields ρ mm (p.pathIdx path) ∨
      ∃ (I' : Name) (us : List VLevel) (k : Nat), g.ctx[p.pathIdx path]? = some (.const I' us) ∧
        Params.classify I' = some (.indTy k))
    {s : TShape}
    (hroot : (s ≤ mC ∧
        ∀ path, r.1 = .var path → m2 path ≤ Valuation.lowerCtx fields ρ mm (p.pathIdx path)) ∨
      ∃ path, r.1 = .var path ∧ s ≤ Valuation.lowerCtx fields ρ mm (p.pathIdx path)) :
    ∃ (n' : Nat) (y b : WShape n'), s ≤ y.T ∧ y.HasType b ∧
      LE_Interp (Valuation.lowerCtx fields ρ mm) b.T (mkInst ls g.type) ∧
      (LR Γ₀).DefEq (r.1.applyS ls fun path => σc (p.pathIdx path))
        (r.1.applyS ls fun path => σc' (p.pathIdx path)) ((mkInst ls g.type).subst σc) y b := by
  have hhd : p.head = c := LE_Interp.Matches.head hMt
  have h1' : Params.env.constants p.head = some ci := hhd ▸ h1
  obtain ⟨selfs, hslen, hfacts, -, hroot'⟩ :=
    LR.rhs_lower2 LIH hR hP hMt hRHS g hg hm Wc.fits hvar hhead
  have hgs := Pattern.gen_self hg
  obtain ⟨es, hes_def⟩ : ∃ es : List (SExpr × SExpr × SExpr × TShape), es =
      ((g.self.zip (r.1.selfLeaves (Pattern.sameRank Params.rank p.head))).zip selfs).map
        fun x => (mkInst ls x.1.1, mkInst ls x.1.2, mkInst ls x.1.2, x.2) := ⟨_, rfl⟩
  have hes : ∀ (j : Nat) (e : SExpr × SExpr × SExpr × TShape), es[j]? = some e →
      ∃ (S el : VExpr) (s : TShape), g.self[j]? = some S ∧
      (r.1.selfLeaves (Pattern.sameRank Params.rank p.head))[j]? = some el ∧ selfs[j]? = some s ∧
      e = (mkInst ls S, mkInst ls el, mkInst ls el, s) := by
    intro j e he
    simp only [hes_def, List.getElem?_map, List.getElem?_zip_eq_some, Option.map_eq_some_iff] at he
    obtain ⟨⟨⟨S, el⟩, s⟩, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ := he
    exact ⟨S, el, s, h1, h2, h3, rfl⟩
  have hesl : es.length = g.self.length := by
    simp only [hes_def, List.length_map, List.length_zip, hslen, ← hgs.1, Nat.min_self]
  have hes1 : es.map (·.1) = g.self.map (mkInst ls) := by
    apply List.ext_getElem (by simp [hesl])
    intro j hj1 hj2
    simp only [List.getElem_map]
    have hj : j < es.length := by simpa using hj1
    obtain ⟨S, el, s, h1, -, -, he⟩ := hes j (es[j]'hj) (List.getElem?_eq_getElem hj)
    rw [he]; dsimp only
    rw [List.getElem?_eq_getElem (by simpa using hj2)] at h1
    cases h1; rfl
  have hes4 : es.map (·.2.2.2) = selfs := by
    apply List.ext_getElem (by simp [hesl, hslen])
    intro j hj1 hj2
    simp only [List.getElem_map]
    have hj : j < es.length := by simpa using hj1
    obtain ⟨S, el, s, -, -, h3, he⟩ := hes j (es[j]'hj) (List.getElem?_eq_getElem hj)
    rw [he]; dsimp only
    rw [List.getElem?_eq_getElem hj2] at h3
    cases h3; rfl
  -- the self entries satisfy `LR.substWF_push`'s conditions
  have hcond : ∀ (j : Nat) (e : SExpr × SExpr × SExpr × TShape), es[j]? = some e → e.1.ClosedN ∧
      (∃ u, IsDefEqStrong (Params.env.below Params.rank (Params.rank c))
        ((es.drop (j+1)).map (·.1) ++ (g.ctx.map (mkInst ls) ++ Γ₀)) e.1 e.1 (.sort u)) ∧
      ∃ (n : Nat) (a₁ q : WShape n), e.2.2.2 = q.T ∧ q.HasType a₁ ∧ LE_Interp .nil a₁.T e.1 ∧
        Γ₀ ⊢ e.2.1 ≡ e.2.2.1 : e.1 ∧ (LR Γ₀).DefEq e.2.1 e.2.2.1 e.1 q a₁ := by
    intro j e he
    obtain ⟨S, el, s, hS, hel, hs, rfl⟩ := hes j e he
    obtain ⟨c', us, ci', hel', -, hci', hlen', hty, ⟨kk, x, b, rfl, hxb, hb⟩, hcg, -⟩ :=
      hfacts j s hs
    cases hel.symm.trans hel'
    have hgetD : g.self.getD j (.sort .zero) = S := by simp [List.getD_eq_getElem?_getD, hS]
    rw [hgetD] at hty
    dsimp only
    have hcl : (mkInst ls S).ClosedN := hty ▸ (Params.henv.closedC hci').mkInstS
    refine ⟨hcl, ?_, ?_⟩
    · have hj : j < g.self.length := (List.getElem?_eq_some_iff.1 hS).1
      obtain ⟨u, Hu⟩ := EnvStrongR.of_params.ctx ls hP hg h1' j S
        (by rw [List.getElem?_append_left hj]; exact hS)
      refine ⟨u, ?_⟩
      have hctx : ((g.self ++ g.ctx).drop (j + 1)).map (mkInst ls) ++ Γ₀ =
          (es.drop (j+1)).map (·.1) ++ (g.ctx.map (mkInst ls) ++ Γ₀) := by
        rw [List.drop_append_of_le_length (by omega), List.map_drop, hes1]
        simp [List.map_drop]
      rw [← hctx, ← hhd]; exact Hu.weak_append
    · refine ⟨kk, b, x, rfl, hxb, ?_, ?_, ?_⟩
      · rw [hty]; exact (LE_Interp.closed_iff (Params.henv.closedC hci').mkInstS).1 hb
      · rw [hty]
        exact IsDefEq.const hci' (by simpa using hlen')
      · rw [hty]
        rcases hcg with ⟨n0, he0⟩ | ⟨n0, m', a', hle, -, -, H⟩
        · obtain ⟨rfl, hx⟩ := Sigma.mk.inj he0
          cases eq_of_heq hx
          exact (LR Γ₀).bot hxb.isType
        · exact H x b hle (by simpa using hb) hxb
  have Wp := LR.substWF_push WFIH hc Wc es hcond
  rw [← List.append_assoc, hes1, ← List.map_append] at Wp
  rw [show es.foldr (fun e ρ' => Valuation.push ρ' e.2.2.2) (Valuation.lowerCtx fields ρ mm) =
      Valuation.lower selfs fields ρ mm by
    rw [Valuation.lower, ← hes4, List.foldr_map]] at Wp
  -- the RHS shape is interpreted at ρ_low; soundness gives a typed pair above it
  have hrootI : LE_Interp (Valuation.lower selfs fields ρ mm) s (mkInst ls g.rhsAbs) := by
    rcases hroot with ⟨hs, hr⟩ | ⟨path, hr, hs⟩
    · exact (hroot' hr).mono hs
    · rw [(Pattern.gen_eq_some hg).2.2.2, hr]
      refine .bvar (hs.trans (le_of_eq' ?_))
      rw [Valuation.lower, ← hslen]; exact (foldr_push_add _ selfs _).symm
  have Hr := (EnvStrongR.of_params.rhs ls hP hg h1').weak_append (Γ₀ := Γ₀)
  rw [hhd] at Hr
  obtain ⟨n', y, b, -, hle, hy, hb, hyb⟩ :=
    ((LE_Interp.soundSE (Params.env.below_le ..) Hr Wp.fits).2 hrootI).out
  have Ad := WFIH _ hc Hr hy hb hyb
  have D := (Ad.1 Wp).1
  -- rewrite with (c) `gen_rhsAbs` and the self/lift bookkeeping
  have hself : ∀ (σ0 : Subst) (j : Nat) (e : VExpr),
      (r.1.selfLeaves (Pattern.sameRank Params.rank p.head))[j]? = some e →
      (es.foldr (fun e τ => τ.cons e.2.1) σ0) j = mkInst ls e := by
    intro σ0 j e he
    have hj : j < es.length := by
      rw [hesl, hgs.1]; exact (List.getElem?_eq_some_iff.1 he).1
    obtain ⟨S, el, s, -, hel, -, hesj⟩ := hes j es[j] (List.getElem?_eq_getElem hj)
    rw [foldr_cons_lt (·.2.1) σ0 es j es[j] (List.getElem?_eq_getElem hj), hesj]
    cases hel.symm.trans he; rfl
  have hself' : ∀ (σ0 : Subst) (j : Nat) (e : VExpr),
      (r.1.selfLeaves (Pattern.sameRank Params.rank p.head))[j]? = some e →
      (es.foldr (fun e τ => τ.cons e.2.2.1) σ0) j = mkInst ls e := by
    intro σ0 j e he
    have hj : j < es.length := by
      rw [hesl, hgs.1]; exact (List.getElem?_eq_some_iff.1 he).1
    obtain ⟨S, el, s, -, hel, -, hesj⟩ := hes j es[j] (List.getElem?_eq_getElem hj)
    rw [foldr_cons_lt (·.2.2.1) σ0 es j es[j] (List.getElem?_eq_getElem hj), hesj]
    cases hel.symm.trans he; rfl
  rw [Pattern.gen_rhsAbs hg ls (fun path => σc (p.pathIdx path)) _ (hself σc) (fun path => by
      rw [← hesl]; exact foldr_cons_add (·.2.1) σc es _),
    Pattern.gen_rhsAbs hg ls (fun path => σc' (p.pathIdx path)) _ (hself' σc') (fun path => by
      rw [← hesl]; exact foldr_cons_add (·.2.2.1) σc' es _),
    mkInst_liftN, ← hesl, liftK_subst_foldr] at D
  refine ⟨n', y, b, hle, hyb, ?_, D⟩
  rw [mkInst_liftN, ← hslen] at hb
  exact (LE_Interp_foldr_push_liftK selfs).1 hb

/-! #### The delta leaf, and the pieces of the iota leaf -/

/-- `strong_env` for a defeq (`pat_defeq`'s open equation, instantiated at `ls`). -/
theorem strong_env_defeq {U : Nat} {Γ : List VExpr} {e₁ e₂ A : VExpr}
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
theorem pat_defeq_inst {p : Pattern} {r : p.RHS × p.Check} {g : PatGen} {ci : VConstant}
    (hP : Params.Pat p r) (hg : Pattern.gen Params.env Params.rank Params.classify p r.1 = some g)
    (hci : Params.env.constants p.head = some ci) (ls : List SLevel) (Γ₀ : List SExpr) :
    IsDefEqStrong Params.env (g.ctx.map (mkInst ls) ++ Γ₀) (mkInst ls g.lhs) (mkInst ls g.rhs)
      (mkInst ls g.type) := by
  have hΓ : OnCtx g.ctx (fun Γ A => Params.env.IsType ci.uvars Γ A) :=
    (onCtx_append_right g.self (Params.pat_typed hP hg hci).1).mono
      (fun h => h.mono (Params.env.below_le ..))
  exact (strong_env_defeq hΓ (Params.pat_defeq hP hg hci) ls).weak_append

/-- The last step of the pattern leaf: from the RHS instance's `DefEq` at a typed pair `(y, b)`
above `m`, with `b` compatible with `a`, and typed head reductions of both sides to the RHS
instances, the goal at `(m, a)` (`LogRel.whr`, `conv`, `LR.defEq_transfer`). -/
theorem LR.finish {Γ₀ : List SExpr} {L L' Rs Rs' A A₁ : SExpr} {n n' : Nat}
    {m a : WShape n} {y b : WShape n'}
    (hL : TWHRedS Γ₀ L Rs A) (hL' : TWHRedS Γ₀ L' Rs' A)
    (D : (LR Γ₀).DefEq Rs Rs' A₁ y b) (hconv : (LR Γ₀).TyDefEq A₁ A b)
    (tyA : (LR Γ₀).TyDefEq A A a)
    (hle : m.T ≤ y.T) (hmem : m.HasType a) (hyb : y.HasType b) (hc : a.T.Compat b.T) :
    (LR Γ₀).DefEq L L' A m a :=
  ((LR Γ₀).whr hL hL').2 <| LR.defEq_transfer hle hmem hyb hc tyA
    ((LR Γ₀).left_ty ((LR Γ₀).symm_ty hconv)) ((LR Γ₀).conv hconv D)



/-- Type validity of a constant's (closed) type at every typed shape interpreting it
(`LR.const_local`'s `tyV`). -/
theorem LR.tyV_const {Γ₀ : List SExpr} {k : Nat} (WFIH : LR.WFIH Params.rank Γ₀ k)
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
theorem LR.pat_leaf_delta {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
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
  have hhd : c = c₀ := (LE_Interp.Matches.head hMt).symm
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
    have := LR.substWF_val W [] rfl i
    simp only [List.length_nil, Nat.zero_add] at this
    rw [this]; rfl
  have Wc : LR.SubstWF Γ₀ σ σ' (g.ctx.map (mkInst ls) ++ Γ₀) (Valuation.lowerCtx [] ρ 0) := by
    rw [hctx, List.map_nil, List.nil_append, ← hρ]; exact W
  obtain ⟨n₁, y, b, hle, hyb, hb, D⟩ := LR.rhs_core WFIH hc h1 LIH hR (rargs := ([] : List (WShape n))) hP .const hRHS g hg
    (by rw [hctx]; rfl) Wc (fun path => path.elim) (fun path => path.elim)
    (.inl ⟨le, fun path => path.elim⟩)
  rw [htype, hcl.subst_eq .zero] at D
  rw [htype] at hb
  have hb' : LE_Interp ρ b.T (mkInst ls ci.type) := (LE_Interp.closed_iff hcl).1 hb
  -- the typed reduction `c ls ⤳ rhs`
  have Hd := pat_defeq_inst hP hg h1 ls Γ₀
  rw [hctx, hlhs, htype] at Hd
  simp only [List.map_nil, List.nil_append] at Hd
  have hlhs' : mkInst ls (VExpr.const c (VLevel.params ci.uvars)) = .const c ls := by
    simp only [mkInst, SLevel.instV_params h2]
  rw [hlhs'] at Hd
  have hcl0 : (mkInst ls g.rhs).ClosedN := by
    have := (pat_defeq_inst hP hg h1 ls []).closedN.2.1
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
  have tyb := LR.tyV_const WFIH W.wf₀ hc h1 ls ((LE_Interp.closed_iff hcl).1 hb') hyb.isType
  have tya := LR.tyV_const WFIH W.wf₀ hc h1 ls ((LE_Interp.closed_iff hcl).1 hA) hmem.isType
  exact LR.finish hred hred D tyb tya hle hmem hyb (hA.compat hb')


theorem mkInst_subst (ls : List SLevel) : ∀ (e : VExpr) (σ : VExpr.Subst),
    mkInst ls (e.subst σ) = (mkInst ls e).subst (fun i => mkInst ls (σ i))
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .app f a, σ => by simp only [VExpr.subst, mkInst, SExpr.subst, mkInst_subst ls f, mkInst_subst ls a]
  | .lam A e, σ | .forallE A e, σ => by
    simp only [VExpr.subst, mkInst, SExpr.subst, mkInst_subst ls A, mkInst_subst ls e]
    congr 2; funext i; cases i with
    | zero => rfl
    | succ i =>
      simp only [VExpr.Subst.lift, SExpr.Subst.lift, VExpr.lift_eq_lift', mkInst_lift']

/-- (d) at the `SExpr` level: the generic type is the body under the substitution sending the
major to the generic ctor spine. -/
theorem type_subst (ls : List SLevel) (Bmaj : VExpr) (c' : Name) (us : List VLevel) (k : Nat) :
    mkInst ls ((Bmaj.liftN k 1).inst (VExpr.bvarSpine (.const c' us) k 0)) =
      (mkInst ls Bmaj).subst (Subst.cons (fun i => .bvar (i + k))
        (openSpine c' (us.map (SLevel.instV ls)) k)) := by
  rw [VExpr.inst_eq, VExpr.liftN_subst, mkInst_subst]
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

theorem hasType_ctor_inv {c : Name} {l : List (WShape n)} {h} {a : WShape (n+1)}
    (H : (WShape.ctor c l h).HasType a) : a = .indTy := by
  cases a using WShape.casesOn' <;> first
    | rfl
    | (exfalso; revert H; simp [WShape.HasType, Shape.HasType, Shape.hasType, WShape.ctor,
        WShape.bot, WShape.sort, WShape.forallE, WShape.lam])

theorem ctor'_eq_ctor {c : Name} {k : Nat} (hc : Params.classify c = some (.ctor k))
    (l : List (WShape n)) : ∃ h, WShape.ctor' c l = WShape.ctor c l h := by
  have hs : IsStruct c = false := by simp [IsStruct, hc]
  have h : IsStruct c → WShape.ListNonZero l := fun h' => by rw [hs] at h'; cases h'
  exact ⟨h, by rw [WShape.ctor', dif_pos h]⟩

omit [Params] in
theorem forall₂_get {α β : Type} {Rl : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ Rl as bs →
      ∀ (j : Nat) (a : α) (b : β), as[j]? = some a → bs[j]? = some b → Rl a b
  | _, _, .nil, _, _, _, h, _ => by simp at h
  | _, _, .cons h0 _, 0, _, _, ha, hb => by simp at ha hb; subst ha hb; exact h0
  | _, _, .cons _ h1, j+1, a, b, ha, hb => forall₂_get h1 j a b (by simpa using ha) (by simpa using hb)

omit [Params] in
theorem forall₂_of_get {α β : Type} {Rl : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, as.length = bs.length →
      (∀ (j : Nat) (a : α) (b : β), as[j]? = some a → bs[j]? = some b → Rl a b) →
      List.Forall₂ Rl as bs
  | [], [], _, _ => .nil
  | a :: as, b :: bs, hl, H => .cons (H 0 a b rfl rfl)
      (forall₂_of_get (by simpa using hl) fun j a' b' h1 h2 =>
        H (j+1) a' b' (by simpa using h1) (by simpa using h2))
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

theorem fieldsEq_get {Γ : List SExpr} {n : Nat} {IH : LogRel Γ n} :
    ∀ {Ts Xs Ys : List SExpr} {l : List (WShape n)}, LRS.FieldsEq IH Ts Xs Ys l →
      Xs.length = Ts.length ∧ Ys.length = Ts.length ∧ l.length = Ts.length ∧
      ∀ (i : Nat) (A : SExpr), Ts[i]? = some A → ∃ X Y q, Xs[i]? = some X ∧ Ys[i]? = some Y ∧
        l[i]? = some q ∧ Γ ⊢ X ≡ Y : A ∧ LRS.FieldRel IH X Y A q
  | _, _, _, _, .nil => ⟨rfl, rfl, rfl, fun _ _ h => by simp at h⟩
  | _, _, _, _, .cons hxy hrel H => by
    obtain ⟨l1, l2, l3, ih⟩ := fieldsEq_get H
    refine ⟨by simp [l1], by simp [l2], by simp [l3], fun i A hA => ?_⟩
    cases i with
    | zero => simp at hA; subst hA; exact ⟨_, _, _, rfl, rfl, rfl, hxy, hrel⟩
    | succ i => simpa using ih i A (by simpa using hA)

/-- A type-typed shape below a `lam'` shape is `⊥`. -/
theorem typeShape_le_lam' {m' : TShape} {r : Bool} {f : WShapeFun n}
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

theorem indTy_T_le {n m : Nat} : (WShape.indTy (n := n)).T ≤ (WShape.indTy (n := m)).T := by
  rw [TShape.LE.def (Nat.succ_le_succ (Nat.le_max_left n m)) (Nat.succ_le_succ (Nat.le_max_right n m))]
  simp only [WShape.T, WShape.lift_indTy]; exact WShape.LE.rfl

/-- An inductive-type constant is interpreted below `indTy`. -/
theorem indTy_interp_le {ρ : Valuation} {I : Name} {ls : List SLevel} {j : Nat}
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
    | lam _ hle => exact h3.trans ((typeShape_le_lam' hm' hle).trans TShape.bot_le)
    | ctor h _ => cases hI.symm.trans h
    | indTy _ hle => exact h3.trans (hle.trans indTy_T_le)
    | pat hP hM _ =>
      obtain ⟨_, h⟩ := Params.Pat.head_symb hP
      rw [LE_Interp.Matches.head hM, hI] at h; cases h


/-- The lowered field shape (PLAN D4 step 1, E6a): the major's field shape `q` when it is typed
at `indTy` and `indTy` interprets the field type `A`, else `⊥` (a Prop-valued field type, or an
untyped field shape). -/
noncomputable def lowF (N : Nat) (A : SExpr) (q : WShape (N+1)) : TShape :=
  @ite _ (LE_Interp .nil (WShape.indTy (n := N)).T A ∧ q.HasType .indTy)
    (Classical.propDecidable _) q.T TShape.bot

theorem lowF_le {N : Nat} {A : SExpr} {q : WShape (N+1)} : lowF N A q ≤ q.T := by
  unfold lowF; split
  · exact .rfl
  · exact TShape.bot_le

/-- A lowered field entry is a typed `SubstWF` entry (`LR.substWF_push`'s condition). -/
theorem LR.lowF_entry {Γ₀ : List SExpr} {N : Nat} {A X Y : SExpr} {q : WShape (N+1)}
    (hxy : Γ₀ ⊢ X ≡ Y : A) (hrel : LRS.FieldRel (LR Γ₀ (n := N+1)) X Y A q) :
    ∃ (n : Nat) (a₁ q' : WShape n), lowF N A q = q'.T ∧ q'.HasType a₁ ∧
      LE_Interp .nil a₁.T A ∧ Γ₀ ⊢ X ≡ Y : A ∧ (LR Γ₀).DefEq X Y A q' a₁ := by
  unfold lowF; split
  · next h => exact ⟨N+1, .indTy, q, rfl, h.2, h.1, hxy, hrel q .rfl h.2⟩
  · exact ⟨0, .bot, .bot, rfl, rfl, .bot, hxy, (LR Γ₀).bot rfl⟩

/-- `hvar` at a constructor-field path: a typed shape below the raw field shape whose type
interprets the (inductive-constant) field type lies below the lowered entry. -/
theorem hvar_field {N n : Nat} {A : SExpr}
    (hA : ∃ (I : Name) (vs : List SLevel) (j : Nat), A = .const I vs ∧
      Params.classify I = some (.indTy j))
    {q : WShape (N+1)} {y b : WShape n} (hyq : y.T ≤ q.T) (hyb : y.HasType b) {ρ' : Valuation}
    (hb : LE_Interp ρ' b.T A) : y.T ≤ lowF N A q := by
  obtain ⟨I, vs, j, rfl, hI⟩ := hA
  have hb' := indTy_interp_le hI hb
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
        ((LE_Interp.closed_iff (M := .const I vs) trivial).1 hb).mono indTy_T_le
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
      unfold lowF; rw [if_pos ⟨hP1, hP2⟩]; exact hyq

/-! #### Iota-leaf data (ported from `docs/const-case/plan/E6a/HheadSupply.lean`, `RankParams` → the
`Params` fields) -/

theorem matches_varN {h c : Name} : ∀ (j : Nat) {n : Nat} {rs : List (WShape n)}
    {mf : (Pattern.varN (.const h) j).Path → TShape},
    LE_Interp.Matches (Pattern.varN (.const h) j) c rs mf →
    rs.length = j ∧ ∀ x, ∃ s, rs[(Pattern.varN (.const h) j).pathIdx x]? = some s ∧ mf x = s.T
  | 0, n, rs, mf, H => by
    cases H with
    | const => exact ⟨rfl, fun x => x.elim⟩
  | j+1, n, rs, mf, H => by
    cases H with
    | @var _ _ _ rs' mf' a H' =>
      obtain ⟨hl, hx⟩ := matches_varN j H'
      refine ⟨by simp [hl], fun x => ?_⟩
      cases x with
      | none => exact ⟨a, rfl, rfl⟩
      | some y =>
        obtain ⟨s, hs, he⟩ := hx y
        refine ⟨s, ?_, he⟩
        change (a :: rs')[(Pattern.varN (.const h) j).pathIdx y + 1]? = some s
        simpa using hs

theorem ofRargs_get {n : Nat} : ∀ {rs : List (WShape n)} {i : Nat} {s : WShape n},
    rs[i]? = some s → Valuation.ofRargs rs i = s.T
  | _ :: _, 0, _, h => by cases h; rfl
  | _ :: rs, i+1, _, h => ofRargs_get (rs := rs) (i := i) (by simpa using h)

theorem range'_foldr (ρ : Valuation) : ∀ (m s i : Nat), i < m →
    ((List.range' s m).foldr (fun i ρ' => ρ'.push (ρ (i + 1))) Valuation.nil) i = ρ (s + i + 1)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | m+1, s, 0, _ => by simp [List.range'_succ, Valuation.push]
  | m+1, s, i+1, h => by
    rw [List.range'_succ, List.foldr_cons]
    change ((List.range' (s+1) m).foldr (fun i ρ' => Valuation.push ρ' (ρ (i + 1))) Valuation.nil) i = _
    rw [range'_foldr ρ m (s+1) i (by omega)]; congr 1; omega

theorem lowerCtx_rec (fields : List TShape) (ρ : Valuation) (m i : Nat) (hi : i < m) :
    Valuation.lowerCtx fields ρ m (fields.length + i) = ρ (i + 1) := by
  rw [Valuation.lowerCtx, foldr_push_add, List.range_eq_range']
  rw [range'_foldr ρ m 0 i hi]; congr 1; omega

omit [Params] in
theorem foldr_forallE_inj' : ∀ {Ts Ts' : List VExpr} {X Y : VExpr},
    (∀ A B, X ≠ .forallE A B) → (∀ A B, Y ≠ .forallE A B) →
    Ts.foldr .forallE X = Ts'.foldr .forallE Y → Ts = Ts'
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, hX, _, h => absurd h (hX _ _)
  | _ :: _, [], _, _, _, hY, h => absurd h.symm (hY _ _)
  | _ :: _, _ :: _, _, _, hX, hY, h => by
    simp only [List.foldr_cons, VExpr.forallE.injEq] at h
    rw [h.1, foldr_forallE_inj' hX hY h.2]

omit [Params] in
theorem foldr_app_ne_forallE (I : Name) (ls : List VLevel) : ∀ (args : List VExpr) A B,
    args.foldr (fun (A acc : VExpr) => acc.app A) (.const I ls) ≠ .forallE A B
  | [], _, _, h => by cases h
  | _ :: _, _, _, h => by cases h

/-- `hhead`, from the iota leaf's data only (`HheadSupply.lean: V.hhead_supply`). -/
theorem hhead_supply {rec c' : Name} {mm k : Nat}
    {r : (Pattern.iota rec mm c' k).RHS} {g : PatGen}
    (hg : Pattern.gen Params.env Params.rank Params.classify (.iota rec mm c' k) r = some g)
    {n : Nat} {rargs : List (WShape n)} {m2 : (Pattern.iota rec mm c' k).Path → TShape}
    (hMt : LE_Interp.Matches (.iota rec mm c' k) rec rargs m2)
    {ρ : Valuation} (hρ : (Valuation.ofRargs rargs).LE ρ)
    {fields : List TShape} (hm : g.ctx.length = fields.length + mm) :
    ∀ path, m2 path ≤ Valuation.lowerCtx fields ρ mm ((Pattern.iota rec mm c' k).pathIdx path) ∨
      ∃ (I' : Name) (us : List VLevel) (k' : Nat),
        g.ctx[(Pattern.iota rec mm c' k).pathIdx path]? = some (.const I' us) ∧
        Params.classify I' = some (.indTy k') := by
  obtain ⟨⟨ci, hci⟩, -⟩ := gen_head_ctx hg
  obtain ⟨Hs, I, us, Bmaj, hHs, -, ci', I', Ts, args, hci', hcl, hTs, -, e3, hctx⟩ :=
    Pattern.gen_head_ctor hg (by rw [← Pattern.head_varN rec mm]; exact hci)
  have hfl : fields.length = k := by
    rw [hctx] at hm; simp [hHs, hTs] at hm; omega
  intro path
  cases hMt with
  | app hf ha =>
    obtain ⟨lf, hxf⟩ := matches_varN mm hf
    obtain ⟨la, hxa⟩ := matches_varN k ha
    cases path with
    | inl x =>
      left
      obtain ⟨s, hs, he⟩ := hxf x
      have hi : (Pattern.varN (.const rec) mm).pathIdx x < mm :=
        lf ▸ (List.getElem?_eq_some_iff.1 hs).1
      simp only [Sum.elim_inl, Pattern.pathIdx_inl, Pattern.nvars_varN, Pattern.nvars]
      rw [he, Nat.zero_add, show (Pattern.varN (.const rec) mm).pathIdx x + k =
        fields.length + (Pattern.varN (.const rec) mm).pathIdx x by omega,
        lowerCtx_rec _ _ _ _ hi]
      have := hρ ((Pattern.varN (.const rec) mm).pathIdx x + 1)
      rwa [Valuation.ofRargs, List.foldr_cons, Valuation.push, ← Valuation.ofRargs,
        ofRargs_get hs] at this
    | inr x =>
      right
      obtain ⟨s, hs, -⟩ := hxa x
      have hi : (Pattern.varN (.const c') k).pathIdx x < k :=
        la ▸ (List.getElem?_eq_some_iff.1 hs).1
      obtain ⟨I'', Ts', e4, hall⟩ := Params.ctor_fields_closed (cl := .ctor k) rfl hcl hci'
      have hT : Ts = Ts' := foldr_forallE_inj' (foldr_app_ne_forallE _ _ args)
        (fun _ _ h => by cases h) (e3.symm.trans e4)
      subst hT
      simp only [Pattern.pathIdx_inr]
      rw [hctx, List.getElem?_append_left (by simp [hTs]; exact hi)]
      have hi' : (Pattern.varN (.const c') k).pathIdx x < Ts.length := hTs ▸ hi
      rw [List.getElem?_reverse (by simpa using hi'), List.getElem?_map]
      have hlt : Ts.length - 1 - (Pattern.varN (.const c') k).pathIdx x < Ts.length := by omega
      rw [List.getElem?_eq_getElem (by simpa using hlt)]
      obtain ⟨J, vs, hJ, hcJ⟩ := hall _ (List.getElem_mem (by simpa using hlt))
      refine ⟨J, vs.map (·.inst us), 0, ?_, hcJ⟩
      simp [hJ, VExpr.instL]

/-- `foldr .forallE` injectivity at equal telescope lengths (`SExpr` form). -/
theorem foldr_forallE_inj : ∀ {Hs Hs' : List SExpr} {B B' : SExpr}, Hs.length = Hs'.length →
    Hs.foldr .forallE B = Hs'.foldr .forallE B' → Hs = Hs' ∧ B = B'
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | A :: Hs, A' :: Hs', _, _, hl, h => by
    simp only [List.foldr_cons, SExpr.forallE.injEq] at h
    obtain ⟨h1, h2⟩ := foldr_forallE_inj (by simpa using hl) h.2
    exact ⟨by rw [h.1, h1], h2⟩

/-! #### Matching the generated left-hand side (ported from `docs/const-case/plan/E3/Measure7-b.lean`,
`genIdx` → `pathIdx`) -/

omit [Params] in
theorem range_reverse_succ (k : Nat) :
    (List.range (k+1)).reverse = ((List.range k).reverse.map (· + 1)) ++ [0] := by
  rw [List.range_succ_eq_map, List.reverse_cons, List.map_reverse]

/-- `varN (const c) k` matches the open spine instance `c τ(k-1) … τ 0` with
`m2 = τ ∘ pathIdx` (Measure7-b's `MatchesS.varN_genIdx`, with the repo's `pathIdx`). -/
theorem matchesS_varN_pathIdx {c : Name} {ls : List SLevel} :
    ∀ (k : Nat) (τ : Subst),
      (Pattern.varN (.const c) k).MatchesS (spine (.const c ls) ((List.range k).reverse.map τ)) ls
        (fun path => τ ((Pattern.varN (.const c) k).pathIdx path))
  | 0, τ => Pattern.MatchesS.congr .const nofun
  | k+1, τ => by
    rw [range_reverse_succ, List.map_append, List.map_map, List.map_singleton, spine_snoc]
    have := (matchesS_varN_pathIdx (c := c) (ls := ls) k (fun i => τ (i + 1))).var (a' := τ 0)
    refine this.congr fun path => ?_
    cases path <;> rfl

/-- (b') The instantiated LHS matches the pattern with `m2 = σ ∘ pathIdx`. -/
theorem gen_lhs_matches {rec c' : Name} {m n : Nat}
    {r : (Pattern.iota rec m c' n).RHS} {g : PatGen}
    (hg : Pattern.gen Params.env Params.rank Params.classify (.iota rec m c' n) r = some g)
    {ci : VConstant} (h1 : Params.env.constants rec = some ci)
    {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr} (hHs : Hs.length = m)
    (hT : ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj))
    {ls : List SLevel} (hls : ls.length = ci.uvars) (σ : Subst) :
    (Pattern.iota rec m c' n).MatchesS ((mkInst ls g.lhs).subst σ) ls
      (fun path => σ ((Pattern.iota rec m c' n).pathIdx path)) := by
  rw [Pattern.gen_lhs_subst hg h1 hHs hT hls σ]
  refine ((matchesS_varN_pathIdx m (fun i => σ (n + i))).app
    (matchesS_varN_pathIdx (ls := us.map (SLevel.instV ls)) n σ)).congr fun path => ?_
  cases path with
  | inl x => simp [Pattern.nvars_varN, Pattern.nvars, Nat.add_comm]
  | inr x => rfl

omit [Params] in
theorem varN_var (p : Pattern) : ∀ n, (Pattern.var p).varN n = (p.varN n).var
  | 0 => rfl
  | n+1 => by simp only [Pattern.varN, varN_var p n]

/-- A `varN` pattern matches any spine of the right length. -/
theorem matchesS_spine {q : Pattern} {h : SExpr} {ls}
    {g : q.Path → SExpr} (H : q.MatchesS h ls g) : ∀ xs : List SExpr,
      ∃ g', (q.varN xs.length).MatchesS (SExpr.spine h xs) ls g'
  | [] => ⟨g, H⟩
  | x :: xs => by
    have ⟨g', h'⟩ := matchesS_spine (q := q.var) (H.var (a' := x)) xs
    revert g' h'; rw [varN_var]
    exact fun g' h' => ⟨g', h'⟩

/-- The last binder type of a strong telescope is typed in the whole telescope. -/
theorem telStrong_last {E : VEnv} : ∀ {Γ Ts : List SExpr} {B : SExpr}, TelStrongE E Γ Ts B →
    ∃ v, IsDefEqStrong E (Ts.reverse ++ Γ) B B (.sort v)
  | _, [], _, .nil h => ⟨_, h⟩
  | _, _ :: _, _, .cons _ H => by
    obtain ⟨v, h⟩ := telStrong_last H
    exact ⟨v, by simpa using h⟩


/-- A shape compatible with `indTy` is below it. -/
theorem le_indTy_of_compat {N : Nat} {a : TShape} (hc : a.Compat (WShape.indTy (n := N)).T) :
    a ≤ (WShape.indTy (n := N)).T := by
  obtain ⟨z, h1, h2⟩ := TShape.Compat.def'.1 hc
  obtain ⟨nz, w⟩ := z
  rw [TShape.LE.def (Nat.le_max_left (N+1) nz) (Nat.le_max_right (N+1) nz)] at h2
  simp only [WShape.T] at h2
  obtain ⟨K, hK⟩ : ∃ K, max (N+1) nz = K + 1 := ⟨max (N+1) nz - 1, by omega⟩
  rw [hK, WShape.lift_indTy] at h2
  have hw := WShape.indTy_le.1 h2
  have := h1.trans (TShape.lift_eqv (a := ⟨nz, w⟩) (Nat.le_max_right (N+1) nz)).2
  dsimp only at this
  rw [hK, hw] at this
  exact this.trans indTy_T_le

/-- `indTy` interprets a non-Prop inductive-type constant. -/
theorem indTy_interp_const {ρ : Valuation} {I₀ : Name} {lv : List SLevel} {ciI : VConstant}
    {u : VLevel} (hI : Params.classify I₀ = some (.indTy 0))
    (hci : Params.env.constants I₀ = some ciI) (hlen : lv.length = ciI.uvars)
    (hty : ciI.type = .sort u) (hu : SLevel.instV lv u ≠ .zero) {N : Nat} :
    LE_Interp ρ (WShape.indTy (n := N)).T (.const I₀ lv) := by
  refine .const (R := fun _ _ => False) (m' := (WShape.indTy (n := N)).T)
    (a := (WShape.type (n := N+1)).T) hci hlen .rfl (WShape.HasType.T .indTy) ?_
    (LE_Interp.Const.indTy (n := N) (rargs := []) hI indTy_T_le) (fun _ _ h => h.elim)
  rw [hty]
  refine .sort ?_
  simp only [ne_eq, hu, not_false_eq_true, decide_true]
  exact TShape.sort_eqv.1

/-! #### The iota leaf -/

/-- The pattern leaf for an iota rule `rec x₁ … xₘ (c' z₁ … zₖ)` (PLAN D4 "RHS step"), given the
two facts `hgapI`/`hgapF` of `pat_leaf_gap`. Steps, as in the proof: I1 the iota data
(`gen_head_ctor`, `ctor_fields_closed`, `hT`); I2 invert `W` at the major; I3 the major's ctor
clause (lifted to a level with field level ≥ 1; `hgapI` makes the major domain a whnf, so the
clause's levels are the pattern's); I4 the lowered field entries and `Wc` (`LR.substWF_push` over
`W`'s tail); I5 `hvar`/`hhead`; I6a (d) and the type transfer to `ρ` (`ctor_spine_le`); I6 the RHS
root is interpreted at `ρ_low` (at a bare non-Prop field root through `le_indTy_of_compat`;
`hgapF`); I7 `LR.rhs_core`; I8 type validity of `B` from the WF IH; I9 `σ` with the major
replaced; I10 typed head reductions (`WHRedS.major`, `WHRed.extra'`, `pat_defeq` through
`IsDefEq.subst`) and `LR.finish`. -/
theorem LR.pat_leaf_iota {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
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
    -- the two missing facts (E6's gap; see `pat_leaf_gap`)
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
    have := LE_Interp.Matches.head hMt
    simp only [Pattern.head, Pattern.head_varN] at this; exact this.symm
  subst hhd
  have hMt0 := hMt
  have hρ0 := hρ
  cases hMt with
  | app hmf hma => ?_
  rename_i n₀ rs_rec c'' rs' mf ma
  have hc'' : c' = c'' := by
    have := LE_Interp.Matches.head hma; rw [Pattern.head_varN] at this; exact this
  subst hc''
  obtain ⟨lf, hxf⟩ := matches_varN mm hmf
  obtain ⟨la, hxa⟩ := matches_varN kf hma
  obtain ⟨Hs, I, us, Bmaj, hHs, hcty, ci', I', Tsc, args, hci', hcl', hTsc, hI', hcity, hctx⟩ :=
    Pattern.gen_head_ctor hg h1
  obtain ⟨I'', Ts', hcity', hall⟩ := Params.ctor_fields_closed (cl := .ctor kf) rfl hcl' hci'
  have hTT : Tsc = Ts' := foldr_forallE_inj' (foldr_app_ne_forallE _ _ args)
    (fun _ _ h => by cases h) (hcity.symm.trans hcity')
  subst hTT
  have hlenTs : Ts.length = mm + 1 := by simp [lf] at hk; omega
  have hT' : mkInst ls ci.type = (Hs.map (mkInst ls) ++ [SExpr.const I (us.map (SLevel.instV ls))]).foldr
      .forallE (mkInst ls Bmaj) := by
    rw [hcty, mkInst_foldr_forallE, List.foldr_append]; rfl
  obtain ⟨rfl, rfl⟩ := foldr_forallE_inj (by simp [hHs, hlenTs]) (hT.symm.trans hT')
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
  obtain ⟨hstr, hctoreq⟩ := ctor'_eq_ctor hcl' (rs'.reverse.map (WShape.lift (N+1)))
  have hle₀ : (WShape.ctor' c' (rs'.reverse.map (WShape.lift (N+1)))) ≤ x₀.2.lift (N+2) := by
    have := (TShape.LE.def (Nat.succ_le_succ hNn) (Nat.le_refl (N+2))).1
      (hraw.trans (TShape.lift_eqv hNx).2)
    rwa [WShape.lift_ctor' hNn, WShape.lift_self] at this
  rw [hctoreq] at hle₀
  obtain ⟨l', h', hm₀, hl'⟩ := WShape.ctor_le.1 hle₀
  rw [hm₀] at hma₀ D₀
  have ha₀ := hasType_ctor_inv hma₀
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
  obtain ⟨hXl, hYl, hll, hFget⟩ := fieldsEq_get hF
  simp only [List.length_map, hTsc] at hXl hYl hll
  obtain ⟨es, hes⟩ : ∃ es : List (SExpr × SExpr × SExpr × TShape),
      es = (((Tsc.map (mkInst (us.map (SLevel.instV ls)))).zip (Xs.zip (Ys.zip l'))).map
        fun x => (x.1, x.2.1, x.2.2.1, lowF N x.1 x.2.2.2)).reverse := ⟨_, rfl⟩
  have heslen : es.length = kf := by
    simp [hes, List.length_zip, hTsc, hXl, hYl, hll]
  have hesget : ∀ (j : Nat) (e : SExpr × SExpr × SExpr × TShape), es[j]? = some e →
      ∃ i, i + j + 1 = kf ∧
        (Tsc.map (mkInst (us.map (SLevel.instV ls))))[i]? = some e.1 ∧ Xs[i]? = some e.2.1 ∧
        Ys[i]? = some e.2.2.1 ∧ ∃ q, l'[i]? = some q ∧ e.2.2.2 = lowF N e.1 q := by
    intro j e he
    have hj : j < kf := heslen ▸ (List.getElem?_eq_some_iff.1 he).1
    refine ⟨kf - 1 - j, by omega, ?_⟩
    have hlz : j + (kf - 1 - j) + 1 = (((Tsc.map (mkInst (us.map (SLevel.instV ls)))).zip
        (Xs.zip (Ys.zip l'))).map fun x => (x.1, x.2.1, x.2.2.1, lowF N x.1 x.2.2.2)).length := by
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
      exact LR.lowF_entry hxy hrel
  have Wc0 := LR.substWF_push WFIH hc Wt es hcondF
  obtain ⟨fields, hfields⟩ : ∃ fields : List TShape, fields = es.map (·.2.2.2) := ⟨_, rfl⟩
  have hflen : fields.length = kf := by rw [hfields, List.length_map, heslen]
  have hρt : (List.range mm).foldr (fun i ρ' => Valuation.push ρ' ((ρt.push x₀) (i+1)))
      Valuation.nil = ρt := by
    refine range_foldr_self (v := ρt) fun i => ?_
    have := LR.substWF_val Wt (Hs.map (mkInst ls)).reverse rfl i
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
    rw [hσc, ← heslen]; exact foldr_cons_add (·.2.1) σ.tail es i
  have hσc'_add : ∀ i, σc' (kf + i) = σ' (i + 1) := fun i => by
    rw [hσc', ← heslen]; exact foldr_cons_add (·.2.2.1) σ'.tail es i
  have hσc_X : (List.range kf).reverse.map σc = Xs := by
    apply List.ext_getElem (by simp [hXl])
    intro j h1 h2
    have hj : j < kf := by simpa using h1
    have hje : (kf - 1 - j) < es.length := by omega
    obtain ⟨i, hij, -, hX, -, -⟩ := hesget (kf - 1 - j) es[kf - 1 - j] (List.getElem?_eq_getElem hje)
    have hi : i = j := by omega
    subst hi
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]
    rw [hσc, foldr_cons_lt (·.2.1) σ.tail es _ es[kf - 1 - i] (List.getElem?_eq_getElem hje)]
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
    rw [hσc', foldr_cons_lt (·.2.2.1) σ'.tail es _ es[kf - 1 - i] (List.getElem?_eq_getElem hje)]
    rw [List.getElem?_eq_getElem h2] at hY
    exact (Option.some.inj hY).symm
  -- I5: `hroot`, `hvar`, `hhead` for `LR.rhs_core`
  have hinl : ∀ x, Sum.elim mf ma (Sum.inl x) ≤ Valuation.lowerCtx fields (ρt.push x₀) mm
      ((Pattern.iota c mm c' kf).pathIdx (Sum.inl x)) := by
    intro x
    obtain ⟨s, hs, he⟩ := hxf x
    have hi : (Pattern.varN (.const c) mm).pathIdx x < mm :=
      lf ▸ (List.getElem?_eq_some_iff.1 hs).1
    simp only [Sum.elim_inl, Pattern.pathIdx_inl, Pattern.nvars_varN, Pattern.nvars]
    rw [he, Nat.zero_add, show (Pattern.varN (.const c) mm).pathIdx x + kf =
      fields.length + (Pattern.varN (.const c) mm).pathIdx x by omega,
      lowerCtx_rec _ _ _ _ hi]
    have := hρ ((Pattern.varN (.const c) mm).pathIdx x + 1)
    rwa [Valuation.ofRargs, List.foldr_cons, Valuation.push, ← Valuation.ofRargs,
      ofRargs_get hs] at this
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
      rw [Valuation.lowerCtx, foldr_push_lt _ _ _ _ hfi, hlow]
      obtain ⟨I₀, vs, hAc, hI₀⟩ := hTsf i₀ _ hA
      -- the context type at the path is the field type
      have hgt : mkInst ls ((g.ctx.getD ((Pattern.varN (.const c') kf).pathIdx x) (.sort .zero)).liftN
          ((Pattern.varN (.const c') kf).pathIdx x + 1)) =
          es[(Pattern.varN (.const c') kf).pathIdx x].1 := by
        rw [mkInst_liftN]
        have hj : (Pattern.varN (.const c') kf).pathIdx x < g.ctx.length := by
          rw [hctx]; simp [hTsc]; omega
        have hgm : (g.ctx.map (mkInst ls))[(Pattern.varN (.const c') kf).pathIdx x]? =
            some es[(Pattern.varN (.const c') kf).pathIdx x].1 := by
          rw [hctx', List.getElem?_append_left (by simp [hTsc]; omega),
            List.getElem?_reverse' (j := i₀) (by simp [hTsc]; omega)]
          exact hA
        rw [List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some] at hgm
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some,
          Option.some.inj hgm, hAc, liftK_const]
      rw [hgt] at hb
      refine hvar_field ⟨I₀, vs, 0, hAc, hI₀⟩ (hy.trans ?_) hyb hb
      have hrs : (rs'.reverse.map (WShape.lift (N+1)))[i₀]? = some (s.lift (N+1)) := by
        rw [List.getElem?_map, List.getElem?_reverse' (j := (Pattern.varN (.const c') kf).pathIdx x)
          (by rw [la]; omega), hs]; rfl
      exact (TShape.lift_eqv hNn).2.trans (WShape.LE.T (forall₂_get hl' i₀ _ _ hrs hq))
  have hhead := hhead_supply hg hMt0 hρ0 hm
  -- I6a: the types: (d) and the type transfer to `ρ`
  have hgty := Pattern.gen_type hg h1 hHs hcty
  have hτ₀ := type_subst ls Bmaj c' us kf
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
      rcases ctor_spine_le hcl' (by simp) h0' with hb0 | ⟨nr, rs, hsr, hF2⟩
      · exact hb0.trans TShape.bot_le
      refine hsr.trans ?_
      have hrsl : rs.length = kf := by have := List.Forall₂.length_eq hF2; simpa using this
      have hrs : List.Forall₂ (fun r q => r.T ≤ q.T) rs l' := by
        refine forall₂_of_get (by rw [hrsl, hl'len]) fun j r q hr hq => ?_
        have hj : j < kf := hrsl ▸ (List.getElem?_eq_some_iff.1 hr).1
        have hZ : ((List.range kf).reverse.map SExpr.bvar)[j]? = some (.bvar (kf - 1 - j)) := by
          rw [List.getElem?_map, List.getElem?_reverse (by simpa using hj)]
          simp [List.getElem?_range (by omega : kf - 1 - j < kf)]
        have hrZ := forall₂_get hF2 j r _ hr hZ
        rw [LE_Interp.bvar_iff] at hrZ
        have hje : kf - 1 - j < es.length := by omega
        obtain ⟨i₀, hi₀, -, -, -, q', hq', hlow⟩ := hesget _ _ (List.getElem?_eq_getElem hje)
        have hi : i₀ = j := by omega
        subst hi
        cases hq.symm.trans hq'
        have hfi : fields[kf - 1 - i₀]? = some es[kf - 1 - i₀].2.2.2 := by
          rw [hfields, List.getElem?_map, List.getElem?_eq_getElem hje]; rfl
        rw [Valuation.lowerCtx, foldr_push_lt _ _ _ _ hfi, hlow] at hrZ
        exact hrZ.trans lowF_le
      refine (ctor'_le_T hrs).trans ?_
      rw [show WShape.ctor' c' l' = WShape.ctor c' l' h' from WShape.ctor_eq_ctor'.symm, ← hm₀]
      exact (TShape.lift_eqv hNx).1
    | succ i =>
      have hi' := hσ'' (i+1)
      simp only [Subst.cons, LE_Interp.bvar_iff] at hi'
      have heq : Valuation.lowerCtx fields (ρt.push x₀) mm (i + kf) = (ρt.push x₀) (i + 1) := by
        rw [Valuation.lowerCtx, show i + kf = fields.length + i by omega, foldr_push_add, hρt]
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
    rw [Valuation.lowerCtx, foldr_push_lt _ _ _ _ hfi, hlow]
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
      hmC.trans ((TShape.lift_eqv hNn).2.trans (WShape.LE.T (forall₂_get hl' i₀ _ _ hrs hq)))
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
      indTy_interp_const hI₀ hciI hlenI htyI hu₀
    -- the rule's type at the field root is the field type (`SoundEq` of the RHS typing)
    have ssR := (LE_Interp.strongSoundS (pat_defeq_inst hP hg h1' ls Γ₀).hasType.2).left
    rw [(Pattern.gen_eq_some hg).2.2.1, hx] at ssR
    simp only [Pattern.RHS.toVExpr, mkInst, Nat.zero_add, Pattern.pathIdx_inr] at ssR
    obtain ⟨-, -, hcoreR, hTeqR⟩ := ssR
    cases hcoreR with
    | bvar hL =>
    obtain ⟨B₀, hB₀, rfl⟩ := lookup_eq hL
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_map, hgctx, Option.map_some,
      Option.some.injEq] at hB₀
    subst hB₀
    have hgt : LE_Interp (Valuation.lowerCtx fields (ρt.push x₀) mm) (WShape.indTy (n := N)).T
        (mkInst ls g.type) := by
      refine (hTeqR Wc.fits).1 ?_
      simp only [mkInst, liftK_const]
      exact (LE_Interp.closed_iff (M := SExpr.const _ _) trivial).1 hP1
    have haI := le_indTy_of_compat (hA.compat (htrans hgt))
    have hbT : LE_Interp .nil a.T es[(Pattern.varN (.const c') kf).pathIdx x].1 := by
      rw [← hgm]; exact hP1.mono haI
    obtain ⟨I₁, vs₁, hTc, hI₁⟩ := hTsf i₀ _ hA'
    exact hvar_field ⟨I₁, vs₁, 0, hTc, hI₁⟩ hmq hmem hbT
  -- I7: the RHS part (`LR.rhs_core`)
  obtain ⟨n₁, y, b, hle, hyb, hb, D⟩ :=
    LR.rhs_core WFIH hc h1 LIH hR hP hMt0 hRHS g hg hm Wc hvar hhead hrootArg
  rw [htyσ] at D
  have hbB := htrans hb
  -- I8: type validity of `B` from the WF IH (`EnvStrongR.const`, `telescope`)
  have hctxT : (Hs.map (mkInst ls) ++ [SExpr.const I (us.map (SLevel.instV ls))]).reverse ++ Γ₀ =
      SExpr.const I (us.map (SLevel.instV ls)) :: ((Hs.map (mkInst ls)).reverse ++ Γ₀) := by
    simp only [List.reverse_append, List.reverse_singleton, List.cons_append, List.nil_append]
  obtain ⟨u₁, HB0⟩ := EnvStrongR.of_params.const ls h1
  rw [hT'] at HB0
  obtain ⟨v₁, HB1⟩ := telStrong_last (IsDefEqStrong.telescope HB0)
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
  have Hos := spine_bvars_typed _ Hc
  rw [liftK_const, hlenTs] at Hos
  change _ ⊢ openSpine c ls (mm+1) : _ at Hos
  have hLdec : ∀ σ₀ : Subst, (openSpine c ls (mm+1)).subst σ₀ =
      .app (spine (.const c ls) ((List.range mm).reverse.map fun i => σ₀ (i+1))) (σ₀ 0) := by
    intro σ₀
    rw [openSpine_subst, range_reverse_succ, List.map_append, List.map_map, List.map_singleton,
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
    have hsp := matchesS_spine (Pattern.MatchesS.const (c := c) (ls := ls))
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
    exact WHRed.extra' hP (gen_lhs_matches hg h1 hHs hcty h2 σc₀) (by rw [hchk]; exact nofun)
  have hE2 := IsDefEq.subst W.wf₀ Wc.left.toSubstEq (pat_defeq_inst hP hg h1' ls Γ₀).defeq
  rw [Pattern.gen_rhs hg ls _ σc (fun _ => rfl), htyσ, ← hlhsEq σ σc Xs hσc_add hσc_X, ← hτ] at hE2
  have hE2' := IsDefEq.subst W.wf₀ Wc.symm.left.toSubstEq (pat_defeq_inst hP hg h1' ls Γ₀).defeq
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
  exact LR.finish hL hL' D (tyB hbB hyb.isType Wτσ) (tyV W.left) hle hmem hyb
    (hA.compat hbB)

/-! #### The leaf -/

/-- The two facts about an iota rule `rec x₁ … xₘ (c' z₁ … zₖ)` that the iota leaf
(`LR.pat_leaf_iota`) takes as `hgapI`/`hgapF` (found by experiment E6, independently by both
attempts), from the `Params` fields `rec_major_indTy` and `rhs_not_field`.

1. The head `I` of the recursor's major domain `const I us` (`gen_head`) is not a `symb`, so that
   `const I ls'` is a whnf: it is an inductive type (`rec_major_indTy`). The major's ctor clause
   (`LRS.CtorDefEq`) only gives `TyRedS Γ₀ (const I ls') (const I₂ ls₂)` with the constructor
   spine at `ls₂`; without a whnf domain nothing ties `ls₂` to the pattern's ctor levels
   `ls' = us.map (instV ls)`, and both the instance `rec … (c'.{ls'} Xs)` of `pat_defeq`'s open
   equation and the field entries of `W_p` (typed at `Fᵢ` at `ls'`, whereas `FieldsEq` types the
   fields at `ls₂`) need `ls₂ = ls'`.
2. If the RHS is a bare constructor-field variable, that field's type is never a `Prop`: vacuous,
   since the RHS is never a bare field (`rhs_not_field`). (The goal's type shape `a` interprets `B`
   at `ρ`, whose major entry is a ctor shape with possibly untyped field shapes (D1,
   `UntypedField.lean`); `W_p` lowers them, and a Prop-valued field to `⊥`. At a bare field root
   the RHS shape is the raw field shape. For a non-Prop field type `LR.pat_leaf_iota` handles it
   (`le_indTy_of_compat`, via the type transfer); for a Prop field type `[[const I']] = {⊥}` and
   excluding a non-`⊥` element shape there would need sort/type uniqueness.)

Neither fact can be supplied by `LR.const_spine`: both are properties of the rule, not of the
`Const` derivation. -/
theorem pat_leaf_gap {c c' : Name} {mm kf : Nat}
    {r : (Pattern.iota c mm c' kf).RHS × (Pattern.iota c mm c' kf).Check}
    (hP : Params.Pat (.iota c mm c' kf) r) {ci : VConstant}
    (h1 : Params.env.constants c = some ci) (g : PatGen) :
    (∀ {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr},
      ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj) → Hs.length = mm →
      ∀ j, Params.classify I ≠ some (.symb j)) ∧
    (∀ x, r.1 = .var (.inr x) → ∀ (I₀ : Name) (vs : List VLevel) (ciI : VConstant) (u : VLevel),
      g.ctx[(Pattern.iota c mm c' kf).pathIdx (.inr x)]? = some (.const I₀ vs) →
      Params.env.constants I₀ = some ciI → ciI.type = .sort u → ∀ ns, (u.inst vs).eval ns ≠ 0) := by
  refine ⟨fun hty hlen j hj => ?_, fun x hx => absurd hx (Params.rhs_not_field hP x)⟩
  obtain ⟨k, hk⟩ := Params.rec_major_indTy hP h1 hty hlen
  cases hk.symm.trans hj

/-- The pattern leaf (the E6 interface; R9 calls it at `Const.pat`), `PatLeafStmt2.lean:168` with
the real `Pattern.gen`, the repo's `IsDefEqStrong E`, and E6a's `hR`. Proved (experiment E6,
landed by R10). By `Params.pat_simple` the pattern is a delta rule `.const c`, done directly
(`LR.pat_leaf_delta`: the pattern context is empty, so `W` is `W_p`'s context part, then
`LR.rhs_core` and `LR.finish`), or an iota rule `rec x₁ … xₘ (c' z₁ … zₖ)` (`LR.pat_leaf_iota`),
done by PLAN D4's six "RHS step" steps through the lowering lemma (`LR.rhs_lower2`): (1) `W_p` from
`W`'s tail, the major's lowered fields (from its ctor clause) and the self entries; (2) the RHS
shape is interpreted at `ρ_low`; (3) the WF IH at `rank c` on `pat_typed`'s RHS typing
(`LR.rhs_core`); (4) the rewrite by `Pattern.gen_rhsAbs`; (5) typed head reductions of both sides
to the RHS instances (`WHRedS.major`, `WHRed.extra'`, `pat_defeq`); (6) `conv` from `B` at the
major's ctor spine to `B` at `σ`, and the transfer to `(m, a)` (`LR.finish`). The iota case uses
the two `Params` fields `rec_major_indTy` and `rhs_not_field` (through `pat_leaf_gap`). `hty` and
`hdef` are not used: `Params.pat_typed` and `Params.pat_defeq` give them from `hP` and `hg`. -/
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
  obtain ⟨sp, rfl⟩ := Params.pat_simple hP
  cases sp with
  | defn c₀ =>
    exact LR.pat_leaf_delta WFIH hc h1 h2 LIH hR hP hMt hRHS hchk g hg hT hk W le hA hmem
  | iota c₀ mm c' kf =>
    have hhd : c = c₀ := by
      have := LE_Interp.Matches.head hMt
      simp only [SimplePattern.toPattern, Pattern.head, Pattern.head_varN] at this
      exact this.symm
    subst hhd
    obtain ⟨hgapI, hgapF⟩ := pat_leaf_gap hP h1 g
    exact LR.pat_leaf_iota WFIH hc h1 h2 LIH hR hP hMt hRHS hchk g hg hT hk hρ W le hA hmem
      tyV hgapI hgapF

/-! ### The spine lemma (PLAN D4, R9) -/

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
* `pat`: `LR.pat_leaf_1a` (E6, landed by R10). -/
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
