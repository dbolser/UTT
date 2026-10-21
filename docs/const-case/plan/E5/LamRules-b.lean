import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! # E5: λ-wrapped rules (PLAN §1 D5, §2 row E5)

Lean4Lean's rules are λ-closures over a binder telescope `Δ` of an open equation `L ≡ R : T`.
`Params` still carries the old `extra_patV` (the `Δ = []` form, SExpr.lean:120), so D5's
λ-`extra_patV` is the explicit hypothesis `ExtraPatVLam` (verbatim from
`docs/const-case/plan/ExtraLamStmt.lean`).  This file gives

* `T.extra_pat_lam`: its `SExpr` translation (the λ-form of `Params.extra_pat`, SExpr.lean:1067);
* `T.strongSoundS_extra_lam`: the `extra` case of `LE_Interp.strongSoundS`
  (ShapeLogRel.lean:5229-5260) for a λ-rule, through the `lam` layers of the telescope, then the
  existing argument on the open body.  Neither uses `Params.extra_pat`/`Params.extra_patV`. -/
namespace Lean4Lean.SExpr
open Lean4Lean
variable [Params]

/-- D5's λ-`extra_patV` (PLAN §1 D5), verbatim, as a hypothesis. -/
def ExtraPatVLam : Prop :=
  ∀ {df : VDefEq} {ls : List VLevel} {Γ : List VExpr},
    Params.env.defeqs df → (∀ l ∈ ls, l.WF Params.univs) → ls.length = df.uvars →
    ∃ (Δ : List VExpr) (L R T : VExpr),
      df.lhs.instL ls = Δ.foldr .lam L ∧ df.rhs.instL ls = Δ.foldr .lam R ∧
      df.type.instL ls = Δ.foldr .forallE T ∧
      OnCtx Δ.reverse (Params.env.IsType Params.univs) ∧
      Params.env.IsDefEq Params.univs Δ.reverse L R T ∧
      ∃ p r m1 m2, Params.Pat p r ∧ p.Matches L m1 m2 ∧
        r.2.OK (Params.env.IsDefEqU Params.univs (Δ.reverse ++ Γ)) m1 m2 ∧ R = r.1.apply m1 m2

namespace T

/-! ## The `SExpr` translation of `ExtraPatVLam` -/

theorem mk_foldr_lam (Δ : List VExpr) (L : VExpr) :
    mk (Δ.foldr .lam L) = (Δ.map mk).foldr .lam (mk L) := by
  induction Δ with
  | nil => rfl
  | cons A Δ ih => simp only [List.foldr_cons, List.map_cons, mk, ih]

theorem mk_foldr_forallE (Δ : List VExpr) (T : VExpr) :
    mk (Δ.foldr .forallE T) = (Δ.map mk).foldr .forallE (mk T) := by
  induction Δ with
  | nil => rfl
  | cons A Δ ih => simp only [List.foldr_cons, List.map_cons, mk, ih]

/-- A well-formed `VExpr` context is level-well-formed. -/
theorem onCtx_levelWF : ∀ {Γ : List VExpr}, OnCtx Γ (Params.env.IsType Params.univs) →
    OnCtx Γ (fun _ A => A.LevelWF Params.univs)
  | [], _ => trivial
  | _ :: _, ⟨h1, _, h2⟩ => ⟨onCtx_levelWF h1, (h2.levelWF (onCtx_levelWF h1)).1⟩

omit [Params] in
theorem onCtx_append_levelWF {U : Nat} : ∀ {Γ₁ Γ₂ : List VExpr},
    OnCtx Γ₁ (fun _ A => A.LevelWF U) → OnCtx Γ₂ (fun _ A => A.LevelWF U) →
    OnCtx (Γ₁ ++ Γ₂) (fun _ A => A.LevelWF U)
  | [], _, _, h => h
  | _ :: _, _, ⟨h1, h2⟩, h => ⟨onCtx_append_levelWF h1 h, h2⟩

omit [Params] in
/-- An entry of an `OnCtx` context satisfies the predicate over its own suffix. -/
theorem onCtx_mid {P : List VExpr → VExpr → Prop} {A : VExpr} : ∀ {Γ₁ Γ₂ : List VExpr},
    OnCtx (Γ₁ ++ A :: Γ₂) P → P Γ₂ A ∧ OnCtx Γ₂ P
  | [], _, ⟨h1, h2⟩ => ⟨h2, h1⟩
  | _ :: _, _, ⟨h1, _⟩ => onCtx_mid h1

/-- A judgment in a well-formed `VExpr` telescope `Ξ`, translated into `SExpr` with any
(level-well-formed) outer context `Γ'` appended: `IsDefEq.weakR` then `IsDefEq.mkS`. -/
theorem isDefEq_append_mkS {Ξ Γ' : List VExpr} {e₁ e₂ A : VExpr}
    (hΞ : OnCtx Ξ (Params.env.IsType Params.univs))
    (hΓ' : OnCtx Γ' (fun _ A => A.LevelWF Params.univs))
    (H : Params.env.IsDefEq Params.univs Ξ e₁ e₂ A) :
    IsDefEq (Ξ.map mk ++ Γ'.map mk) (mk e₁) (mk e₂) (mk A) := by
  have := IsDefEq.mkS (H.weakR Params.henv (VEnv.CtxWF.closed Params.henv hΞ) Γ')
    (onCtx_append_levelWF (onCtx_levelWF hΞ) hΓ')
  simpa only [List.map_append] using this

/-- The `SExpr` form of `ExtraPatVLam` (the λ-form of `Params.extra_pat`): every instantiated
rule is the λ-closure over a telescope `Δ` (binder `A` typed over the outer binders `Δ₁` and
`Γ`) of an open typed equation `Δ.reverse ++ Γ ⊢ L ≡ R : T` whose `L` is a pattern instance with
side conditions holding in `Δ.reverse ++ Γ` and right-hand side `R`.  With `Δ = []` the last
conjunct is `Params.extra_pat`'s conclusion. -/
theorem extra_pat_lam (hlam : ExtraPatVLam) (Γ : List SExpr) {df : VDefEq} {ls : List SLevel}
    (h1 : Params.env.defeqs df) (h2 : ls.length = df.uvars) :
    ∃ (Δ : List SExpr) (L R T : SExpr),
      .mkInst ls df.lhs = Δ.foldr .lam L ∧ .mkInst ls df.rhs = Δ.foldr .lam R ∧
      .mkInst ls df.type = Δ.foldr .forallE T ∧
      (∀ Δ₁ A Δ₂, Δ = Δ₁ ++ A :: Δ₂ → ∃ u, Δ₁.reverse ++ Γ ⊢ A : .sort u) ∧
      Δ.reverse ++ Γ ⊢ L ≡ R : T ∧
      ∃ p r m1 m2 dfs, Params.Pat p r ∧ p.MatchesS L m1 m2 ∧
        (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 ∧
        (∀ a b A, (A, a, b) ∈ dfs → Δ.reverse ++ Γ ⊢ a ≡ b : A) ∧
        R = r.1.applyS m1 m2 := by
  obtain ⟨vs, hvs, rfl⟩ := SLevel.exists_map_mk ls
  obtain ⟨Γ', hΓ', rfl⟩ := SExpr.exists_map_mk Γ
  obtain ⟨Δ, L, R, T, hl, hr, ht, hΔ, hLRT, p, r, m1, m2, hp, hm, hok, hR⟩ :=
    hlam (Γ := Γ') h1 hvs (by simpa using h2)
  have hΔwf := onCtx_levelWF hΔ
  have hm1 := hm.levelWF (hLRT.levelWF hΔwf).1
  obtain ⟨dfs, hdfs, hdefeq⟩ := hok.mkS (onCtx_append_levelWF hΔwf hΓ') hm1
  refine ⟨Δ.map mk, mk L, mk R, mk T, ?_, ?_, ?_, ?_, ?_, p, r, _, _, dfs, hp, hm.mkS, hdfs, ?_, ?_⟩
  · rw [mkInst_map_mk hvs, hl, mk_foldr_lam]
  · rw [mkInst_map_mk hvs, hr, mk_foldr_lam]
  · rw [mkInst_map_mk hvs, ht, mk_foldr_forallE]
  · intro Δ₁' A' Δ₂' e
    obtain ⟨Δ₁, l₂, rfl, rfl, e2⟩ := List.map_eq_append_iff.1 e
    obtain ⟨A, Δ₂, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 e2
    have hmid : OnCtx (Δ₂.reverse ++ A :: Δ₁.reverse) (Params.env.IsType Params.univs) := by
      simpa using hΔ
    obtain ⟨⟨u, hA⟩, hΔ₁⟩ := onCtx_mid hmid
    exact ⟨_, by simpa [List.map_reverse, mk] using isDefEq_append_mkS hΔ₁ hΓ' hA⟩
  · simpa [List.map_reverse] using isDefEq_append_mkS hΔ hΓ' hLRT
  · intro a b A hmem; simpa [List.map_reverse] using hdefeq a b A hmem
  · rw [hR]; exact Pattern.RHS.mkS_apply hm1 _

/-! ## The `extra` case of `LE_Interp.strongSoundS` for a λ-rule -/

/-- Soundness of `lam` congruence (the `lamDF` case of `strongSoundS`, ShapeLogRel.lean:5101,
with equal domains). -/
theorem soundEq_lam {Γ : List SExpr} {A M N : SExpr} {u : SLevel}
    (hA : SoundTy Γ A (.sort u)) (H : SoundEq (A::Γ) M N) :
    SoundEq Γ (.lam A M) (.lam A N) := by
  intro _ ρ W m
  suffices ∀ {M N}, SoundEq (A::Γ) M N → LE_Interp ρ m (.lam A M) → LE_Interp ρ m (.lam A N) from
    ⟨this H, this H.symm⟩
  intro M N H h
  cases h with
  | bot => exact .bot
  | lam h1 h2 h3 h4 =>
    exact .lam h1 h2 (fun _ h => (H (W.cons (InterpTyped.hsort (hA W)) h1 h.T)).1 (h3 _ h)) h4

/-- The existing `extra` argument (ShapeLogRel.lean:5233-5260) on an open pattern instance `L`
with right-hand side `R`, from the strong soundness of `L` and the soundness of `R`'s typing at
the same type. -/
theorem soundEq_pat {Γ : List SExpr} {L R X : SExpr} {p : Pattern} {r : p.RHS × p.Check}
    {m1 : List SLevel} {m2 : p.Path → SExpr}
    (a1 : Params.Pat p r) (a2 : p.MatchesS L m1 m2) (a5 : R = r.1.applyS m1 m2)
    (hL : StrongSound Γ L X) (hR : SoundTy Γ R X) : SoundEq Γ L R := by
  subst a5
  intro Γ₀ ρ W m
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ (LE_Interp.sound_bot (A := default)).1
  refine ⟨fun hLE => ?_, fun hLE => ?_⟩
  · obtain ⟨_, built⟩ := LE_Interp.Matches.of_matchesS a2 (Params.pat_wf a1) hLE
    obtain ⟨_, rargs, m_path, m_head, hMatch, hpath, hle, hConst⟩ := built _ (Nat.le_refl _)
    cases hConst with
    | bot => cases hm (hle.trans TShape.bot_eqv.1)
    | lam hRec hle_lam =>
      refine hm ((hle.trans hle_lam).trans ?_) |>.elim
      rw [WShape.lam']; split <;> [rename_i hf; exact TShape.bot_eqv.1]
      obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf
      refine (hn (WShape.LE.T_iff.1 (.trans ?_ TShape.bot_eqv.2))).elim
      exact (hRec s t hxy).compat_mismatch (by simp) <| .inr <| .inr ⟨_, _, _, a1, hMatch⟩
    | ctor h | indTy h =>
      obtain ⟨_, h_symb⟩ := hMatch.head_wf (Params.pat_wf a1)
      cases h ▸ h_symb
    | pat hP hM hRHS'
    obtain ⟨_, hi⟩ := hM.matches_inter (.rfl fun _ _ => .rfl)
      (Params.pat_wf hP) hMatch (Params.pat_wf a1)
    obtain ⟨rfl, -, ⟨⟩⟩ := Params.pat_uniq a1 hP .refl hi
    exact .mono hle <| LE_Interp.RHS.le_applyS hpath (fun _ _ => id) <|
      LE_Interp.Matches.unique (Params.pat_wf a1) hM hMatch ▸ hRHS'
  · have ⟨_, _, a, hm_lvl, hm_le_typed, h_LE_m_typed_R, ha, h_m_typed_HT⟩ := (hR W hLE).out
    obtain ⟨m_path_T, hpath, hRHS⟩ := LE_Interp.RHS.of_applyS h_LE_m_typed_R
    obtain ⟨_, built⟩ := LE_Interp.build_spine a2 W hL (Params.pat_wf a1) hpath
    obtain ⟨c, rargs, m', rAs, hMatch, hbnd, h_per_arg, h_foldr_eq⟩ := built _ (Nat.le_refl _)
    exact .mono hm_le_typed <| h_foldr_eq ▸ LE_Interp.apps_realize W h_m_typed_HT.T ha
      (h_foldr_eq ▸ hL) h_per_arg (.pat a1 hMatch (hRHS.mono_l hbnd))

/-- Through the `lam` layers of a telescope: invert `StrongSound` of each λ (its core is
`StrongSoundCore.lam`), identify the two codomains by `SoundEq.forallE_inv`, and close each layer
by `soundEq_lam`; the open body is `hbody`. -/
theorem soundEq_foldr_lam {L R : SExpr} : ∀ (Δ : List SExpr) {Γ : List SExpr} {XL XR : SExpr},
    (∀ {Y}, StrongSound (Δ.reverse ++ Γ) L Y → SoundTy (Δ.reverse ++ Γ) R Y →
      SoundEq (Δ.reverse ++ Γ) L R) →
    StrongSound Γ (Δ.foldr .lam L) XL → StrongSound Γ (Δ.foldr .lam R) XR → SoundEq Γ XL XR →
    SoundEq Γ (Δ.foldr .lam L) (Δ.foldr .lam R)
  | [], _, _, _, hbody, hL, hR, hX => hbody hL (hR.sound.defeq_r hX.symm)
  | A :: Δ, Γ, _, _, hbody, ⟨_, _, hcL, hXL⟩, ⟨_, _, hcR, hXR⟩, hX => by
    let .lam hA hbL := hcL
    let .lam hA' hbR := hcR
    have hB := (SoundEq.forallE_inv (hXL.trans (hX.trans hXR.symm)) hA hA').2
    have e : (A :: Δ).reverse ++ Γ = Δ.reverse ++ A :: Γ := by simp
    rw [e] at hbody
    exact soundEq_lam hA (soundEq_foldr_lam Δ hbody hbL hbR hB)

/-- The `extra` case of `LE_Interp.strongSoundS` for a λ-wrapped rule (E5). `ih1`/`ih2` are the
case's two IHs (`IsDefEqStrong.extra`'s typing premises, SExpr.lean:1139). -/
theorem strongSoundS_extra_lam (hlam : ExtraPatVLam) {df : VDefEq} {ls : List SLevel}
    {Γ : List SExpr} (h1 : Params.env.defeqs df) (h2 : ls.length = df.uvars)
    (ih1 : StrongSoundEq Γ (.mkInst ls df.lhs) (.mkInst ls df.lhs) (.mkInst ls df.type))
    (ih2 : StrongSoundEq Γ (.mkInst ls df.rhs) (.mkInst ls df.rhs) (.mkInst ls df.type)) :
    StrongSoundEq Γ (.mkInst ls df.lhs) (.mkInst ls df.rhs) (.mkInst ls df.type) := by
  refine ⟨.extra h1 h2, ?_, ih1.left, ih2.left⟩
  obtain ⟨Δ, L, R, T, eL, eR, -, -, -, p, r, m1, m2, -, a1, a2, -, -, a5⟩ :=
    extra_pat_lam hlam Γ h1 h2
  have hL := ih1.left; have hR := ih2.left
  rw [eL] at hL ⊢; rw [eR] at hR ⊢
  exact soundEq_foldr_lam Δ (fun hL' hR' => soundEq_pat a1 a2 a5 hL' hR') hL hR .rfl

end T
end Lean4Lean.SExpr
