import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! E5 (PLAN §1 D5): `extra_patV` restated for λ-wrapped rules, as an explicit hypothesis
`ExtraPatVLam`; its `SExpr` translation `T.extra_pat_lam` (the λ-form of `Params.extra_pat`);
and the `extra` case of `LE_Interp.strongSoundS` for a λ-rule, `T.strongSoundS_extra_lam`. -/
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

theorem mk_foldr_lam (L : VExpr) : ∀ Δ : List VExpr, mk (Δ.foldr .lam L) = (Δ.map mk).foldr .lam (mk L)
  | [] => rfl
  | A :: Δ => by simp only [List.foldr_cons, List.map_cons, mk, mk_foldr_lam L Δ]

theorem mk_foldr_forallE (T : VExpr) :
    ∀ Δ : List VExpr, mk (Δ.foldr .forallE T) = (Δ.map mk).foldr .forallE (mk T)
  | [] => rfl
  | A :: Δ => by simp only [List.foldr_cons, List.map_cons, mk, mk_foldr_forallE T Δ]

/-- A well-typed `VExpr` telescope, appended to a level-well-formed context, is level-well-formed. -/
theorem onCtx_append_levelWF : ∀ {Θ : List VExpr} {Γ : List VExpr},
    OnCtx Θ (Params.env.IsType Params.univs) → OnCtx Γ (fun _ A => A.LevelWF Params.univs) →
    OnCtx (Θ ++ Γ) (fun _ A => A.LevelWF Params.univs)
  | [], _, _, hΓ => hΓ
  | _ :: _, Γ, ⟨hΘ, _, hA⟩, hΓ =>
    have ih := onCtx_append_levelWF hΘ hΓ
    ⟨ih, ((hA.weakR Params.henv (VEnv.CtxWF.closed Params.henv hΘ) Γ).levelWF ih).1⟩

/-- The `SExpr` image of a well-typed `VExpr` telescope over a well-formed context is well-formed. -/
theorem ctxWF_append_mk : ∀ {Θ : List VExpr} {Γ : List VExpr},
    OnCtx Θ (Params.env.IsType Params.univs) → OnCtx Γ (fun _ A => A.LevelWF Params.univs) →
    ⊢ Γ.map mk → ⊢ (Θ ++ Γ).map mk
  | [], _, _, _, h => h
  | _ :: _, Γ, ⟨hΘ, _, hA⟩, hΓ, h =>
    ⟨ctxWF_append_mk hΘ hΓ h, _, by
      simpa [mk] using IsDefEq.mkS (hA.weakR Params.henv (VEnv.CtxWF.closed Params.henv hΘ) Γ)
        (onCtx_append_levelWF hΘ hΓ)⟩

/-- The `SExpr` form of `ExtraPatVLam` (the λ-form of `Params.extra_pat`, SExpr.lean:1067): every
instantiated defeq rule is the λ-closure over a telescope `Δ` of an open equation `L ≡ R : T`,
typed in `Δ.reverse ++ Γ` for any `SExpr` context `Γ` (whose well-formedness it preserves),
whose left side is a pattern instance with side conditions holding in `Δ.reverse ++ Γ` and whose
right side is the pattern's right-hand side. With `Δ = []` the last conjunct is exactly the
conclusion of `Params.extra_pat Γ`. -/
theorem extra_pat_lam (hlam : ExtraPatVLam) (Γ : List SExpr) {df : VDefEq} {ls : List SLevel}
    (h1 : Params.env.defeqs df) (h2 : ls.length = df.uvars) :
    ∃ (Δ : List SExpr) (L R T : SExpr),
      .mkInst ls df.lhs = Δ.foldr .lam L ∧ .mkInst ls df.rhs = Δ.foldr .lam R ∧
      .mkInst ls df.type = Δ.foldr .forallE T ∧
      (⊢ Γ → ⊢ Δ.reverse ++ Γ) ∧
      Δ.reverse ++ Γ ⊢ L ≡ R : T ∧
      ∃ p r m1 m2 dfs, Params.Pat p r ∧ p.MatchesS L m1 m2 ∧
        (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 ∧
        (∀ a b A, (A, a, b) ∈ dfs → Δ.reverse ++ Γ ⊢ a ≡ b : A) ∧
        R = r.1.applyS m1 m2 := by
  obtain ⟨vs, hvs, rfl⟩ := SLevel.exists_map_mk ls
  obtain ⟨Γ', hΓ', rfl⟩ := SExpr.exists_map_mk Γ
  obtain ⟨Δ, L, R, T, hl, hr, hT, hΔ, hLR, p, r, m1, m2, hp, hm, hok, hR⟩ :=
    hlam (Γ := Γ') h1 hvs (by simpa using h2)
  have hctx := onCtx_append_levelWF hΔ hΓ'
  have hΔlv := onCtx_append_levelWF (Γ := []) hΔ ⟨⟩
  rw [List.append_nil] at hΔlv
  have hmap : (Δ.map mk).reverse ++ Γ'.map mk = (Δ.reverse ++ Γ').map mk := by
    simp [List.map_reverse]
  have hm1 := hm.levelWF (hLR.levelWF hΔlv).1
  obtain ⟨dfs, hdfs, hdefeq⟩ := hok.mkS hctx hm1
  refine ⟨Δ.map mk, mk L, mk R, mk T, ?_, ?_, ?_, ?_, ?_, p, r, _, _, dfs, hp, hm.mkS, hdfs, ?_, ?_⟩
  · rw [mkInst_map_mk hvs, hl, mk_foldr_lam]
  · rw [mkInst_map_mk hvs, hr, mk_foldr_lam]
  · rw [mkInst_map_mk hvs, hT, mk_foldr_forallE]
  · rw [hmap]; exact ctxWF_append_mk hΔ hΓ'
  · rw [hmap]; exact IsDefEq.mkS (hLR.weakR Params.henv (VEnv.CtxWF.closed Params.henv hΔ) Γ') hctx
  · rw [hmap]; exact hdefeq
  · rw [hR]; exact Pattern.RHS.mkS_apply hm1 _

/-! ### The `extra` case of `LE_Interp.strongSoundS` for a λ-rule -/

/-- `SoundEq` congruence for `lam` (the `sound` half of the `lamDF` case of `strongSoundS`). -/
theorem SoundEq.lam (hA : SoundTy Γ A (.sort u)) (H : SoundEq (A::Γ) F G) :
    SoundEq Γ (.lam A F) (.lam A G) := by
  intro _ ρ W m
  suffices ∀ {F G}, SoundEq (A::Γ) F G → LE_Interp ρ m (.lam A F) → LE_Interp ρ m (.lam A G) from
    ⟨this H, this H.symm⟩
  intro F G H h
  cases h with | bot => exact .bot | lam h1 h2 h3 h4
  exact .lam h1 h2 (fun _ h => (H (W.cons (InterpTyped.hsort (hA W)) h1 h.T)).1 (h3 _ h)) h4

/-- The existing argument of the `extra` case of `strongSoundS` (ShapeLogRel.lean:5229-5260),
on an open pattern instance `L ⤳ R` typed (strongly-soundly) at a common type `X`. -/
theorem soundEq_pat {p : Pattern} {r : p.RHS × p.Check} {m1 : List SLevel}
    {m2 : p.Path → SExpr} {Γ : List SExpr} {L R X : SExpr}
    (a1 : Params.Pat p r) (a2 : p.MatchesS L m1 m2) (a5 : R = r.1.applyS m1 m2)
    (hL : StrongSound Γ L X) (hR : SoundTy Γ R X) : SoundEq Γ L R := by
  intro Γ₀ ρ W m
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ (LE_Interp.sound_bot (A := default)).1
  subst a5
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

/-- Through the `LE_Interp.lam` layers of a λ-telescope: the two sides' `StrongSound` facts are
inverted layer by layer (`StrongSoundCore.lam`, then `SoundEq.forallE_inv` to keep the reported
types semantically equal to the declared codomain), and `SoundEq` of the open bodies is lifted
back by `SoundEq.lam`. -/
theorem SoundEq.lam_foldr {T : SExpr} : ∀ (Δ : List SExpr) {Γ : List SExpr} {L R B B' : SExpr},
    StrongSound Γ (Δ.foldr .lam L) B → SoundEq Γ B (Δ.foldr .forallE T) →
    StrongSound Γ (Δ.foldr .lam R) B' → SoundEq Γ B' (Δ.foldr .forallE T) →
    (∀ {X Y}, StrongSound (Δ.reverse ++ Γ) L X → SoundEq (Δ.reverse ++ Γ) X T →
      StrongSound (Δ.reverse ++ Γ) R Y → SoundEq (Δ.reverse ++ Γ) Y T →
      SoundEq (Δ.reverse ++ Γ) L R) →
    SoundEq Γ (Δ.foldr .lam L) (Δ.foldr .lam R)
  | [], _, _, _, _, _, hL, hB, hR, hB', H => H hL hB hR hB'
  | A :: Δ, Γ, L, R, B, B', hL, hB, hR, hB', H => by
    have ⟨_, _, cL, eL⟩ := hL; have .lam hA hF := cL
    have ⟨_, _, cR, eR⟩ := hR; have .lam _ hG := cR
    have hBF := ((eL.trans hB).forallE_inv hA hA).2
    have hBG := ((eR.trans hB').forallE_inv hA hA).2
    have hctx : (A :: Δ).reverse ++ Γ = Δ.reverse ++ A :: Γ := by simp
    exact SoundEq.lam hA <| lam_foldr Δ hF hBF hG hBG fun h1 h2 h3 h4 =>
      hctx ▸ H (hctx ▸ h1) (hctx ▸ h2) (hctx ▸ h3) (hctx ▸ h4)

/-- The `extra` case of `LE_Interp.strongSoundS` for a λ-wrapped rule (E5). `ih1`/`ih2` are the
case's two IHs (`IsDefEqStrong.extra`'s typing premises, SExpr.lean:1139). -/
theorem strongSoundS_extra_lam (hlam : ExtraPatVLam) {df : VDefEq} {ls : List SLevel}
    {Γ : List SExpr} (h1 : Params.env.defeqs df) (h2 : ls.length = df.uvars)
    (ih1 : StrongSoundEq Γ (.mkInst ls df.lhs) (.mkInst ls df.lhs) (.mkInst ls df.type))
    (ih2 : StrongSoundEq Γ (.mkInst ls df.rhs) (.mkInst ls df.rhs) (.mkInst ls df.type)) :
    StrongSoundEq Γ (.mkInst ls df.lhs) (.mkInst ls df.rhs) (.mkInst ls df.type) := by
  refine ⟨.extra h1 h2, ?_, ih1.left, ih2.left⟩
  obtain ⟨Δ, L, R, T, hl, hr, hT, -, -, p, r, m1, m2, -, a1, a2, -, -, a5⟩ := extra_pat_lam hlam Γ h1 h2
  have hL := ih1.left; have hR := ih2.left
  rw [hl, hT] at hL; rw [hr, hT] at hR; rw [hl, hr]
  exact SoundEq.lam_foldr Δ hL .rfl hR .rfl fun hL' hX hR' hY =>
    soundEq_pat a1 a2 a5 hL' (hR'.sound.defeq_r (hY.trans hX.symm))

end T
end Lean4Lean.SExpr
