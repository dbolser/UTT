import Lean4Lean.Experimental.E6.IotaData
/-! # E6: the two residual facts of the iota leaf, and the cases of them that are proved

The iota leaf (`T.pat_leaf_iota`) needs two facts about an iota rule `rec x₁ … xₘ (c' z₁ … zₖ)`
that the landed definitions do not provide in general. Each is a `theorem` here whose proof
covers every case it can and leaves ONE marked `sorry` for the case that needs unique typing.

* F1, `T.gap_major_levels`: the levels `ls₂` that the major's constructor clause reads off the
  whnf of the major domain `const I ls'` (`ls' = us.map (instV ls)`, `us` from `Pattern.genIota`)
  are `ls'` themselves. Proved when `I` has no delta rule (then `const I ls'` is a whnf,
  `T.const_whnf`) and when `c'` has no universe parameters (`T.lhs_ctor_levels`). Left: `I` has a
  delta rule and `c'` is universe-polymorphic.
* F2, `T.gap_field_sort`: if the RHS is a bare constructor-field variable whose field type is a
  `Prop` at the instance, then the recursor body `B` is a `Prop` too (any derivable sort `v₁` of
  `B` is zero). Used only when `B` depends on the major: the non-dependent case and the
  non-`Prop` case are proved in `T.pat_leaf_iota_of` without it. -/
namespace Lean4Lean.SExpr
variable [Params]

/-! ## F1: the major's levels -/

/-- A bare constant with no delta rule is a whnf. -/
theorem T.const_whnf {Γ : List SExpr} {I : Name} {us : List SLevel}
    (hI : ∀ r : (Pattern.const I).RHS × (Pattern.const I).Check, ¬ Params.Pat (.const I) r) :
    WHNF Γ (.const I us) := by
  intro e' H
  cases H with
  | extra hP hm _ _ =>
    cases hm
    exact hI _ hP

/-- Head reduction does not depend on the context: every rule has `r.2 = .true`
(`Params.pat_check`), so `extra` has no side conditions. -/
theorem T.whRed_ctx {Γ Δ : List SExpr} {e e' : SExpr} (H : Γ ⊢ e ⤳ e') : Δ ⊢ e ⤳ e' := by
  induction H with
  | app _ ih => exact .app ih
  | major h _ ih => exact .major h ih
  | beta => exact .beta
  | extra hP hm _ _ =>
    refine WHRed.extra' hP hm fun x hx => ?_
    rw [Params.pat_check hP] at hx; cases hx

theorem T.whRedS_ctx {Γ Δ : List SExpr} {e e' : SExpr} (H : Γ ⊢ e ⤳* e') : Δ ⊢ e ⤳* e' := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (T.whRed_ctx h)

/-- The head of a strongly sound spine is strongly sound. -/
theorem T.spine_head_sound {Γ : List SExpr} : ∀ (Zs : List SExpr) {h T : SExpr},
    StrongSound Γ (spine h Zs) T → ∃ T', StrongSound Γ h T'
  | [], _, _, H => ⟨_, H⟩
  | Z :: Zs, h, T, H => by
    obtain ⟨T', H'⟩ := T.spine_head_sound Zs (h := .app h Z) H
    obtain ⟨-, -, hcore, -⟩ := H'
    cases hcore with
    | app _ hf _ => exact ⟨_, hf⟩

/-- A strongly sound constant has its declared number of levels. -/
theorem T.const_sound_levels {Γ : List SExpr} {c : Name} {ls : List SLevel} {T : SExpr}
    {ci : VConstant} (H : StrongSound Γ (.const c ls) T)
    (hci : Params.env.constants c = some ci) : ls.length = ci.uvars := by
  obtain ⟨-, -, hcore, -⟩ := H
  cases hcore with
  | const h1 h2 => cases h1.symm.trans hci; exact h2

/-- From the rule's open equation (the pinned `hdef`, i.e. `pat_defeq`): the generic LHS's
constructor `c'.{us}` has the constructor's number of levels (`StrongSound` inversion). -/
theorem T.lhs_ctor_levels {c c' : Name} {mm kf : Nat}
    {r : (Pattern.iota c mm c' kf).RHS × (Pattern.iota c mm c' kf).Check} {g : PatGen}
    (hg : Pattern.gen Params.env Params.rank Params.classify (.iota c mm c' kf) r.1 = some g)
    {ci : VConstant} (h1 : Params.env.constants c = some ci)
    (hΓ : OnCtx g.ctx (fun Γ A => Params.env.IsType ci.uvars Γ A))
    (hdef : Params.env.IsDefEq ci.uvars g.ctx g.lhs g.rhs g.type)
    {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr} (hHs : Hs.length = mm)
    (hcty : ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj))
    {ci' : VConstant} (hci' : Params.env.constants c' = some ci') : us.length = ci'.uvars := by
  have H := (LE_Interp.strongSoundS (T.strong_env_defeq hΓ hdef [])).left
  rw [Pattern.gen_lhs hg h1 hHs hcty] at H
  obtain ⟨-, -, hcore, -⟩ := H
  simp only [mkInst] at hcore
  cases hcore with
  | app _ _ ha =>
    rw [mkInst_bvarSpine] at ha
    obtain ⟨T', hT'⟩ := T.spine_head_sound _ ha
    simpa [mkInst] using T.const_sound_levels hT' hci'

/-- **Gap F1.** The constructor clause of the major (`LRS.CtorDefEq` at the major domain
`const I ls'`, `ls' = us.map (instV ls)`) gives `TyRedS Γ₀ (const I ls') (const I₂ ls₂)` with the
constructor spine at `ls₂`. The iota step needs `ls₂ = ls'`: `pat_defeq`'s open equation is at
`c'.{ls'}`, and the field entries of `W_p` are typed at the field types at `ls'`, while
`FieldsEq` types the fields at `ls₂`. Only the reduction part of `TyRedS` matters, and head
reduction does not depend on the context (`T.whRedS_ctx`), so the gap is stated for the closed
reduction `[] ⊢ const I ls' ⤳* const I₂ ls₂`: a fact about the rule and the environment alone.

Proved: (a) `I` has no delta rule, so `const I ls'` is a whnf and the reduction is the identity;
(b) `c'` has no universe parameters, so both lists are empty (`T.lhs_ctor_levels`, `hls₂`).

Left (the one `sorry`): `I` has a delta rule (the recursor's major domain is a definition;
`Pattern.genIota` matches the domain as `.const _ us` and never ties `I` to `c'`'s inductive) and
`c'` is universe-polymorphic. Then `ls₂` is whatever `I`'s unfolding produces (e.g.
`def J.{u} := I'.{0}` gives `ls₂ = [0]`), and `ls₂ = ls'` holds only because `pat_defeq` makes
the LHS well typed: inverting that typing gives `c'.{us} z⃗ : const I us`, type uniqueness gives
`const I us ≡ const I' us`, so `const I' ls' ≡ const I₂ ls₂` by the clause, and level
injectivity of inductive constants gives `ls₂ = ls'`. Inversion, type uniqueness and level
injectivity are unique-typing facts (R10's own goal). The WF IH does not reach them: it covers
lower-rank derivations over the fixed `Γ₀`, while `pat_defeq` is a full-environment derivation
containing `rec` itself. Shapes carry no levels, so neither the logical relation nor
`LR.const_spine` (R9) can supply it. The statement holds wherever unique typing does. -/
theorem T.gap_major_levels {c c' : Name} {mm kf : Nat}
    {r : (Pattern.iota c mm c' kf).RHS × (Pattern.iota c mm c' kf).Check} {g : PatGen}
    (_hP : Params.Pat (.iota c mm c' kf) r)
    (hg : Pattern.gen Params.env Params.rank Params.classify (.iota c mm c' kf) r.1 = some g)
    {ci : VConstant} (h1 : Params.env.constants c = some ci)
    (hΓ : OnCtx g.ctx (fun Γ A => Params.env.IsType ci.uvars Γ A))
    (hdef : Params.env.IsDefEq ci.uvars g.ctx g.lhs g.rhs g.type)
    {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr} (hHs : Hs.length = mm)
    (hcty : ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj))
    {ci' : VConstant} (hci' : Params.env.constants c' = some ci') {ls : List SLevel}
    (_h2 : ls.length = ci.uvars)
    {I₂ : Name} {ls₂ : List SLevel} (_hI₂ : Params.classify I₂ = some (.indTy 0))
    (hls₂ : ls₂.length = ci'.uvars)
    (hred : [] ⊢ .const I (us.map (SLevel.instV ls)) ⤳* .const I₂ ls₂) :
    us.map (SLevel.instV ls) = ls₂ := by
  by_cases hs : ∃ r' : (Pattern.const I).RHS × (Pattern.const I).Check, Params.Pat (.const I) r'
  · by_cases h0 : ci'.uvars = 0
    · -- (b) no universe parameters
      have hus := T.lhs_ctor_levels hg h1 hΓ hdef hHs hcty hci'
      rw [h0] at hus hls₂
      rw [List.eq_nil_of_length_eq_zero hus, List.eq_nil_of_length_eq_zero hls₂]; rfl
    · sorry -- SORRY(E6): F1, the major domain `I` has a delta rule and `c'` is universe-
      -- polymorphic. The reduction to the clause's `const I₂ ls₂` runs through `I`'s unfolding, and
      -- `ls₂ = us.map (instV ls)` needs inversion of `pat_defeq`'s LHS typing plus level
      -- injectivity of `const I₂` under defeq (unique typing). Not suppliable by R9 (shapes carry
      -- no levels). Cheapest fix in the landed definitions: `Pattern.genIota` requires the
      -- major domain head to be `c'`'s inductive (or `classify I = indTy`), then case (a) applies.
  · -- (a) `I` has no delta rule
    have hw : WHNF [] (.const I (us.map (SLevel.instV ls))) := T.const_whnf fun r' h => hs ⟨r', h⟩
    have := hw.whRedS hred
    injection this

/-- F1 under the fix proposed for `Pattern.genIota` (the major domain head is an inductive type,
as for Lean's recursors and `natParamsR`): sorry-free. -/
theorem T.major_levels_of_indTy {Γ₀ : List SExpr} {I : Name} {k : Nat}
    (hI : Params.classify I = some (.indTy k)) {ls' : List SLevel} {I₂ : Name} {ls₂ : List SLevel}
    (hred : TyRedS Γ₀ (.const I ls') (.const I₂ ls₂)) : ls' = ls₂ := by
  have hw : WHNF Γ₀ (.const I ls') := T.const_whnf fun r' h => by
    obtain ⟨_, h'⟩ := Params.Pat.head_symb h
    rw [show (Pattern.const I).head = I from rfl, hI] at h'; cases h'
  have := hw.whRedS hred.2
  injection this

/-! ## F2: a bare `Prop` field as the RHS -/

/-- If `B`'s (derivable) sort is `Prop`, every typed shape at an interpretation of `B` is `⊥`. -/
theorem T.prop_sort_bot {E : VEnv} (hE : E ≤ Params.env) {Γ₀ Γ : List SExpr} {ρ : Valuation}
    {B : SExpr} {vB : SLevel} (HB : IsDefEqStrong E Γ B B (.sort vB))
    (W : Valuation.Fits Γ₀ Γ ρ) (hv : vB = SLevel.zero)
    {n'} {m a : WShape n'} (hA : LE_Interp ρ a.T B) (hmem : m.HasType a) : m.T ≤ TShape.bot := by
  obtain ⟨m', a₂, hle, -, ha₂, hm'⟩ := (LE_Interp.soundSE hE HB W).2 hA
  have h1 : a₂ ≤ TShape.sort false := by
    have := ha₂.le_sort; subst hv; simpa using this
  have h2 : m'.HasType (TShape.sort false) :=
    TShape.HasType.mono_r h1 (TShape.HasType.sort_r.2 WShape.HasType.sort) hm'
  have h3 : a.T.HasType (TShape.sort false) :=
    TShape.HasType.retype (TShape.HasType.sort_r.2 hmem.isType) h2 hle
  exact TShape.HasType.proofIrrel h3 (WShape.HasType.T hmem)

/-- A closed inductive constant whose sort instantiates to `Prop` is interpreted only by `⊥`
(the verifier's `V.prop_interp_bot`, /tmp/utt-exp/e6/a-verify/GapF2b.lean). -/
theorem T.prop_interp_bot {ρ : Valuation} {I : Name} {ls : List SLevel} {j : Nat}
    (hI : Params.classify I = some (.indTy j)) {ciI : VConstant} {u : VLevel}
    (hci : Params.env.constants I = some ciI) (hty : ciI.type = .sort u)
    (hz : SLevel.instV ls u = .zero) {b : TShape} (H : LE_Interp ρ b (.const I ls)) :
    b ≤ TShape.bot := by
  generalize eC : SExpr.const I ls = M at H
  cases H with
  | bot => exact TShape.bot_le'
  | bvar | sort | app | lam | forallE => cases eC
  | @const _ c₁ ci₁ mT₀ m' ρ₁ a₁ ls₁ R h1 h2 h3 h4 h5 h6 h7 =>
    injection eC with e1 e2; subst e1 e2
    cases h1.symm.trans hci
    rw [hty] at h5
    have hs := h5.le_sort
    have hm' := TShape.HasType.mono_r hs (TShape.HasType.sort_r.2 .sort) h4
    simp only [hz, ne_eq, not_true_eq_false, decide_false] at hm'
    cases h6 with
    | bot => exact h3.trans TShape.bot_le'
    | lam _ hle => exact h3.trans ((T.typeShape_le_lam' hm' hle).trans TShape.bot_le)
    | ctor h _ => cases hI.symm.trans h
    | indTy _ hle =>
      refine h3.trans ?_
      obtain ⟨nm, w⟩ := m'
      rename_i nn _
      obtain ⟨K, hK⟩ : ∃ K, max nm (nn+1) = K + 1 := ⟨max nm (nn+1) - 1, by omega⟩
      have hl := (TShape.LE.def (Nat.le_max_left nm (nn+1)) (Nat.le_max_right nm (nn+1))).1 hle
      have ht := (TShape.HasType.def (m := max nm (nn+1)) (Nat.le_max_left nm (nn+1))
        (Nat.zero_le _)).1 hm'
      simp only [WShape.T] at hl ht
      rw [hK] at hl ht
      rw [WShape.lift_indTy] at hl
      rcases WShape.le_indTy.1 hl with e | e
      · rw [TShape.LE.def (m := max nm (nn+1)) (Nat.le_max_left _ _) (Nat.zero_le _)]
        simp only [TShape.bot, WShape.T]
        rw [hK, e, WShape.lift_bot]; exact WShape.LE.rfl
      · rw [e] at ht
        simp only [TShape.sort, WShape.T] at ht
        rw [WShape.lift_sort] at ht
        exact absurd ht (by simp [WShape.HasType, WShape.indTy, WShape.sort, Shape.HasType,
          Shape.hasType])
    | pat hP hM _ =>
      obtain ⟨_, h⟩ := Params.Pat.head_symb hP
      rw [T.matches_head hM, hI] at h; cases h

/-- A shape typed at a type shape below `⊥` is `⊥`. -/
theorem T.le_bot_of_type_le_bot {n} {m a : WShape n} (hmem : m.HasType a)
    (ha : a.T ≤ TShape.bot) : m.T ≤ TShape.bot := by
  have := T.le_bot_T ha
  subst this
  cases hmem.bot_r; exact TShape.bot_le'

/-- The non-dependent case of F2: if `B = B₀.lift` does not mention the major, an interpretation
of `B` at `ρt.push x₀` interprets the generic type `B[major := c' z⃗]` at any valuation whose
entries beyond the `kf` fields are `ρt`. -/
theorem T.nondep_type_low {ρt ρl : Valuation} {kf : Nat} {B₀ X : SExpr} {b : TShape}
    {x₀ : TShape} (hρl : ∀ i, ρl (i + kf) = ρt i) (H : LE_Interp (ρt.push x₀) b B₀.lift) :
    LE_Interp ρl b (B₀.lift.subst (Subst.cons (fun i => .bvar (i + kf)) X)) := by
  rw [lift_subst_cons]
  exact LE_Interp.subst.2 ⟨ρt, LE_Interp.weak_iff.1 H, fun i => .bvar (by rw [hρl]; exact .rfl)⟩

/-- **Gap F2.** The RHS is a bare constructor-field variable `zₓ` whose field type
`const I₀ vs` is a `Prop` at the instance (`hz`). Then the RHS adequacy at `ρ_low` only gives
`⊥` (the lowered entry of a Prop field is `⊥`, `T.prop_interp_bot`), but the goal's element
shape `m` lies below the major's raw field shape (untyped junk such as a λ shape is allowed,
D1) and is typed at `a`, which interprets `B` at the raw valuation. `m = ⊥` follows once `B` is
a `Prop` (`T.prop_sort_bot`), i.e. this lemma.

`_HB` is a closed derivation: its context is the recursor's own instantiated telescope
`x₁ … xₘ, (x : const I ls')`, which is well formed because `rec`'s type is typed in `[]`
(`Params.type_below`; `_HB` is read off that typing by `IsDefEqStrong.telescope`). So the gap is
an instance of sort uniqueness at a well-formed closed context; no outer context `Γ₀` occurs.

Scope: only the case where `B` depends on the major (`hdep`); otherwise `a` interprets the field
type itself and is `⊥` (`T.nondep_type_low`, used in `T.pat_leaf_iota_of`).

Left (the one `sorry`): sort uniqueness. The pinned `hty` types `zₓ : g.type` and the context
gives `zₓ : const I₀ vs`; so `g.type ≡ const I₀ vs` (type uniqueness), the sort of
`g.type = B[major := c' z⃗]` is the field's sort, zero (`hz`), and that is the sort `v₁` of `B`
(sort uniqueness, plus `c' z⃗ : const I us` to substitute it for the major: the F1 link, which only
the full-environment `hdef` gives). These are unique-typing facts. The WF IH does not give them:
both typings of `zₓ` are lower-rank, but the WF IH is fixed at the outer `Γ₀` and cannot be used
at the rule context `g.self ++ g.ctx` as its own target.

Why semantics alone cannot give it: every valuation that fits `g.ctx` has `⊥` at `zₓ`
(`⟦const I₀ vs⟧ = {⊥}`, `T.prop_interp_bot`), so soundness of `hty` and `hdef` speaks only about
`⊥` there (`StrongSound.uniq` gives only `SoundEq`). The goal's `a` interprets `B` at the raw
valuation, whose major entry may carry junk at `zₓ`, and `⟦B⟧` grows with the valuation. R9
cannot supply it either: it is a fact about the rule's typing, and the junk comes from
`LE_Interp.const`'s argument shapes, which `LamDefEq` forces R9 to range over. The statement
holds wherever unique typing does. -/
theorem T.gap_field_sort {c c' : Name} {mm kf : Nat}
    {r : (Pattern.iota c mm c' kf).RHS × (Pattern.iota c mm c' kf).Check}
    (_hP : Params.Pat (.iota c mm c' kf) r) {ci : VConstant}
    (_h1 : Params.env.constants c = some ci) {g : PatGen}
    (_hg : Pattern.gen Params.env Params.rank Params.classify (.iota c mm c' kf) r.1 = some g)
    (_hdef : Params.env.IsDefEq ci.uvars g.ctx g.lhs g.rhs g.type)
    {x : (Pattern.varN (.const c') kf).Path} (_hx : r.1 = .var (.inr x))
    {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr} (_hHs : Hs.length = mm)
    (_hcty : ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj))
    {ls : List SLevel} (_h2 : ls.length = ci.uvars)
    {I₀ : Name} {vs : List VLevel} {ciI : VConstant} {u₀ : VLevel}
    (_hgctx : g.ctx[(Pattern.iota c mm c' kf).pathIdx (.inr x)]? = some (.const I₀ vs))
    (_hciI : Params.env.constants I₀ = some ciI) (_htyI : ciI.type = .sort u₀)
    (_hz : SLevel.instV (vs.map (SLevel.instV ls)) u₀ = .zero)
    (_hdep : ¬ ∃ B₀ : SExpr, mkInst ls Bmaj = B₀.lift)
    {v₁ : SLevel}
    (_HB : IsDefEqStrong (Params.env.below Params.rank (Params.rank c))
      (Hs.map (mkInst ls) ++ [SExpr.const I (us.map (SLevel.instV ls))]).reverse
      (mkInst ls Bmaj) (mkInst ls Bmaj) (.sort v₁)) :
    v₁ = SLevel.zero := by
  sorry -- SORRY(E6): F2, sort uniqueness. The rule `rec … (c' z⃗) ⤳ zₓ` types `zₓ : g.type`
  -- (`hty`) and `zₓ : const I₀ vs : Prop` (context), so `B[major := c' z⃗]`'s sort, and so `B`'s
  -- sort `v₁`, is zero; that needs type and sort uniqueness plus `c' z⃗ : const I us` (unique
  -- typing; the last only from the full-environment `hdef`). Not suppliable by R9. Fix in
  -- the landed definitions: `Pattern.gen` (or a `Params` field) requires, for an iota rule with a
  -- bare constructor-field RHS, that `Bmaj` not mention the major (or that the field type is not
  -- a `Prop`); Lean's recursor rules never have a bare-field RHS, and stage-1a projections have a
  -- closed codomain. Then this lemma is never called (`T.pat_leaf_iota_fixed`).

end Lean4Lean.SExpr
