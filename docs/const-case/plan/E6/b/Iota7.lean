import Lean4Lean.Experimental.E6.Iota6
/-! E6, iota shape: the two facts about the rule that the available lemmas do not reach (fact A,
`T.gap_major_levels`, sorry in one branch; fact B, `T.gap_prop_root_sort`, sorry), and small
helpers for the assembly. `T.pat_leaf_iota` takes both facts as hypotheses. -/
namespace Lean4Lean.SExpr
variable [Params]

theorem T.fieldsEq_len {Γ : List SExpr} {n : Nat} {IH : LogRel Γ n} {Ts Xs Ys : List SExpr}
    {l : List (WShape n)} (H : LRS.FieldsEq IH Ts Xs Ys l) :
    Xs.length = Ts.length ∧ Ys.length = Ts.length ∧ l.length = Ts.length := by
  induction H with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons _ _ _ ih => simp [ih.1, ih.2.1, ih.2.2]

/-- A recursor-argument path's raw shape is below its `lowerCtx` entry (`hρ`). -/
theorem T.rec_path_bound {c : Name} {mm : Nat} {N : Nat} {rf : List (WShape (N+1))}
    {mf : (Pattern.varN (.const c) mm).Path → TShape}
    (hf : LE_Interp.Matches (.varN (.const c) mm) c rf mf) {x0 : WShape (N+1)}
    {ρ : Valuation} (hρ : (Valuation.ofRargs (x0 :: rf)).LE ρ) {fields : List TShape} {kf : Nat}
    (hkf : fields.length = kf) (x : (Pattern.varN (.const c) mm).Path) :
    mf x ≤ Valuation.lowerCtx fields ρ mm (kf + (Pattern.varN (.const c) mm).pathIdx x) := by
  subst hkf
  obtain ⟨lf, hxf⟩ := T.matches_varN mm hf
  obtain ⟨s, hs, he⟩ := hxf x
  have hi : (Pattern.varN (.const c) mm).pathIdx x < mm := lf ▸ (List.getElem?_eq_some_iff.1 hs).1
  rw [T.lowerCtx_rec _ _ _ _ hi]
  have := hρ ((Pattern.varN (.const c) mm).pathIdx x + 1)
  rw [Valuation.ofRargs, List.foldr_cons, Valuation.push, ← Valuation.ofRargs,
    T.ofRargs_get hs] at this
  exact he ▸ this

/-- The head constant of a strongly sound spine has the right number of levels. -/
theorem T.spine_head_sound {Γ : List SExpr} : ∀ (Zs : List SExpr) {h T : SExpr},
    StrongSound Γ (spine h Zs) T → ∃ T', StrongSound Γ h T'
  | [], _, _, H => ⟨_, H⟩
  | Z :: Zs, h, T, H => by
    obtain ⟨T', H'⟩ := T.spine_head_sound Zs (h := .app h Z) H
    obtain ⟨-, -, hcore, -⟩ := H'
    cases hcore with
    | app _ hf _ => exact ⟨_, hf⟩

theorem T.const_sound_levels {Γ : List SExpr} {c : Name} {ls : List SLevel} {T : SExpr}
    {ci : VConstant} (H : StrongSound Γ (.const c ls) T)
    (hci : Params.env.constants c = some ci) : ls.length = ci.uvars := by
  obtain ⟨-, -, hcore, -⟩ := H
  cases hcore with
  | const h1 h2 => cases h1.symm.trans hci; exact h2

/-- From `pat_defeq`: the generic LHS's constructor has its declared number of levels. -/
theorem T.lhs_ctor_levels {c c' : Name} {mm nn : Nat}
    {r : (Pattern.iota c mm c' nn).RHS × (Pattern.iota c mm c' nn).Check} {g : PatGen}
    (hg : Pattern.gen Params.env Params.rank Params.classify (.iota c mm c' nn) r.1 = some g)
    {ci : VConstant} (h1 : Params.env.constants c = some ci)
    (hΓctx : OnCtx g.ctx (fun Γ A => Params.env.IsType ci.uvars Γ A))
    (hdef : Params.env.IsDefEq ci.uvars g.ctx g.lhs g.rhs g.type)
    {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr} (hHs : Hs.length = mm)
    (hTc : ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj))
    {ci' : VConstant} (hci' : Params.env.constants c' = some ci') : us.length = ci'.uvars := by
  have H := (LE_Interp.strongSoundS (T.strong_env hΓctx hdef.hasType.1 [])).left
  rw [Pattern.gen_lhs hg h1 hHs hTc] at H
  obtain ⟨-, -, hcore, -⟩ := H
  simp only [mkInst] at hcore
  cases hcore with
  | app _ _ ha =>
    rw [mkInst_bvarSpine] at ha
    obtain ⟨T', hT'⟩ := T.spine_head_sound _ ha
    simpa [mkInst] using T.const_sound_levels hT' hci'

/-- A bare constant with no delta rule is in whnf. -/
theorem T.const_whnf {Γ : List SExpr} {I : Name} {us : List SLevel}
    (hI : ∀ (r : (Pattern.const I).RHS × (Pattern.const I).Check), ¬ Params.Pat (.const I) r) :
    WHNF Γ (.const I us) := by
  intro e' H
  cases H with
  | extra hP hm _ _ =>
    cases hm
    exact hI _ hP

/-- **Gap (A), the levels tie of the major (PLAN §4 open question 3).** The constructor clause
reads its levels `ls''` off the whnf of the major's type `const I us₀`. Proved when `I` has no
delta rule (then `const I us₀` is in whnf and `ls'' = us₀`, `T.const_whnf`) and when the
constructor has no universe parameters (both lists are empty, `T.lhs_ctor_levels`). Left: `I` has
a delta rule `Pat (.const I) r` (the recursor's major domain is a definition; `Pattern.gen` only
asks for a syntactic `.const I us` domain, and `Const.pat` at `I` is what lets `indTy` interpret
it) and `c'` is universe-polymorphic. Then `I.{us₀}` unfolds to `I_c.{ls''}` with levels of its
own. Tying them to `us₀` takes `pat_defeq`'s LHS typing: `c'.{us} z⃗ : I_c.{us}` (its constructor
type) and `: I.{us}` (the recursor's major domain), so `I.{us} ≡ I_c.{us}` (uniqueness of types),
and then `I_c.{ls''} ≡ I_c.{us₀}` gives `ls'' = us₀` (levels of a whnf constant are injective
under defeq, i.e. confluence). Both are unique-typing facts, not available here. Untyped matching
ignores the constructor's levels (`MatchesS.app`), so the reduction itself fires at `ls''`; only
its typed counterpart (`pat_defeq`, at `us₀`) needs the tie. -/
theorem T.gap_major_levels {Γ₀ : List SExpr} {c c' : Name} {mm nn : Nat}
    {r : (Pattern.iota c mm c' nn).RHS × (Pattern.iota c mm c' nn).Check} {g : PatGen}
    (_hP : Params.Pat (.iota c mm c' nn) r)
    (hg : Pattern.gen Params.env Params.rank Params.classify (.iota c mm c' nn) r.1 = some g)
    {ci : VConstant} (h1 : Params.env.constants c = some ci) {ls : List SLevel}
    (hΓctx : OnCtx g.ctx (fun Γ A => Params.env.IsType ci.uvars Γ A))
    (hdef : Params.env.IsDefEq ci.uvars g.ctx g.lhs g.rhs g.type)
    {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr} (hHs : Hs.length = mm)
    (hTc : ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj))
    {ci' : VConstant} (hci' : Params.env.constants c' = some ci')
    {I_c : Name} {ls'' : List SLevel} (_hIc : Params.classify I_c = some (.indTy 0))
    (hls'' : ls''.length = ci'.uvars)
    (hred : TyRedS Γ₀ (.const I (us.map (SLevel.instV ls))) (.const I_c ls'')) :
    us.map (SLevel.instV ls) = ls'' := by
  by_cases hs : ∃ r' : (Pattern.const I).RHS × (Pattern.const I).Check, Params.Pat (.const I) r'
  · by_cases h0 : ci'.uvars = 0
    · have hus := T.lhs_ctor_levels hg h1 hΓctx hdef hHs hTc hci'
      rw [h0] at hus hls''
      rw [List.eq_nil_of_length_eq_zero hus, List.eq_nil_of_length_eq_zero hls'']; rfl
    · -- SORRY(E6): the recursor's major domain `I` has a delta rule (it is a definition) and the
      -- constructor `c'` is universe-polymorphic: `TyRedS` to the clause's `const I_c ls''` goes
      -- through `I`'s unfolding, and `ls'' = us.map (instV ls)` needs level injectivity of
      -- `const I_c` under defeq (unique typing). Supplied by a Params field / `Pattern.gen` check
      -- that the major domain's head is the inductive (`classify I = some (.indTy 0)`, or just "no
      -- `Pat (.const I)`"; kernel invariant: a recursor's major premise has the inductive as its
      -- type; `T.pat_leaf_1a_restricted`, `RA`, shows it suffices); R9 cannot supply it.
      sorry
  · have hw : WHNF Γ₀ (.const I (us.map (SLevel.instV ls))) := T.const_whnf fun r' h => hs ⟨r', h⟩
    have := hw.whRedS hred.2
    injection this

/-- If `B`'s sort is `Prop`, every typed shape at an interpretation of `B` is `⊥`. -/
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

/-- **Gap (B), the sort of a rule whose RHS is a `Prop`-instance constructor field.** Every datum
is the rule's own: `hP`/`hg`/`h1` fix the rule `rec x₁…xₘ (c' z₁…zₙ) ⤳ zᵢ` (`hroot`: the RHS is
the bare field variable `x`), `hHs`/`hTc` read the recursor's type as `Π Hs, Π (_ : I.{us}), Bmaj`,
`F` is the field's own type in the generated context (`hF`), at the leaf's levels `ls`, and has no
`indTy` interpretation (`hprop`: `F = J.{vs}` with `J : Sort u` and `u` instantiated to zero, a
`Prop` instance). `HB` is the strong typing of the codomain `Bmaj` in the recursor telescope over
`Γ₀`, at sort `vB`.

The claim `vB = 0` is sort uniqueness for this rule: by `pat_typed` (and `pat_defeq`) the field
`zᵢ : F` also has type `g.type = Bmaj[c' z⃗]`, and `c' z⃗ : I.{us}` by the LHS typing, so
`F ≡ Bmaj[c' z⃗]` and their sorts `0` and `vB` agree. That is a unique-typing fact (uniqueness of
types up to defeq, plus injectivity of `Sort` under defeq); nothing here provides it. The shape model cannot
see it: a type whose only interpretation is `⊥` has every sort shape, and the major's constructor
shape may carry a non-`⊥` shape such as `indTy` at a `Prop` field (`LRS.FieldRel` constrains only
the sub-shapes typed `indTy`, and the only one below `indTy` is `⊥`), so `B` at the spine valuation
can have non-`Prop` interpretations that the lowered pattern valuation (whose `Prop` field entries
`Fits` forces to `⊥`) never sees. -/
theorem T.gap_prop_root_sort {Γ₀ : List SExpr} {c c' : Name} {mm nn : Nat}
    {r : (Pattern.iota c mm c' nn).RHS × (Pattern.iota c mm c' nn).Check} {g : PatGen}
    (_hP : Params.Pat (.iota c mm c' nn) r)
    (_hg : Pattern.gen Params.env Params.rank Params.classify (.iota c mm c' nn) r.1 = some g)
    {ci : VConstant} (_h1 : Params.env.constants c = some ci) {ls : List SLevel}
    (_h2 : ls.length = ci.uvars)
    {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr} (_hHs : Hs.length = mm)
    (_hTc : ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj))
    {x : (Pattern.varN (.const c') nn).Path} (_hroot : r.1 = .var (.inr x))
    {F : SExpr} (_hF : (g.ctx.map (mkInst ls))[(Pattern.varN (.const c') nn).pathIdx x]? = some F)
    (_hprop : ∀ K, ¬ LE_Interp .nil (WShape.indTy (n := K)).T F)
    (_hΓ₀ : ⊢ Γ₀) {vB : SLevel}
    (_HB : IsDefEqStrong (Params.env.below Params.rank (Params.rank c))
      (.const I (us.map (SLevel.instV ls)) :: ((Hs.map (mkInst ls)).reverse ++ Γ₀))
      (mkInst ls Bmaj) (mkInst ls Bmaj) (.sort vB)) :
    vB = SLevel.zero := by
  -- SORRY(E6): sort uniqueness for the rule `rec … (c' z⃗) ⤳ zᵢ` (see the docstring): the field's
  -- type `F` is a `Prop` instance and `pat_typed` also types `zᵢ` at `Bmaj[c' z⃗]`, so `F` and
  -- `Bmaj[c' z⃗]` are defeq types and `vB = 0`. That needs unique typing (types unique up to defeq,
  -- `Sort` injective under defeq), which no lemma here provides.
  -- R9 cannot supply it (it is a fact about the rule, not the spine). Closed instead by a Params
  -- field: no iota RHS is a bare constructor-field variable (`T.pat_leaf_1a_restricted`, `RB`), or
  -- constructor-field inductives are never `Prop` instances.
  sorry

end Lean4Lean.SExpr
