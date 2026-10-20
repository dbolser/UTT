import Lean4Lean.Experimental.E6.Iota
/-! # E6: the pattern leaf `T.pat_leaf_1a`

`T.pat_leaf_1a` has exactly the statement of the repo's `LR.pat_leaf_1a`
(`ShapeLogRelAdequacy.lean`). By `Params.pat_simple` the pattern is a delta rule `.const c`
(`T.pat_leaf_delta`, sorry-free) or an iota rule `rec x₁ … xₘ (c' z₁ … zₖ)` (`T.pat_leaf_iota`,
sorry-free given two facts). The two facts are `T.pat_leaf_gap`, the one `sorry` of E6: properties
of the iota rules that the landed `Params` does not state (see its docstring). -/
namespace Lean4Lean.SExpr
variable [Params]

/-- **The E6 gap**: two properties of every iota rule `rec x₁ … xₘ (c' z₁ … zₖ)` that the pattern
leaf needs and the landed `Params` does not provide.

1. The head `I` of the recursor's major domain `const I us` (`gen_head`) is not a `symb`, so that
   `const I ls'` is a whnf. The major's ctor clause (`LRS.CtorDefEq`) only gives
   `TyRedS Γ₀ (const I ls') (const I₂ ls₂)` with the constructor spine at `ls₂`; without a whnf
   domain nothing ties `ls₂` to the pattern's ctor levels `ls' = us.map (instV ls)`, and both the
   instance `rec … (c'.{ls'} Xs)` of `pat_defeq`'s open equation and the field entries of `W_p`
   (typed at `Fᵢ` at `ls'`, whereas `FieldsEq` types the fields at `ls₂`) need `ls₂ = ls'`.
   Deriving it from `pat_defeq` needs injectivity of type-constructor levels under defeq (unique
   typing). Lean's recursors satisfy it (the major domain is the inductive type, `indTy`).
2. If the RHS is a bare constructor-field variable, that field's type is never a `Prop`. The goal's
   type shape `a` interprets `B` at `ρ`, whose major entry is a ctor shape with possibly untyped
   field shapes (D1, `UntypedField.lean`); `W_p` lowers them, and a Prop-valued field to `⊥`. At a
   bare field root the RHS shape is the raw field shape. For a non-Prop field type `indTy` is a
   type shape of it, so `a` is compatible with `indTy` (`T.le_indTy_of_compat`, via the type
   transfer) and the element shape lies below the lowered entry: proved. For a Prop field type
   `[[const I']] = {⊥}` and nothing relates `a` to the lowered type; excluding a non-`⊥` element
   shape there needs sort/type uniqueness. Lean's recursor rules have RHS `minor fields ihs`,
   never a bare field.

Neither fact can be supplied by `LR.const_spine` (R9): both are properties of the rule, not of
the `Const` derivation. -/
theorem T.pat_leaf_gap {c c' : Name} {mm kf : Nat}
    {r : (Pattern.iota c mm c' kf).RHS × (Pattern.iota c mm c' kf).Check}
    (hP : Params.Pat (.iota c mm c' kf) r) {ci : VConstant}
    (h1 : Params.env.constants c = some ci) {g : PatGen}
    (hg : Pattern.gen Params.env Params.rank Params.classify (.iota c mm c' kf) r.1 = some g) :
    (∀ {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr},
      ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj) → Hs.length = mm →
      ∀ j, Params.classify I ≠ some (.symb j)) ∧
    (∀ x, r.1 = .var (.inr x) → ∀ (I₀ : Name) (vs : List VLevel) (ciI : VConstant) (u : VLevel),
      g.ctx[(Pattern.iota c mm c' kf).pathIdx (.inr x)]? = some (.const I₀ vs) →
      Params.env.constants I₀ = some ciI → ciI.type = .sort u → ∀ ns, (u.inst vs).eval ns ≠ 0) := by
  sorry -- SORRY(E6): two iota-rule invariants missing from `Params` (docstring above): (1) the
  -- recursor's major-domain head is not `symb`, so the ctor clause's levels are the pattern's;
  -- (2) a bare constructor-field RHS has a never-Prop field type (Prop fields lower to `⊥`).

/-- E6 (PLAN §2 row E6, D4 "RHS step"): the pattern leaf, with exactly the statement of the
repo's `LR.pat_leaf_1a`. -/
theorem T.pat_leaf_1a {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
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
    exact T.pat_leaf_delta WFIH hc h1 h2 LIH hR hP hMt hRHS hchk g hg hT hk W le hA hmem
  | iota c₀ mm c' kf =>
    have hhd : c = c₀ := by
      have := T.matches_head hMt
      simp only [SimplePattern.toPattern, Pattern.head, Pattern.head_varN] at this
      exact this.symm
    subst hhd
    obtain ⟨hgapI, hgapF⟩ := T.pat_leaf_gap hP h1 hg
    exact T.pat_leaf_iota WFIH hc h1 h2 LIH hR hP hMt hRHS hchk g hg hT hk hρ W le hA hmem
      tyV hgapI hgapF

end Lean4Lean.SExpr
