import Lean4Lean.Experimental.ShapeLogRelAdequacy

/-! Scratch experiment for the design of the `const` case of `LR.adequacy`.
Port of the artifact's `LRS.TmEq` nat-clauses / `TmEqNat` to lean4lean's
`(ctor c l, indTy)` shape pair.  Read-only w.r.t. the snapshot. -/

namespace Lean4Lean.SExpr
variable [Params]

/-- `h X₁ … Xₖ` in spine order. -/
def spine (h : SExpr) (Xs : List SExpr) : SExpr := Xs.foldl .app h

/-- Port of the artifact's `Γ ⊢ A ⤳* nat` component: the type weak-head reduces to an
inductive-type spine.  Needed to make `trans'` vacuous at `s = indTy`. -/
def LRS.IndTyRed (Γ : List SExpr) (A : SExpr) : Prop :=
  ∃ (I : Name) (ls : List SLevel) (As : List SExpr),
    Params.classify I = some (.indTy As.length) ∧ Γ ⊢ A ⤳* spine (.const I ls) As

/-- Port of `TmEqNat`, generalised to a dependent constructor telescope `Ts`
(closed; `bvar 0` = previous field).  Each field is related in the `Subst1`/`SubstWF`
form: at every type shape `a` of its declared type that is valid under the
telescope valuation `ρ` (built from the element shapes `l`).  The type-congruence
components are what `symm`/`trans` need to move between the two instantiations. -/
inductive LRS.CtorArgsEq (IH : LogRel Γ n) :
    List SExpr → List SExpr → List SExpr → List (WShape n) → Valuation → Subst → Subst → Prop
  | nil : CtorArgsEq IH [] [] [] [] ρ σ σ'
  | cons {T Ts X Xs Y Ys} {p : WShape n} {l ρ σ σ'} :
    (∃ u, Γ ⊢ T.subst σ ≡ T.subst σ' : .sort u) →
    (∀ a : WShape n, LE_Interp ρ a.T T → a.HasType .type →
      IH.TyDefEq (T.subst σ) (T.subst σ') a) →
    Γ ⊢ X ≡ Y : T.subst σ →
    (∀ a : WShape n, LE_Interp ρ a.T T → p.HasType a → IH.DefEq X Y (T.subst σ) p a) →
    CtorArgsEq IH Ts Xs Ys l (ρ.push p.T) (σ.cons X) (σ'.cons Y) →
    CtorArgsEq IH (T :: Ts) (X :: Xs) (Y :: Ys) (p :: l) ρ σ σ'

/-- The new `LRS.DefEq` clause at `(m, a) = (ctor c l, indTy)`. -/
def LRS.CtorDefEq (IH : LogRel Γ n) (M N A : SExpr) (c : Name) (l : List (WShape n)) : Prop :=
  LRS.IndTyRed Γ A ∧
  ∃ (ls : List SLevel) (Xs Ys Ts : List SExpr) (B : SExpr),
    Γ ⊢ .const c ls : Ts.foldr .forallE B ∧
    Γ ⊢ M ⤳* spine (.const c ls) Xs ∧
    Γ ⊢ N ⤳* spine (.const c ls) Ys ∧
    LRS.CtorArgsEq IH Ts Xs Ys l .nil .id .id

theorem LRS.CtorArgsEq.left {IH : LogRel Γ n} :
    CtorArgsEq IH Ts Xs Ys l ρ σ σ' → CtorArgsEq IH Ts Xs Xs l ρ σ σ := by
  intro H; induction H with
  | nil => exact .nil
  | cons h1 h2 h3 h4 _ ih =>
    obtain ⟨_, h1⟩ := h1
    exact .cons ⟨_, h1.hasType.1⟩ (fun a ha ht => IH.left_ty (h2 a ha ht)) h3.hasType.1
      (fun a ha hp => IH.left (h4 a ha hp)) ih

theorem LRS.CtorArgsEq.symm {IH : LogRel Γ n} :
    CtorArgsEq IH Ts Xs Ys l ρ σ σ' → CtorArgsEq IH Ts Ys Xs l ρ σ' σ := by
  intro H; induction H with
  | nil => exact .nil
  | cons h1 h2 h3 h4 _ ih =>
    obtain ⟨_, h1⟩ := h1
    refine .cons ⟨_, h1.symm⟩ (fun a ha ht => IH.symm_ty (h2 a ha ht)) ?_
      (fun a ha hp => ?_) ih
    · exact h1.defeqDF h3.symm
    · exact IH.conv (h2 a ha hp.isType) (IH.symm (h4 a ha hp))

theorem LRS.CtorDefEq.left {IH : LogRel Γ n} :
    CtorDefEq IH M N A c l → CtorDefEq IH M M A c l
  | ⟨hA, ls, Xs, _, Ts, B, hc, hM, _, h⟩ => ⟨hA, ls, Xs, Xs, Ts, B, hc, hM, hM, h.left⟩

theorem LRS.CtorDefEq.symm {IH : LogRel Γ n} :
    CtorDefEq IH M N A c l → CtorDefEq IH N M A c l
  | ⟨hA, ls, Xs, Ys, Ts, B, hc, hM, hN, h⟩ => ⟨hA, ls, Ys, Xs, Ts, B, hc, hN, hM, h.symm⟩

/-- A constructor spine is weak-head normal: no `beta` (head is a `const`), no `extra`
(pattern heads are `symb`, see `pat_arity`), and `app` needs a reducible prefix spine.
Needed for `trans` (determinism) and for the pat leaf (syntactic `MatchesS`). -/
theorem WHNF.ctorSpine (hc : Params.classify c = some (.ctor k)) (Xs : List SExpr) :
    WHNF Γ (spine (.const c ls) Xs) := sorry

theorem LRS.CtorArgsEq.trans {IH : LogRel Γ n} :
    CtorArgsEq IH Ts Xs Ys l ρ σ σ' → CtorArgsEq IH Ts Ys Zs l ρ σ' σ'' →
    CtorArgsEq IH Ts Xs Zs l ρ σ σ'' := by
  intro H1 H2; induction H1 generalizing Zs σ'' with
  | nil => cases H2; exact .nil
  | cons h1 h2 h3 h4 _ ih =>
    obtain ⟨_, h1⟩ := h1
    cases H2 with | cons g1 g2 g3 g4 g5
    obtain ⟨_, g1⟩ := g1
    refine .cons ⟨_, h1.trans' g1⟩ (fun a ha ht => IH.trans_ty (h2 a ha ht) (g2 a ha ht)) ?_
      (fun a ha hp => ?_) (ih g5)
    · exact h3.trans (h1.symm.defeqDF g3)
    · exact IH.trans (h4 a ha hp) (IH.conv (IH.symm_ty (h2 a ha hp.isType)) (g4 a ha hp))

theorem LRS.CtorDefEq.trans {IH : LogRel Γ n} (hc : Params.classify c = some (.ctor k)) :
    CtorDefEq IH M₁ M₂ A c l → CtorDefEq IH M₂ M₃ A c l → CtorDefEq IH M₁ M₃ A c l
  | ⟨hA, ls, Xs, Ys, Ts, B, hc', hM₁, hM₂, h⟩, ⟨_, ls', Ys', Zs, _, _, _, hM₂', hM₃, h'⟩ => by
    have := hM₂.determ (WHNF.ctorSpine hc Ys) hM₂' (WHNF.ctorSpine hc Ys')
    sorry  -- spine injectivity: `spine (const c ls) Ys = spine (const c ls') Ys'` ⇒ `ls = ls' ∧ Ys = Ys'`,
           -- then `⟨hA, ls, Xs, Zs, Ts, B, hc', hM₁, hM₃, h.trans h'⟩`.

/-! ### The spine-generalised `const` statement (mirrors `LR.adequacy_Y`).

The spine arguments are *variables* of the constant's own type telescope, so that
argument relatedness (and validity of their type shapes) comes from `SubstWF`
exactly as in the `lamDF` case, rather than from an instantiated `LamDefEq`. -/

/-- `const c ls (bvar (k-1)) … (bvar 0)`. -/
def openSpine (c : Name) (ls : List SLevel) (k : Nat) : SExpr :=
  spine (.const c ls) ((List.range k).reverse.map .bvar)

/-- Telescope valuation: push the (reversed-spine) shapes `rargs` onto `.nil`. -/
def Valuation.ofRargs {n} (rargs : List (WShape n)) : Valuation :=
  rargs.foldr (fun x ρ => ρ.push x.T) .nil

theorem LR.adequacy_const_spine
    {c : Name} {ci} {ls : List SLevel} {Ts : List SExpr} {B : SExpr}
    (h1 : Params.env.constants c = some ci) (h2 : ls.length = ci.uvars)
    -- the constant's type, unfolded `k` binders (`Ts` closed telescope of the first `k` args)
    (hT : Γ₀ ⊢ (SExpr.mk ci.type).instL ls ≡ Ts.foldr .forallE B : .sort u)
    {rargs : List (WShape n)} (hk : rargs.length = Ts.length) {m : TShape}
    (hC : LE_Interp.Const c ls R rargs m)
    (hR : ∀ m e, R m e → LE_Interp (Valuation.ofRargs rargs) m e)
    -- IHs for the self-witnesses (the `adequacy_Y` measure): every `R m e` leaf is adequate
    (ihR : ∀ m e, R m e → ∀ {n'} {m' a' : WShape n'} {A},
      m ≤ m'.T → LE_Interp (Valuation.ofRargs rargs) a'.T A → m'.HasType a' →
      Γ₀ ⊢ e : A → Adequate Γ₀ Γ₀ .nil e e A m' a')
    {m' a : WShape n'} (le : m ≤ m'.T) (hA : LE_Interp (Valuation.ofRargs rargs) a.T B)
    (hmem : m'.HasType a) :
    Adequate Γ₀ (Ts.reverse ++ Γ₀) (Valuation.ofRargs rargs)
      (openSpine c ls rargs.length) (openSpine c ls rargs.length) B m' a := sorry

end Lean4Lean.SExpr
