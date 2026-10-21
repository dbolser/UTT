import Lean4Lean.Experimental.ShapeLogRelAdequacy
namespace Lean4Lean.SExpr
variable [Params]

/-! Refuter check of claim C3: does `mono_l` for C's clause need an *explicitly stored*
valuation?  The analyst says the valuation transport goes the wrong way for
`LE_Interp.mono_l`.  Test: C's clause with the field quantifier weakened to
`∀ q ≤ p, q.HasType a → …` (the part of the restatement that IS needed), valuation still
`ρ.push p.T` (no stored valuation), and prove `mono_l` for `l ≤ l'` pointwise. -/

inductive LRS.CtorArgsEq' (IH : LogRel Γ n) :
    List SExpr → List SExpr → List SExpr → List (WShape n) → Valuation → Subst → Subst → Prop
  | nil : CtorArgsEq' IH [] [] [] [] ρ σ σ'
  | cons {T Ts X Xs Y Ys} {p : WShape n} {l ρ σ σ'} :
    (∃ u, Γ ⊢ T.subst σ ≡ T.subst σ' : .sort u) →
    (∀ a : WShape n, LE_Interp ρ a.T T → a.HasType .type →
      IH.TyDefEq (T.subst σ) (T.subst σ') a) →
    Γ ⊢ X ≡ Y : T.subst σ →
    (∀ a : WShape n, LE_Interp ρ a.T T → ∀ q : WShape n, q ≤ p → q.HasType a →
      IH.DefEq X Y (T.subst σ) q a) →
    CtorArgsEq' IH Ts Xs Ys l (ρ.push p.T) (σ.cons X) (σ'.cons Y) →
    CtorArgsEq' IH (T :: Ts) (X :: Xs) (Y :: Ys) (p :: l) ρ σ σ'

/-- `mono_l` for the clause, generalised over a smaller valuation: NO stored valuation needed.
The validity hypothesis of the smaller clause (`LE_Interp ρ`) is transported to the larger
one (`LE_Interp ρ'`) by `LE_Interp.mono_l`, which is exactly its direction. -/
theorem LRS.CtorArgsEq'.mono_l {IH : LogRel Γ n} {l' : List (WShape n)} {ρ'}
    (H : CtorArgsEq' IH Ts Xs Ys l' ρ' σ σ') :
    ∀ {l : List (WShape n)} {ρ : Valuation}, List.Forall₂ (· ≤ ·) l l' → ρ.LE ρ' →
      CtorArgsEq' IH Ts Xs Ys l ρ σ σ' := by
  induction H with
  | nil => intro l ρ hl _; cases hl; exact .nil
  | cons h1 h2 h3 h4 _ ih =>
    intro l ρ hl hρ
    cases hl with | cons hp hl' =>
    exact .cons h1 (fun a ha ht => h2 a (ha.mono_l hρ) ht) h3
      (fun a ha q hq hqa => h4 a (ha.mono_l hρ) q (hq.trans hp) hqa)
      (ih hl' (Valuation.LE.push.2 ⟨hρ, hp.T⟩))

/-- The instance actually needed by `LogRel.mono_l` at `(ctor c l, indTy)`: same base valuation. -/
theorem LRS.CtorArgsEq'.mono_l_nil {IH : LogRel Γ n} {l l' : List (WShape n)}
    (hl : List.Forall₂ (· ≤ ·) l l')
    (H : CtorArgsEq' IH Ts Xs Ys l' .nil σ σ') : CtorArgsEq' IH Ts Xs Ys l .nil σ σ' :=
  H.mono_l hl .rfl

/-! Sanity: the analyst's stated direction `LE_Interp (push p'.T) → LE_Interp (push p.T)`
(larger valuation to smaller) is indeed NOT what `LE_Interp.mono_l` gives — but it is also
not what `mono_l` needs. -/
#check @LE_Interp.mono_l   -- ρ.LE ρ' → LE_Interp ρ m M → LE_Interp ρ' m M
#check @Valuation.LE.push

end Lean4Lean.SExpr
