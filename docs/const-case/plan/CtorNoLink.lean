import Lean4Lean.Experimental.ShapeLogRelAdequacy
namespace Lean4Lean.SExpr
variable [Params]

/-! Design C's clause (docs/const-case/CtorClause.lean, copied verbatim, but over HEAD's
`SExpr.spine`).  Check: the clause relates the term's TYPE `A` to nothing but "some inductive
spine".  It is invariant under replacing `A` by ANY other `IndTyRed` type, so it cannot entail
any relation between `A`'s arguments (the recursor's parameters, at the pat leaf) and the
constructor spine's own parameter arguments.  Sorry-free. -/

def IndTyRedC (Γ : List SExpr) (A : SExpr) : Prop :=
  ∃ (I : Name) (ls : List SLevel) (As : List SExpr),
    Params.classify I = some (.indTy As.length) ∧ Γ ⊢ A ⤳* spine (.const I ls) As

inductive CtorArgsEqC (IH : LogRel Γ n) :
    List SExpr → List SExpr → List SExpr → List (WShape n) → Valuation → Subst → Subst → Prop
  | nil : CtorArgsEqC IH [] [] [] [] ρ σ σ'
  | cons {T Ts X Xs Y Ys} {p : WShape n} {l ρ σ σ'} :
    (∃ u, Γ ⊢ T.subst σ ≡ T.subst σ' : .sort u) →
    (∀ a : WShape n, LE_Interp ρ a.T T → a.HasType .type →
      IH.TyDefEq (T.subst σ) (T.subst σ') a) →
    Γ ⊢ X ≡ Y : T.subst σ →
    (∀ a : WShape n, LE_Interp ρ a.T T → p.HasType a → IH.DefEq X Y (T.subst σ) p a) →
    CtorArgsEqC IH Ts Xs Ys l (ρ.push p.T) (σ.cons X) (σ'.cons Y) →
    CtorArgsEqC IH (T :: Ts) (X :: Xs) (Y :: Ys) (p :: l) ρ σ σ'

def CtorDefEqC (IH : LogRel Γ n) (M N A : SExpr) (c : Name) (l : List (WShape n)) : Prop :=
  IndTyRedC Γ A ∧
  ∃ (ls : List SLevel) (Xs Ys Ts : List SExpr) (B : SExpr),
    Γ ⊢ .const c ls : Ts.foldr .forallE B ∧
    Γ ⊢ M ⤳* spine (.const c ls) Xs ∧ Γ ⊢ N ⤳* spine (.const c ls) Ys ∧
    CtorArgsEqC IH Ts Xs Ys l .nil .id .id

/-- The clause at `A` follows from the clause at an unrelated `A'` plus `IndTyRed A`:
e.g. `major` related at `List α` (recursor side) is the same fact as `major` related at
`List Nat`, whatever the constructor spine's parameter `β` is. -/
theorem CtorDefEqC.retype_any {IH : LogRel Γ n} (hA : IndTyRedC Γ A)
    (H : CtorDefEqC IH M N A' c l) : CtorDefEqC IH M N A c l := ⟨hA, H.2⟩

end Lean4Lean.SExpr
