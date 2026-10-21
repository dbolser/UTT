import Lean4Lean.Experimental.ShapeLogRelAdequacy

/-! Lens 2 experiment: type-shape reconciliation for parametric constructor fields.

`LR.field_retype` is the consumer-side move at the `pat` leaf: a field `x` of the matched
constructor spine is related (producer side) at `(p, a)` with its type written with the
*constructor's* parameter term `P'`; the minor premise consumes it at `(p'', a₁)` with the
type written with the *recursor's* parameter term `P` (`p''` is the `HasDom`-lowered point,
`a₁` the minor's domain shape).  The lemma shows the gap closes with the EXISTING `LogRel`
fields and shape algebra as soon as

  (i)  both type shapes `a`, `a₁` are bounded by ONE parameter shape `q`     (`ha`, `ha₁`),
  (ii) `P` is LR-valid at every shape below `q`                             (`hT`), and
  (iii) `P' ≡ P` is LR-related at `a`                                        (`hPP'`).

(ii) is exactly what the recursor spine's `Subst1` entry for the parameter gives
(`LR.Subst1.tyValid_below` below).  (i) and (iii) are what neither design A nor design C
provides today: in both, `a ≤ q'` (the constructor's own parameter shape, independent of
`q` in `LE_Interp.Matches.app`), and `TyDefEq P' P _` is not stored anywhere (A stores only
the *syntactic* `P ≡ P'` via `SynSpine`; C stores `IndTyRed`).  Without (i) the join
`a ⊔ a₁` need not exist (`Compat` fails) and `hT` cannot be applied at it; without (iii)
the `conv` step is unavailable.  Both become available once `indTy` carries the parameter
shapes (and the parameter relatedness lives in `TyDefEq` at `indTy qs …`). -/

namespace Lean4Lean.SExpr
variable [Params]

theorem LR.field_retype {n} {q a a₁ p p'' : WShape n} {x x' P P' : SExpr}
    (ha : a ≤ q) (ha₁ : a₁ ≤ q)
    (hp : p.HasType a) (hp'' : p''.HasType a₁) (hle : p'' ≤ p)
    (hT : ∀ m : WShape n, m ≤ q → m.HasType .type → (LR Γ₀).TyDefEq P P m)
    (hPP' : (LR Γ₀).TyDefEq P' P a)
    (h : (LR Γ₀).DefEq x x' P' p a) :
    (LR Γ₀).DefEq x x' P p'' a₁ := by
  have h1 : (LR Γ₀).DefEq x x' P p a := (LR Γ₀).conv hPP' h
  have hC : a.Compat a₁ := WShape.Compat.iff.2 ⟨q, ha, ha₁⟩
  have hJ := WShape.Join.mk hC
  have ⟨hj1, hj2⟩ := hJ.le
  have hjq : a.join a₁ ≤ q := (hJ q).2 ⟨ha, ha₁⟩
  have hjt : (a.join a₁).HasType .type := hp.isType.join' hJ hp''.isType
  have hpj : p.HasType (a.join a₁) := WShape.HasType.mono_r hj1 hjt hp
  have hp''j : p''.HasType (a.join a₁) := WShape.HasType.mono_r hj2 hjt hp''
  have h2 := (LR Γ₀).mono_r_1 hj1 hp hpj (hT _ hjq hjt) h1
  have h3 := (LR Γ₀).mono_l hle hp''j hpj h2
  exact (LR Γ₀).mono_r_2 hj2 hp'' hjt h3

/-- Hypothesis (ii) of `field_retype` is exactly the recursor spine's `Subst1` entry for the
parameter variable (valuation entry `q`, declared type `A₀` a sort): `P` is LR-valid as a type
at every `m ≤ q`. -/
theorem LR.Subst1.tyValid_below {n} {q : WShape n} {P P' A₀ A A' : SExpr} {ρ : Valuation}
    (h : LR.Subst1 Γ₀ P P' A₀ A A' (ρ.push q.T))
    (hA₀ : LE_Interp (ρ.push q.T) (WShape.sort true : WShape n).T A₀)
    {m : WShape n} (hm : m ≤ q) (hmt : m.HasType (.sort true)) : (LR Γ₀).TyDefEq P P m :=
  (LR Γ₀).left_ty <| (LR Γ₀).toType <| (h.2 _ hA₀).2 (LE_Interp.bvar0.mono hm.T) hmt

/-- The constructor-side parameter shape `q'` and the recursor-side one `q` are independent in
the shape model: `LE_Interp.Matches.app` accepts any `q'` in the ctor sub-match and any `q` in
the recursor's own argument list (`pat_simple` shape `app (varN rec 4) (varN cons 3)`). -/
example {n} (rec cons : Name) (q M mn mc : WShape (n+1)) (q' x xs : WShape n) :
    ∃ m, LE_Interp.Matches (.app (.varN (.const rec) 4) (.varN (.const cons) 3)) rec
      (WShape.ctor' cons [q', x, xs] :: [mc, mn, M, q]) m :=
  ⟨_, .app (.var (.var (.var (.var .const)))) (.var (.var (.var .const)))⟩

/-- A shape of the recursor's parameter variable under the recursor valuation is bounded by the
valuation entry (`bvar_iff`); this is the only constraint the model places on the minor
premise's domain shape `a₁`. -/
example {ρ : Valuation} {q : TShape} {a₁ : TShape} (h : LE_Interp (ρ.push q) a₁ (.bvar 0)) :
    a₁ ≤ q := LE_Interp.bvar_iff.1 h

end Lean4Lean.SExpr
