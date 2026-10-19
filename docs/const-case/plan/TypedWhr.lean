import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Synthesizer probes for decision D6 (typed reductions), against HEAD 3c35f59 (/tmp/utt-snap6).

(1) `TyDefEq_forallE_typed`: relating two Π types at a Π type-shape forces the TYPED
    equation of their domains.  So the pat-leaf conversion `motive (c Zs) ~ motive x` at a
    Π result shape (e.g. `motive := fun t => P t → N`) needs `Γ ⊢ P (c Zs) ≡ P x : sort u`.
(2) `inst_congr_beta`: typed instantiation congruence WITHOUT `⊢ Γ`, via `beta`.  Shows the
    codomain conversions inside a typed `conv` do not need a well-formed-context index.
(3) `LamDefEq.whr_typed`: the (lam, forallE) case of a TYPED `whr` field goes through,
    given a typed ambient-type equation `Γ ⊢ A ≡ forallE A₁ A₂ : sort w` (to be stored in the
    clause) and the typed `whr` of the level below.  No `⊢ Γ` needed: the `M b` side is
    obtained by `appDF` with the argument pair `(a, b)`.
No sorries. -/
namespace Lean4Lean.SExpr
variable [Params]

theorem TyDefEq_forallE_typed {Γ : List SExpr} {n} (IH : LogRel Γ n) {b : WShape n}
    {f : WShapeFun n} {B₁ B₂ F₁ F₂ : SExpr}
    (h : LRS.TyDefEq IH (.forallE B₁ F₁) (.forallE B₂ F₂) (WShape.forallE b f)) :
    ∃ u, Γ ⊢ B₁ ≡ B₂ : .sort u := by
  obtain ⟨_, _, _, _, u, _, r1, r2, hB, _⟩ := (LRS.TyDefEq.forallE_iff).1 h
  cases WHNF.forallE.whRedS r1; cases WHNF.forallE.whRedS r2; exact ⟨u, hB⟩

theorem inst_congr_beta {Γ : List SExpr} {B F F' a : SExpr} {u v}
    (hB : Γ ⊢ B : .sort u) (hF : B::Γ ⊢ F ≡ F' : .sort v) (ha : Γ ⊢ a : B) :
    Γ ⊢ F.inst a ≡ F'.inst a : .sort v := by
  have b1 : Γ ⊢ .app (.lam B F) a ≡ F.inst a : .sort v := .beta hF.hasType.1 ha
  have b2 : Γ ⊢ .app (.lam B F') a ≡ F'.inst a : .sort v := .beta hF.hasType.2 ha
  have l : Γ ⊢ .app (.lam B F) a ≡ .app (.lam B F') a : .sort v := .appDF (.lamDF hB hF) ha
  exact .trans (.symm b1) (.trans l b2)

theorem LRS.LamDefEq.whr_typed {Γ : List SExpr} {n} {IH : LogRel Γ n}
    (IHwhr : ∀ {M M' N N' A : SExpr} {m a : WShape n}, Γ ⊢ M ≡ M' : A → Γ ⊢ N ≡ N' : A →
      Γ ⊢ M ⤳* M' → Γ ⊢ N ⤳* N' → (IH.DefEq M N A m a ↔ IH.DefEq M' N' A m a))
    {M M' N N' A A₁ A₂ : SExpr} {w} {m : WShapeFun n} {a₁ : WShape n} {a₂ : WShapeFun n}
    (hA : Γ ⊢ A ≡ .forallE A₁ A₂ : .sort w)
    (hMt : Γ ⊢ M ≡ M' : A) (hNt : Γ ⊢ N ≡ N' : A)
    (hM : Γ ⊢ M ⤳* M') (hN : Γ ⊢ N ⤳* N') :
    LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ ↔ LRS.LamDefEq IH M' N' A₁ A₂ m a₁ a₂ := by
  have hMP : Γ ⊢ M ≡ M' : .forallE A₁ A₂ := hA.defeqDF hMt
  have hNP : Γ ⊢ N ≡ N' : .forallE A₁ A₂ := hA.defeqDF hNt
  -- typed reductions of `X a` and `X b` at `A₂.inst a`, from `X ≡ X'` and `a ≡ b`
  have tyL {X X' : SExpr} (h : Γ ⊢ X ≡ X' : .forallE A₁ A₂) {x y : SExpr} (hxy : Γ ⊢ x ≡ y : A₁) :
      Γ ⊢ X.app x ≡ X'.app x : A₂.inst x := .appDF h hxy.hasType.1
  have tyR {X X' : SExpr} (h : Γ ⊢ X ≡ X' : .forallE A₁ A₂) {x y : SExpr} (hxy : Γ ⊢ x ≡ y : A₁) :
      Γ ⊢ X.app y ≡ X'.app y : A₂.inst x :=
    .trans (.symm (.appDF (.symm h) hxy)) (.appDF h.hasType.2 hxy)
  constructor <;> intro ⟨pav, pae⟩ <;> refine ⟨fun x y p hp hxy a1 => ?_, fun x p hp hx a1 => ?_⟩
  · have ⟨d1, d2⟩ := pav hp hxy a1
    exact ⟨(IHwhr (tyL hMP hxy) (tyR hMP hxy) (.app hM) (.app hM)).1 d1,
           (IHwhr (tyL hNP hxy) (tyR hNP hxy) (.app hN) (.app hN)).1 d2⟩
  · exact (IHwhr (tyL hMP hx) (tyL hNP hx) (.app hM) (.app hN)).1 (pae hp hx a1)
  · have ⟨d1, d2⟩ := pav hp hxy a1
    exact ⟨(IHwhr (tyL hMP hxy) (tyR hMP hxy) (.app hM) (.app hM)).2 d1,
           (IHwhr (tyL hNP hxy) (tyR hNP hxy) (.app hN) (.app hN)).2 d2⟩
  · exact (IHwhr (tyL hMP hx) (tyL hNP hx) (.app hM) (.app hN)).2 (pae hp hx a1)

#print axioms TyDefEq_forallE_typed
#print axioms inst_congr_beta
#print axioms LRS.LamDefEq.whr_typed
end Lean4Lean.SExpr
