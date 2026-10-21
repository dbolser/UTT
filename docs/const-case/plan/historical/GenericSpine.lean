import Lean4Lean.Experimental.ShapeLogRelAdequacy
-- historical: typechecked at 3c35f59, before the typed logical relation (docs/const-case/PLAN.md D6, landed by R1+R2); no longer compiles.
/-! Refuter (proof, lens clause), experiment 2.
ClauseA's `SpineDefEq` is stated over the CONCRETE tower `LR Γ`, and its `conv`/`symm`/`trans`
use `LRS.TyDefEq.forallE_iff` at level `n+1` plus `LR.TyDefEq.lift (Nat.le_succ n)` (a theorem
about the tower, proven from `LR.lift_succ_aux` after `LR` is defined).  In the wiring the clause
is a case of `LRS.DefEq IH` and the fields are proven inside `def LRS (IH : LogRel Γ n)`
(ShapeLogRel.lean ~5664) for an ABSTRACT `IH`.  Here is the same clause over an abstract `IH`.
`conv`/`symm`/`trans` go through ONLY with the extra hypothesis `hl` (IH-level `TyDefEq` at `s`
gives `LRS.TyDefEq IH` at `s.lift (n+1)`), which is not a `LogRel` field; `left` and `mono`
need nothing extra.  `hl_LR` shows `hl` is exactly the ⇐ half of `LR.TyDefEq.lift` for the
concrete tower.  No sorries. -/
namespace Lean4Lean.SExpr
variable [Params]

def SpineDefEqG {Γ : List SExpr} {n : Nat} (IH : LogRel Γ n) : List SExpr → List SExpr → SExpr →
    List (WShape n) → WShape (n+1) → Prop
  | [], [], _, [], _ => True
  | x :: xs, y :: ys, T, p :: ps, k =>
    ∀ (a₁ : WShape n) (f : WShapeFun n), k = .forallE a₁ f → p.HasType a₁ →
      ∃ A₁ A₂ u v, Γ ⊢ T ⤳* .forallE A₁ A₂ ∧ Γ ⊢ A₁ : .sort u ∧ A₁::Γ ⊢ A₂ : .sort v ∧
        Γ ⊢ x ≡ y : A₁ ∧
        IH.TyDefEq A₁ A₁ a₁ ∧
        IH.DefEq x y A₁ p a₁ ∧
        IH.TyDefEq (A₂.inst x) (A₂.inst y) (f.app p) ∧
        SpineDefEqG IH xs ys (A₂.inst x) ps ((f.app p).lift (n+1))
  | _, _, _, _, _ => False

/-- The inter-level hypothesis the generic proofs need. Not a `LogRel` field. -/
def LiftHyp {Γ : List SExpr} {n : Nat} (IH : LogRel Γ n) : Prop :=
  ∀ {M N : SExpr} {s : WShape n}, s.HasType .type → IH.TyDefEq M N s →
    LRS.TyDefEq IH M N (s.lift (n+1))

theorem hl_LR {Γ : List SExpr} {n : Nat} : LiftHyp (LR Γ (n := n)) :=
  fun hs h => (LR.TyDefEq.lift (Nat.le_succ n) hs).2 h

theorem lift_app_typeG {n} {f : WShapeFun n} {p : WShape n}
    (h : (f.app p).HasType .type) : ((f.app p).lift (n+1)).HasType .type := by
  have := (WShape.HasType.lift (Nat.le_succ n)).2 h; rwa [WShape.lift_sort] at this

theorem code_codG {a₁ : WShape n} {f : WShapeFun n} (hk : (WShape.forallE a₁ f).HasType .type)
    (hp : p.HasType a₁) : (f.app p).HasType .type := by
  obtain ⟨_, htpi, _⟩ := WShape.HasType.forallE_l.1 hk
  exact (WShape.HasTypePi.iff.1 htpi.toType).2 _ hp

theorem SpineDefEqG.conv {Γ : List SExpr} {n : Nat} {IH : LogRel Γ n} (hl : LiftHyp IH)
    {xs : List SExpr} : ∀ {ys : List SExpr} {T T'} {ps : List (WShape n)} {k : WShape (n+1)},
    k.HasType .type → LRS.TyDefEq IH T T' k →
    SpineDefEqG IH xs ys T' ps k → SpineDefEqG IH xs ys T ps k := by
  induction xs with
  | nil => intro ys T T' ps k _ _ h; cases ys <;> cases ps <;> simp_all [SpineDefEqG]
  | cons x xs ih =>
    intro ys T T' ps k hk hTT' h
    cases ys with | nil => simp [SpineDefEqG] at h | cons y ys
    cases ps with | nil => simp [SpineDefEqG] at h | cons p ps
    intro a₁ f hkf hp; subst hkf
    obtain ⟨A₁, A₂, u, v, rT', hA₁, hA₂, hxy, t1, d1, d2, d4⟩ := h _ _ rfl hp
    obtain ⟨B₁, F₁, B₂, F₂, u', v', rT, rT'', hBB, hFF, hValB, hEdge⟩ :=
      (LRS.TyDefEq.forallE_iff (IH := IH)).1 hTT'
    cases rT'.determ .forallE rT'' .forallE
    have hfp := code_codG hk hp
    have d1' := IH.conv (IH.symm_ty hValB) d1
    have hxB : Γ ⊢ x ≡ y : B₁ := hBB.symm.defeqDF hxy
    have piL := hEdge.1 hp hxB d1'
    have piD := hEdge.2 hp hxB.hasType.1 (IH.left d1')
    exact ⟨B₁, F₁, u', v', rT, hBB.hasType.1, hFF.hasType.1, hxB, IH.left_ty hValB, d1', piL.1,
      ih (lift_app_typeG hfp) (hl hfp piD) d4⟩

theorem SpineDefEqG.symm {Γ : List SExpr} {n : Nat} {IH : LogRel Γ n} (hl : LiftHyp IH)
    {xs : List SExpr} : ∀ {ys : List SExpr} {T} {ps : List (WShape n)} {k : WShape (n+1)},
    k.HasType .type → SpineDefEqG IH xs ys T ps k → SpineDefEqG IH ys xs T ps k := by
  induction xs with
  | nil => intro ys T ps k _ h; cases ys <;> cases ps <;> simp_all [SpineDefEqG]
  | cons x xs ih =>
    intro ys T ps k hk h
    cases ys with | nil => simp [SpineDefEqG] at h | cons y ys
    cases ps with | nil => simp [SpineDefEqG] at h | cons p ps
    intro a₁ f hkf hp; subst hkf
    obtain ⟨A₁, A₂, u, v, rT, hA₁, hA₂, hxy, t1, d1, d2, d4⟩ := h _ _ rfl hp
    have hfp := code_codG hk hp
    refine ⟨A₁, A₂, u, v, rT, hA₁, hA₂, hxy.symm, t1, IH.symm d1, IH.symm_ty d2, ?_⟩
    exact SpineDefEqG.conv hl (lift_app_typeG hfp) (hl hfp (IH.symm_ty d2))
      (ih (lift_app_typeG hfp) d4)

theorem SpineDefEqG.trans {Γ : List SExpr} {n : Nat} {IH : LogRel Γ n} (hl : LiftHyp IH)
    {xs : List SExpr} : ∀ {ys zs : List SExpr} {T} {ps : List (WShape n)} {k : WShape (n+1)},
    k.HasType .type →
    SpineDefEqG IH xs ys T ps k → SpineDefEqG IH ys zs T ps k → SpineDefEqG IH xs zs T ps k := by
  induction xs with
  | nil => intro ys zs T ps k _ h1 h2; cases ys <;> cases zs <;> cases ps <;> simp_all [SpineDefEqG]
  | cons x xs ih =>
    intro ys zs T ps k hk h1 h2
    cases ys with | nil => simp [SpineDefEqG] at h1 | cons y ys
    cases zs with | nil => simp [SpineDefEqG] at h2 | cons z zs
    cases ps with | nil => simp [SpineDefEqG] at h1 | cons p ps
    intro a₁ f hkf hp; subst hkf
    obtain ⟨A₁, A₂, u, v, rT, hA₁, hA₂, hxy, t1, d1, d2, d4⟩ := h1 _ _ rfl hp
    obtain ⟨A₁', A₂', u', v', rT', hA₁', hA₂', hyz, -, e1, e2, e4⟩ := h2 _ _ rfl hp
    cases rT.determ .forallE rT' .forallE
    have hfp := code_codG hk hp
    refine ⟨A₁, A₂, u, v, rT, hA₁, hA₂, hxy.trans hyz, t1, IH.trans d1 e1, IH.trans_ty d2 e2, ?_⟩
    exact ih (lift_app_typeG hfp) d4
      (SpineDefEqG.conv hl (lift_app_typeG hfp) (hl hfp d2) e4)

end Lean4Lean.SExpr

#print axioms Lean4Lean.SExpr.SpineDefEqG.symm
#print axioms Lean4Lean.SExpr.SpineDefEqG.trans
#print axioms Lean4Lean.SExpr.hl_LR
