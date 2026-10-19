import Lean4Lean.Experimental.ShapeLogRelAdequacy

/-! Refutation of C9/C11 (design κ): `LogRel.mono_r_1` is FALSE at `indTy` under κ as specified.

κ puts per-constructor codes `K` in the TYPE shape `indTy qs kI K`, types `ctor c l` by
`SpineTyped l (K c) ∧ params(l) ≤ qs`, relates the fields along `K c` (Exp2's `SpineDefEq`),
and defines `TyDefEq` at `indTy qs kI K` by the PARAMETERS along `kI` only (C11): nothing in
`TyDefEq (I Ps) (I Ps) (indTy qs kI K)` constrains `K`.  `mono_r_1` raises `a = indTy qs kI K` to
`a' = indTy qs kI K'` with `K ≤ K'`, given only `TyDefEq A A a'`; the field step along `K' c` then
demands the codomain `TyDefEq` at `f'.app p` (bigger than `f.app p`) which nothing supplies.

Instance (`box : {α : Type} → α → Box α`, `M = N = box Nat 0`, `A = Box Nat`):
  p := shape of the parameter `Nat`  (here `indTy`),  field shape `⊥`,
  K box  := k  = forallE type [(indTy, forallE ⊥    [])]   (field domain ⊥)
  K' box := k' = forallE type [(indTy, forallE type [])]   (field domain `type`)
Below: (1) the shape facts by `decide`; (2) the field step along `k'` is FALSE whenever the
parameter does not reduce to a sort (it forces `∃ u, Nat ⤳* sort u`), via Exp2's `SpineDefEq`
verbatim; (3) the same conjunct along `k` HOLDS from syntactic typing alone.  All other
conjuncts of the two `SpineDefEq`s coincide (step 2 is at `⊥`, `True` by `LogRel.bot`), and C11's
nil conjunct `TyDefEq A (Box Nat) (indTy qs kI _)` and `TyDefEq A A (indTy qs kI _)` do not
mention `K`.  So `DefEq M N A m a` holds, `m : a`, `m : a'`, `a ≤ a'`, `TyDefEq A A a'`, and
`DefEq M N A m a'` fails.  (The κ-level glue is argued: κ is not implemented.) -/

namespace Lean4Lean.SExpr
variable [Params]

-- Exp2_Spine.lean's definition, verbatim
def SpineDefEq (Γ : List SExpr) : ∀ {n}, List SExpr → List SExpr → SExpr →
    List (WShape n) → WShape (n+1) → Prop
  | _, [], [], _, [], _ => True
  | n, x :: xs, y :: ys, T, p :: ps, k =>
    ∀ (a₁ : WShape n) (f : WShapeFun n), k = .forallE a₁ f → p.HasType a₁ →
      ∃ A₁ A₂ u v, Γ ⊢ T ⤳* .forallE A₁ A₂ ∧ Γ ⊢ A₁ : .sort u ∧ A₁::Γ ⊢ A₂ : .sort v ∧
        Γ ⊢ x ≡ y : A₁ ∧
        (LR Γ).DefEq x y A₁ p a₁ ∧
        (LR Γ).TyDefEq (A₂.inst x) (A₂.inst y) (f.app p) ∧
        (∃ w, Γ ⊢ A₂.inst x ≡ A₂.inst y : .sort w) ∧
        SpineDefEq Γ xs ys (A₂.inst x) ps ((f.app p).lift (n+1))
  | _, _, _, _, _, _ => False

/-! (1) shape facts (codes at level 2, fields at level 1, as in Exp2) -/
def kSmall : Shape 2 := ShapeS.forallE (.sort true) [(.indTy, ShapeS.forallE Shape0.bot [])]
def kBig   : Shape 2 := ShapeS.forallE (.sort true) [(.indTy, ShapeS.forallE (Shape0.sort true) [])]
example : kSmall ≤ kBig := by decide
example : Shape.hasType kSmall (.sort true) = true := by decide   -- both codes are TYPED codes,
example : Shape.hasType kBig (.sort true) = true := by decide     -- so typing K does not help
example : Shape.hasType (n := 1) .indTy (.sort true) = true := by decide  -- p : type (1st binder)
-- 2nd field `⊥` typed at both field domains (`⊥` resp. `type`, lifted to level 1)
example : Shape.hasType (n := 1) .bot .bot = true := by decide
example : Shape.hasType (n := 1) .bot (.sort true) = true := by decide
-- the codomain codes at the parameter's shape `indTy` (equal up to ≤ both ways)
def cSmall : Shape 1 := ShapeS.forallE Shape0.bot []
def cBig : Shape 1 := ShapeS.forallE (Shape0.sort true) []
example : ShapeFun.app (n := 1) [(.indTy, cSmall)] .indTy ≤ cSmall ∧
    cSmall ≤ ShapeFun.app (n := 1) [(.indTy, cSmall)] .indTy := by decide
example : ShapeFun.app (n := 1) [(.indTy, cBig)] .indTy ≤ cBig ∧
    cBig ≤ ShapeFun.app (n := 1) [(.indTy, cBig)] .indTy := by decide
example : cSmall ≤ cBig ∧ ¬ cBig ≤ cSmall := by decide

/-! (2) along the bigger code the parameter must reduce to a sort -/
theorem tyDefEq_forallE_sort_dom {Γ : List SExpr} {M B F : SExpr} {g : WShapeFun 0}
    (h : (LR Γ (n := 1)).TyDefEq M M (WShape.forallE (WShape.sort true) g))
    (hM : Γ ⊢ M ⤳* .forallE B F) : ∃ u, Γ ⊢ B ⤳* .sort u := by
  rw [LR_succ] at h
  obtain ⟨B₁, F₁, B₂, F₂, u, v, r1, -, -, -, hValB, -⟩ :=
    (LRS.TyDefEq.forallE_iff (IH := LR Γ)).1 h
  cases r1.determ .forallE hM .forallE
  exact ((LR Γ).sort_iff_ty.1 hValB).imp fun _ h => h.1

theorem indTy_not_whr_sort {Γ : List SExpr} {I : Name} {ls : List SLevel} {k : Nat} {u}
    (hI : Params.classify I = some (.indTy k)) : ¬ Γ ⊢ .const I ls ⤳* .sort u := fun h =>
  nomatch (WHNF.indTySpine (Γ := Γ) (ls := ls) hI []).whRedS h

/-- The field step of `SpineDefEq` along a code whose codomain at the parameter's shape has a
`type` domain is unsatisfiable when the parameter is an inductive type (e.g. `Nat`). -/
theorem spine_bigCode_false {Γ : List SExpr} {x y z w A₁ A₂ F : SExpr} {I : Name}
    {ls : List SLevel} {k : Nat} {p q : WShape 1} {a₁ : WShape 1} {f : WShapeFun 1}
    {g : WShapeFun 0}
    (hI : Params.classify I = some (.indTy k))
    (hx : A₂.inst x = .forallE (.const I ls) F)
    (hp : p.HasType a₁) (hf : f.app p = WShape.forallE (WShape.sort true) g) :
    ¬ SpineDefEq Γ [x, z] [y, w] (.forallE A₁ A₂) [p, q] (WShape.forallE a₁ f) := by
  intro h
  obtain ⟨A₁', A₂', u, v, rT, -, -, -, -, d2, -, -⟩ := h a₁ f rfl hp
  cases WHNF.forallE.whRedS rT
  rw [hf] at d2
  have := (LR Γ).left_ty d2
  rw [hx] at this
  obtain ⟨u, hu⟩ := tyDefEq_forallE_sort_dom this .rfl
  exact indTy_not_whr_sort hI hu

/-! (3) along the smaller code the same conjunct holds from syntactic typing alone -/
theorem tyDefEq_forallE_bot_dom {Γ : List SExpr} {B F : SExpr} {u v}
    (hB : Γ ⊢ B : .sort u) (hF : B::Γ ⊢ F : .sort v) :
    (LR Γ (n := 1)).TyDefEq (.forallE B F) (.forallE B F) (WShape.forallE .bot .bot) := by
  rw [LR_succ]
  refine (LRS.TyDefEq.forallE_iff (IH := LR Γ)).2
    ⟨B, F, B, F, u, v, .rfl, .rfl, hB, hF, trivial, ?_, ?_⟩
  · intro _ _ _ _ _ _; simp only [WShapeFun.bot_app]; exact ⟨trivial, trivial⟩
  · intro _ _ _ _ _; simp only [WShapeFun.bot_app]; exact trivial

end Lean4Lean.SExpr
