import Lean4Lean.Experimental.ShapeLogRelAdequacy
namespace Lean4Lean.SExpr
variable [Params]

/-! Experiment 3: the pieces of the fuel/measure design.
(a) `IsDefEqStrong'.const` with a typing premise for the closed fixed subterms of the RHS of
    every rule headed by `c`, except bare constants of the same recursive block; legal inductive.
(b) `induction hM` on `LE_Interp ρ m (const c ls)` gives a usable IH through `a7`.
(c) statement of the spine-generalised const lemma. -/

/-- Closed subterms `e` of an RHS (the `.fixed` leaves). -/
def _root_.Lean4Lean.Pattern.RHS.fixedLeaves {p : Pattern} : p.RHS → List VExpr
  | .fixed e _ => [e]
  | .var _ => []
  | .app f a => f.fixedLeaves ++ a.fixedLeaves

/-- A block relation on constants (e.g. mutual recursors); only its decidability matters here. -/
def SameBlock (Block : Name → Name → Prop) (c : Name) : VExpr → Prop
  | .const c' _ => Block c c'
  | _ => False

section
set_option hygiene false
local notation:65 (priority := high) Γ " ⊢ " e1 " : " A:36 => IsDefEqStrong' Γ e1 e1 A
local notation:65 (priority := high) Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEqStrong' Γ e1 e2 A
variable (Block : Name → Name → Prop)
inductive IsDefEqStrong' : List SExpr → SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ A : .sort u → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ A : .sort u → Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  | sort : Γ ⊢ .sort l : .sort (.succ l)
  | const : Params.env.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ (SExpr.mk ci.type).instL ls : .sort u →
    (F : ∀ cl, CtorBundle c cl) →
    (∀ cl, Γ ⊢ (SExpr.mk ci.type).instL ls ≡ (F cl).rhs ls : .sort (F cl).u) →
    -- NEW: typing of the closed fixed subterms of every rule headed by `c`, except same-block
    -- bare constants (those are handled by the local induction on the model derivation).
    (Ts : ∀ p (r : p.RHS × p.Check), Params.Pat p r → p.head = c → VExpr → SExpr) →
    (∀ p r (hP : Params.Pat p r) (hc : p.head = c), ∀ e ∈ r.1.fixedLeaves,
      ¬ SameBlock Block c e → Γ ⊢ (SExpr.mk e).instL ls : Ts p r hP hc e) →
    Γ ⊢ .const c ls : (SExpr.mk ci.type).instL ls
  | appDF : Γ ⊢ A : .sort u →
    Γ ⊢ f ≡ f' : .forallE A B → Γ ⊢ a ≡ a' : A →
    Γ ⊢ B.inst a ≡ B.inst a' : .sort v →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
end

/-- (b): the model-derivation induction in the const case. The IH `ih` is available for every
`R m e`, i.e. for every closed fixed subterm of every unfolding, at a strictly smaller derivation. -/
example (P : ∀ {ρ m M}, LE_Interp ρ m M → Prop)
    (hM : LE_Interp ρ m (.const c ls)) : True := by
  generalize eq : SExpr.const c ls = M at hM
  induction hM with
  | const h1 h2 h3 h4 h5 h6 h7 ih5 ih7 =>
    -- `ih7 : ∀ m e (h : R m e), const c ls = e → ...` : IH for every RHS closed subterm (via a7)
    -- `ih5` : IH for the type's interpretation.
    have := @ih7; have := @ih5
    trivial
  | _ => trivial

/-- (c): the spine-generalised statement that the const case reduces to, by induction on the
`Const` derivation. `ps` are typed shapes dominating `rargs`; `xs, xs'` the syntactic spine
related at `ps`; `T` the telescope type of `apps c xs` with its type-validity at `a`. -/
theorem const_spine {n} {rargs : List (WShape n)} {m' : TShape}
    (hC : LE_Interp.Const c ls (LE_Interp ρ) rargs m')
    {k} (ps : List (WShape k)) (hps : List.Forall₂ (fun (r : WShape n) (p : WShape k) => r.T ≤ p.T) rargs ps)
    (xs xs' As : List SExpr) (a : WShape k) (m : WShape k) (T : SExpr)
    (hrel : List.Forall₂ (fun (x : SExpr × SExpr × SExpr) (p : WShape k) =>
      Γ₀ ⊢ x.1 ≡ x.2.1 : x.2.2 ∧ ∃ ap, (LR Γ₀).DefEq x.1 x.2.1 x.2.2 p ap)
      (xs.zip (xs'.zip As)) ps)
    (hle : m.T ≤ m') (hmem : m.HasType a) (hT : (LR Γ₀).TyDefEq T T a) :
    (LR Γ₀).DefEq (xs.foldr (fun a acc => .app acc a) (.const c ls))
      (xs'.foldr (fun a acc => .app acc a) (.const c ls)) T m a := by
  sorry

end Lean4Lean.SExpr
