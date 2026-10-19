import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Audit circ-3: the spine lemma's lam case (R9) needs, for each domain `T` of the constant's
own type telescope, an `env.below rank (rank c)` strong derivation of `T` in its telescope
context, to feed the WF IH (→ `ihA`) and `Adequate.cons` (→ `HA`). The only syntactic source is
`IsDefEqStrong.forallE_inv'` (SExpr.lean:1433) applied to `type_below`'s derivation; R4 does not
list it among the lemmas generalised to `E`. This file shows the `E`-version and the telescope
iteration are mechanical (no `hE`, no env lookups). `IsDefEqStrongE` is the PatLeafStmt2.lean copy.
No sorries. -/
namespace Lean4Lean.SExpr
variable [Params]

section
set_option hygiene false
local notation:65 Γ " ⊢ₑ " e1 " : " A:36 => IsDefEqStrongE Γ e1 e1 A
local notation:65 Γ " ⊢ₑ " e1 " ≡ " e2 " : " A:36 => IsDefEqStrongE Γ e1 e2 A
variable (E : VEnv)
inductive IsDefEqStrongE : List SExpr → SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ₑ A : .sort u → Γ ⊢ₑ .bvar i : A
  | symm : Γ ⊢ₑ e ≡ e' : A → Γ ⊢ₑ e' ≡ e : A
  | trans : Γ ⊢ₑ A : .sort u → Γ ⊢ₑ e₁ ≡ e₂ : A → Γ ⊢ₑ e₂ ≡ e₃ : A → Γ ⊢ₑ e₁ ≡ e₃ : A
  | trans' : Γ ⊢ₑ A ≡ B : .sort u → Γ ⊢ₑ B ≡ C : .sort v → Γ ⊢ₑ A ≡ C : .sort u
  | sort : Γ ⊢ₑ .sort l : .sort (.succ l)
  | const : E.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ₑ SExpr.mkInst ls ci.type : .sort u →
    (F : ∀ cl, CtorBundle c cl) →
    (∀ cl, Γ ⊢ₑ SExpr.mkInst ls ci.type ≡ (F cl).rhs ls : .sort (F cl).u) →
    Γ ⊢ₑ .const c ls : SExpr.mkInst ls ci.type
  | appDF : Γ ⊢ₑ A : .sort u → A::Γ ⊢ₑ B : .sort v →
    Γ ⊢ₑ f ≡ f' : .forallE A B → Γ ⊢ₑ a ≡ a' : A →
    Γ ⊢ₑ B.inst a ≡ B.inst a' : .sort v →
    Γ ⊢ₑ .app f a ≡ .app f' a' : B.inst a
  | lamDF : Γ ⊢ₑ A ≡ A' : .sort u → A::Γ ⊢ₑ B : .sort v →
    A::Γ ⊢ₑ body ≡ body' : B → A'::Γ ⊢ₑ body ≡ body' : B →
    Γ ⊢ₑ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF : Γ ⊢ₑ A ≡ A' : .sort u →
    A::Γ ⊢ₑ body ≡ body' : .sort v → A'::Γ ⊢ₑ body ≡ body' : .sort v →
    Γ ⊢ₑ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF : Γ ⊢ₑ A ≡ B : .sort u → Γ ⊢ₑ e1 ≡ e2 : A → Γ ⊢ₑ e1 ≡ e2 : B
  | beta : A::Γ ⊢ₑ e : B → Γ ⊢ₑ e' : A →
    Γ ⊢ₑ .app (.lam A e) e' : B.inst e' → Γ ⊢ₑ e.inst e' : B.inst e' →
    Γ ⊢ₑ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta : Γ ⊢ₑ e : .forallE A B → Γ ⊢ₑ .lam A (.app e.lift (.bvar 0)) : .forallE A B →
    Γ ⊢ₑ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel : Γ ⊢ₑ p : .sort .zero → Γ ⊢ₑ h : p → Γ ⊢ₑ h' : p → Γ ⊢ₑ h ≡ h' : p
  | extra : E.defeqs df → ls.length = df.uvars →
    Γ ⊢ₑ .mkInst ls df.lhs : .mkInst ls df.type →
    Γ ⊢ₑ .mkInst ls df.rhs : .mkInst ls df.type →
    Γ ⊢ₑ .mkInst ls df.lhs ≡ .mkInst ls df.rhs : .mkInst ls df.type
end

variable {E : VEnv}

theorem IsDefEqStrongE.hasTypeS (H : IsDefEqStrongE E Γ e1 e2 (.sort u)) :
    IsDefEqStrongE E Γ e1 e1 (.sort u) ∧ IsDefEqStrongE E Γ e2 e2 (.sort u) :=
  ⟨.trans .sort H H.symm, .trans .sort H.symm H⟩

/-- `IsDefEqStrong.forallE_inv'` (SExpr.lean:1433) for any `E`: same proof, no `E ≤ env`. -/
theorem IsDefEqStrongE.forallE_inv' (H : IsDefEqStrongE E Γ e1 e2 V)
    (eq : e1 = A.forallE B ∨ e2 = A.forallE B) :
    (∃ u, IsDefEqStrongE E Γ A A (.sort u)) ∧ ∃ v, IsDefEqStrongE E (A::Γ) B B (.sort v) := by
  induction H generalizing A B with
  | symm _ ih => exact ih eq.symm
  | trans _ _ _ _ ih1 ih2
  | trans' _ _ ih1 ih2
  | proofIrrel _ _ _ _ ih1 ih2 =>
    obtain eq | eq := eq
    · exact ih1 (.inl eq)
    · exact ih2 (.inr eq)
  | forallEDF h1 h2 h3 =>
    obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq
    · exact ⟨⟨_, h1.hasTypeS.1⟩, _, h2.hasTypeS.1⟩
    · exact ⟨⟨_, h1.hasTypeS.2⟩, _, h3.hasTypeS.2⟩
  | defeqDF _ _ _ ih2 => exact ih2 eq
  | beta _ _ _ _ _ _ _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih (.inr eq)
  | eta _ _ ih _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih (.inr eq)
  | extra _ _ _ _ ih1 ih2 =>
    obtain eq | eq := eq
    · exact ih1 (.inl eq)
    · exact ih2 (.inl eq)
  | _ => nomatch eq

/-- Every domain of a strongly typed syntactic Π-telescope, and its codomain, is strongly typed
in its own telescope context, in the SAME environment `E` (so the WF IH applies at that rank). -/
inductive TelStrongE (E : VEnv) : List SExpr → List SExpr → SExpr → Prop where
  | nil : IsDefEqStrongE E Γ B B (.sort v) → TelStrongE E Γ [] B
  | cons : IsDefEqStrongE E Γ T T (.sort u) → TelStrongE E (T :: Γ) Ts B →
      TelStrongE E Γ (T :: Ts) B

theorem IsDefEqStrongE.telescope : ∀ {Ts : List SExpr} {Γ B u},
    IsDefEqStrongE E Γ (Ts.foldr .forallE B) (Ts.foldr .forallE B) (.sort u) → TelStrongE E Γ Ts B
  | [], _, _, _, H => .nil H
  | T :: Ts, _, _, _, H => by
    obtain ⟨⟨_, hT⟩, _, hB⟩ := H.forallE_inv' (A := T) (B := Ts.foldr .forallE _) (.inl rfl)
    exact .cons hT (IsDefEqStrongE.telescope hB)

end Lean4Lean.SExpr
#print axioms Lean4Lean.SExpr.IsDefEqStrongE.forallE_inv'
#print axioms Lean4Lean.SExpr.IsDefEqStrongE.telescope
