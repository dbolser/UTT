import Lean4Lean.Experimental.ShapeLogRelAdequacy

/-! Refutation of C14 (the fallback restriction `Params.CtorFieldsShapeClosed`).

Copy of /tmp/utt-exp/plan/params/Restrict.lean, repaired for HEAD 3c35f59 (HEAD now defines
`SExpr.spine` and `SExpr.args`; the local `spine` is dropped and the auto-bound `args` renamed
`as`). Definitions otherwise verbatim.

Finding: the "proof field" disjunct `∃ Γ, env.HasType univs Γ T (.sort .zero)` quantifies the
context existentially, so it holds for EVERY de Bruijn variable `T = bvar i`
(take `Γ = replicate (i+1) Prop`).  Hence every field whose type is a parameter passes, and the
restriction admits `List.cons`, `Option.some`, `Prod.mk`, `Sum.inl`, ... — exactly the
constructors C14 says it excludes. -/

namespace Lean4Lean.SExpr
variable [Params]

inductive ShapeClosed : SExpr → Prop
  | sort : ShapeClosed (.sort u)
  | closed : ClosedN T 0 → ShapeClosed T
  | indTy : Params.classify I = some (.indTy k) → ShapeClosed (spine (.const I ls) as)
  | forallE : ShapeClosed A → ShapeClosed B → ShapeClosed (.forallE A B)

def Params.CtorFieldsShapeClosed : Prop :=
  ∀ {c cl ci}, (cl matches .ctor .. | .etaCtor ..) → Params.classify c = some cl →
    Params.env.constants c = some ci →
    ∀ (I : Name) (Ts as : List VExpr),
      ci.type = Ts.foldr .forallE
        (as.foldr (fun A acc => acc.app A) (.const I (VLevel.params ci.uvars))) →
      ∀ T ∈ Ts, ShapeClosed (SExpr.mk T) ∨
        ∃ Γ, Params.env.HasType Params.univs Γ T (.sort .zero)

/-- Every variable is "a proposition in some context". -/
theorem bvar_isProp_somewhere (i : Nat) :
    ∃ Γ, Params.env.HasType Params.univs Γ (.bvar i) (.sort .zero) := by
  refine ⟨List.replicate (i+1) (.sort .zero), .bvar ?_⟩
  induction i with
  | zero =>
    have := Lean4Lean.Lookup.zero (ty := VExpr.sort .zero) (Γ := [])
    simpa [VExpr.liftN] using this
  | succ i ih =>
    have := Lean4Lean.Lookup.succ (A := VExpr.sort .zero) ih
    simpa [List.replicate_succ, VExpr.liftN] using this

/-- The field-wise condition of `CtorFieldsShapeClosed`, for a `List.cons`-shaped telescope
`[Sort (u+1), bvar 0, L (bvar 1)]` (`α`, `head : α`, `tail : L α`) over any inductive head `L`
with one argument: it HOLDS.  So `List.cons` (and with it every constructor whose fields are
parameter-typed) is admitted by the restriction. -/
theorem cons_telescope_passes {L : Name} {us : List VLevel} (u : VLevel)
    (hL : Params.classify L = some (.indTy 1)) :
    ∀ T ∈ [VExpr.sort u.succ, .bvar 0, .app (.const L us) (.bvar 1)],
      ShapeClosed (SExpr.mk T) ∨ ∃ Γ, Params.env.HasType Params.univs Γ T (.sort .zero) := by
  intro T hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl
  · exact .inl .sort
  · exact .inr (bvar_isProp_somewhere 0)
  · left
    have : SExpr.mk (.app (.const L us) (.bvar 1)) = spine (.const L (us.map .mk)) [.bvar 1] := rfl
    rw [this]; exact .indTy hL

/-- Same for a `Prod.mk`-shaped telescope `[Sort (u+1), Sort (v+1), bvar 1, bvar 1]`. -/
theorem prod_telescope_passes (u v : VLevel) :
    ∀ T ∈ [VExpr.sort u.succ, .sort v.succ, .bvar 1, .bvar 1],
      ShapeClosed (SExpr.mk T) ∨ ∃ Γ, Params.env.HasType Params.univs Γ T (.sort .zero) := by
  intro T hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl
  · exact .inl .sort
  · exact .inl .sort
  · exact .inr (bvar_isProp_somewhere 1)
  · exact .inr (bvar_isProp_somewhere 1)

end Lean4Lean.SExpr
