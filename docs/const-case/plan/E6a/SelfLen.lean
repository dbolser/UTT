import Lean4Lean.Experimental.E6a.FieldLower
/-! Verifier: the `ls'.length = ci'.uvars` fact that `LR.rhs_lower'` drops for `⊥` self entries
(and that `Adequate.cons`'s `hx` needs for W_p) is derivable from `RP.pat_defeq` by typing
inversion (`HasType.app_inv`/`const_inv`, Theory/Typing/Strong.lean). -/
namespace Lean4Lean.SExpr
variable [Params]

theorem V.selfConsts_typed {p : Pattern} {rank : Name → Nat} {k : Nat} {idx : p.Path → Nat}
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (Params.env.IsType U)) :
    ∀ (r : p.RHS) {V}, Params.env.HasType U Γ (r.toOpen idx) V →
      ∀ c' us, (c', us) ∈ r.selfOccs rank k →
        ∃ ci', Params.env.constants c' = some ci' ∧ us.length = ci'.uvars
  | .fixed e _, V, H, c', us, hm => by
    simp only [Pattern.RHS.selfOccs, Pattern.RHS.selfConsts, Option.mem_toList] at hm
    obtain ⟨rfl, -⟩ := VExpr.selfConst?_eq_some.1 hm
    obtain ⟨ci, h1, -, h3⟩ := VEnv.HasType.const_inv Params.henv hΓ H
    exact ⟨ci, h1, h3⟩
  | .var _, _, _, _, _, hm => by simp [Pattern.RHS.selfOccs, Pattern.RHS.selfConsts] at hm
  | .app f a, V, H, c', us, hm => by
    obtain ⟨A, B, hf, ha⟩ := VEnv.HasType.app_inv Params.henv hΓ H
    simp only [Pattern.RHS.selfOccs, Pattern.RHS.selfConsts, List.mem_append] at hm
    rcases hm with hm | hm
    · exact V.selfConsts_typed hΓ f hf c' us hm
    · exact V.selfConsts_typed hΓ a ha c' us hm

theorem V.onCtx_suffix {P : List VExpr → VExpr → Prop} :
    ∀ (S : List VExpr) {C : List VExpr}, OnCtx (S ++ C) P → OnCtx C P
  | [], _, h => h
  | _ :: S, _, h => V.onCtx_suffix S h.1

theorem V.self_uvars (RP : RankParams) {p : Pattern} {r : p.RHS × p.Check} (hP : Params.Pat p r)
    {g : PatGen} (hg : Pattern.gen Params.env RP.rank Params.classify p r.1 = some g) {ci : VConstant}
    (hci : Params.env.constants p.head = some ci) {j : Nat} {c' : Name} {us : List VLevel}
    (hj : (r.1.selfOccs RP.rank (RP.rank p.head))[j]? = some (c', us)) :
    ∃ ci', Params.env.constants c' = some ci' ∧ us.length = ci'.uvars := by
  have hΓ : OnCtx g.ctx (Params.env.IsType ci.uvars) :=
    (V.onCtx_suffix g.self (RP.pat_typed hP hg hci).1).mono fun h => h.mono (Params.env.below_le ..)
  have H := (RP.pat_defeq hP hg hci).hasType.2
  rw [(Pattern.gen_rhs_eq hg).1] at H
  exact V.selfConsts_typed hΓ r.1 H c' us (List.mem_of_getElem? hj)

end Lean4Lean.SExpr
#print axioms Lean4Lean.SExpr.V.self_uvars
