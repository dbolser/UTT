import Lean4Lean.Experimental.E3.Measure7
/-! E3 check file: axioms of the spec lemmas (a)-(g) and of `EnvStrongR.of_params`, the D4
literal form of `const_local`, and the sorry tracer (scripts/TraceSorry.lean:6-29). -/

-- (a) gen_head (+ the ctor_syn form)
#print axioms Lean4Lean.Pattern.gen_head
#print axioms Lean4Lean.Pattern.gen_head_ctor
-- (b) gen_lhs (VExpr form, under a substitution, as an openSpine instance)
#print axioms Lean4Lean.Pattern.gen_lhs
#print axioms Lean4Lean.Pattern.gen_lhs_subst
#print axioms Lean4Lean.Pattern.gen_lhs_openSpine
-- (c) per-occurrence RHS.toVExpr_subst (generic, and at Pattern.gen's rhsAbs)
#print axioms Lean4Lean.Pattern.RHS.toVExpr_subst
#print axioms Lean4Lean.Pattern.gen_rhsAbs
-- (d) gen_type
#print axioms Lean4Lean.Pattern.gen_type
-- (e) gen_arity (VExpr, mkInst, and through pat_gen for any Pat)
#print axioms Lean4Lean.Pattern.gen_arity
#print axioms Lean4Lean.Pattern.gen_arity_mkInst
#print axioms Lean4Lean.SExpr.RankParams.pat_arity
-- (f) gen_rhs
#print axioms Lean4Lean.Pattern.gen_rhs
-- (g) gen_self (VExpr, and the mkInst_instL link to ConstGoal's type)
#print axioms Lean4Lean.Pattern.gen_self
#print axioms Lean4Lean.Pattern.gen_self_mkInst
-- delta shape
#print axioms Lean4Lean.Pattern.gen_delta
-- EnvStrongR
#print axioms Lean4Lean.SExpr.EnvStrongR.of_params
-- the repo's E-versions used by the spine lemma's lam case (R4)
#print axioms Lean4Lean.SExpr.IsDefEqStrong.forallE_inv'
#print axioms Lean4Lean.SExpr.IsDefEqStrong.telescope

namespace Lean4Lean.SExpr
/-- `LR.const_local` at D4's literal statement (WF IH and conclusion spelled out). -/
example [Params] (RP : RankParams) {Γ₀ : List SExpr} {k : Nat} {c₀ : Name}
    (WFIH : ∀ k' < k, ∀ {Γ M N A}, IsDefEqStrong (Params.env.below RP.rank k') Γ M N A →
      ∀ {ρ n} {m a : WShape n}, LE_Interp ρ m.T M → LE_Interp ρ a.T A → m.HasType a →
      LR.Adequate Γ₀ Γ ρ M N A m a)
    (hΓ₀ : ⊢ Γ₀) (hc₀ : RP.rank c₀ < k) :
    ∀ {ρ mT M} (_hM : LE_Interp ρ mT M) {c ls ci}, M = .const c ls → RP.rank c ≤ RP.rank c₀ →
      Params.env.constants c = some ci → ls.length = ci.uvars →
      (∃ n, mT = (WShape.bot (n := n)).T) ∨
      ∃ (n : Nat) (m' a' : WShape n), mT ≤ m'.T ∧ m'.HasType a' ∧
        LE_Interp ρ a'.T (mkInst ls ci.type) ∧
        ∀ {n'} (m a : WShape n'), m.T ≤ m'.T → LE_Interp ρ a.T (mkInst ls ci.type) → m.HasType a →
          (LR Γ₀).DefEq (.const c ls) (.const c ls) (mkInst ls ci.type) m a :=
  LR.const_local RP WFIH hΓ₀ hc₀
end Lean4Lean.SExpr

open Lean in
def traceSorries (roots : List Name) : CoreM Unit := do
  let env ← getEnv
  let mut visited : NameSet := {}
  let mut stack := roots
  let mut direct : Array Name := #[]
  let mut axioms : Array Name := #[]
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if visited.contains n then continue
    visited := visited.insert n
    match env.find? n with
    | none => continue
    | some ci =>
      let used := ci.getUsedConstantsAsSet
      if let .axiomInfo _ := ci then axioms := axioms.push n
      if used.contains ``sorryAx then direct := direct.push n
      for c in used.toList do
        if !visited.contains c then stack := c :: stack
  IO.println s!"== roots: {roots}"
  IO.println s!"axioms reached ({axioms.size}):"
  for a in axioms.qsort (·.toString < ·.toString) do IO.println s!"  {a}"
  IO.println s!"constants directly containing sorry ({direct.size}):"
  for d in direct.qsort (·.toString < ·.toString) do IO.println s!"  {d}"

#eval traceSorries [``Lean4Lean.SExpr.LR.const_local]
#eval traceSorries [``Lean4Lean.SExpr.LR.pat_leaf_1a]
#eval traceSorries [``Lean4Lean.SExpr.LR.const_case]
#eval traceSorries [``Lean4Lean.Pattern.gen, ``Lean4Lean.SExpr.EnvStrongR.of_params]
