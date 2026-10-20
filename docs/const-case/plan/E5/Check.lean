import Lean4Lean.Experimental.E5.LamRules
import Lean4Lean.Experimental.E5.LamAdequacy

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

-- (1) axioms: expect no `sorryAx`
#print axioms Lean4Lean.SExpr.T.extra_pat_lam
#print axioms Lean4Lean.SExpr.T.strongSoundS_extra_lam
#print axioms Lean4Lean.SExpr.typed_beta_rule
#print axioms Lean4Lean.SExpr.typed_beta_rhs
#print axioms Lean4Lean.SExpr.T.LR.lamRule

-- (2) the statement of `T.strongSoundS_extra_lam`, next to plan/ExtraLamStmt.lean's
#check @Lean4Lean.SExpr.T.strongSoundS_extra_lam
namespace Lean4Lean.SExpr
variable [Params]
-- plan/ExtraLamStmt.lean's statement, verbatim (binders and conclusion), closed by the E5 lemma
example (hlam : ExtraPatVLam) {df : VDefEq} {ls : List SLevel}
    {Γ : List SExpr} (h1 : Params.env.defeqs df) (h2 : ls.length = df.uvars)
    (ih1 : StrongSoundEq Γ (.mkInst ls df.lhs) (.mkInst ls df.lhs) (.mkInst ls df.type))
    (ih2 : StrongSoundEq Γ (.mkInst ls df.rhs) (.mkInst ls df.rhs) (.mkInst ls df.type)) :
    StrongSoundEq Γ (.mkInst ls df.lhs) (.mkInst ls df.rhs) (.mkInst ls df.type) :=
  T.strongSoundS_extra_lam hlam h1 h2 ih1 ih2
-- `T.extra_pat_lam` at `Δ = []`: its pattern conjunct (with the `lhs`/`rhs` equations) is exactly
-- the conclusion of `Params.extra_pat Γ` (SExpr.lean:1067)
example {Γ : List SExpr} {L R : SExpr} {df : VDefEq} {ls : List SLevel}
    (hl : SExpr.mkInst ls df.lhs = ([] : List SExpr).foldr .lam L)
    (hr : SExpr.mkInst ls df.rhs = ([] : List SExpr).foldr .lam R)
    (H : ∃ p r m1 m2 dfs, Params.Pat p r ∧ p.MatchesS L m1 m2 ∧
      (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 ∧
      (∀ a b A, (A, a, b) ∈ dfs → ([] : List SExpr).reverse ++ Γ ⊢ a ≡ b : A) ∧
      R = r.1.applyS m1 m2) :
    ∃ p r m1 m2 dfs, Params.Pat p r ∧ p.MatchesS (.mkInst ls df.lhs) m1 m2 ∧
      (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 ∧
      (∀ a b A, (A, a, b) ∈ dfs → Γ ⊢ a ≡ b : A) ∧
      .mkInst ls df.rhs = r.1.applyS m1 m2 := by
  simp only [List.foldr_nil] at hl hr; subst hl hr; exact H
#check @Params.extra_pat
end Lean4Lean.SExpr
#print Lean4Lean.SExpr.ExtraPatVLam
#check @Lean4Lean.SExpr.T.extra_pat_lam
#check @Lean4Lean.SExpr.T.LR.adequacy

-- (3) tracer: expect exactly one constant directly containing sorry (T.LR.adequacy), and 0
#eval traceSorries [``Lean4Lean.SExpr.T.LR.adequacy]
#eval traceSorries [``Lean4Lean.SExpr.T.strongSoundS_extra_lam]
