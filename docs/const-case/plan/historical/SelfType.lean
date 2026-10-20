import Lean4Lean.Experimental.ShapeLogRelAdequacy
-- historical: typechecked at 3c35f59, before Pattern.gen and the rank fields landed (docs/const-case/PLAN.md D4/D3, landed by R5); no longer compiles.
/-! Audit circ-3: the link between `LR.LocalIH` (ConstGoal at `mkInst ls' ci'.type`) and a
`Pattern.gen` self entry (type `g.self[j]`, a VExpr `ci'.type.instL us` at the occurrence's
levels, then `mkInst ls`). Spec lemmas (a)-(e) do not state what `g.self` is; this is the
level-composition step such a spec lemma (f) needs. No sorries. -/
namespace Lean4Lean.SExpr
variable [Params]

theorem SLevel.instV_inst {ls : List SLevel} {us : List VLevel} {l : VLevel} :
    SLevel.instV ls (l.inst us) = SLevel.instV (us.map (SLevel.instV ls)) l := by
  apply Subtype.ext; funext v
  simp only [SLevel.instV, VLevel.eval_inst, List.map_map, Function.comp_def]

/-- `mkInst ls (e.instL us) = mkInst (us.map (instV ls)) e`: so the self entry's type equals the
ConstGoal's `mkInst ls' ci'.type` with `ls' = us.map (instV ls)`, the SExpr levels of the
occurrence `mkInst ls (.const c' us) = .const c' ls'`. -/
theorem mkInst_instL {ls : List SLevel} {us : List VLevel} :
    ∀ {e : VExpr}, mkInst ls (e.instL us) = mkInst (us.map (SLevel.instV ls)) e
  | .bvar _ => rfl
  | .sort u => by simp only [VExpr.instL, mkInst, SLevel.instV_inst]
  | .const c vs => by
    simp only [VExpr.instL, mkInst, List.map_map, Function.comp_def, SLevel.instV_inst]
  | .app f a | .lam f a | .forallE f a => by
    simp only [VExpr.instL, mkInst, mkInst_instL (e := f), mkInst_instL (e := a)]

example {ls : List SLevel} {c' : Name} {us : List VLevel} :
    mkInst ls (.const c' us) = .const c' (us.map (SLevel.instV ls)) := rfl

end Lean4Lean.SExpr
#print axioms Lean4Lean.SExpr.mkInst_instL
