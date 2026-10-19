import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Completeness audit 2: axioms of the repo lemmas the PLAN cites as proven building blocks. -/
open Lean4Lean Lean4Lean.SExpr
#print axioms Lean4Lean.SExpr.WHRedS.ctorSpine_determ
#print axioms Lean4Lean.SExpr.WHNF.indTySpine
#print axioms Lean4Lean.SExpr.WHNF.ctorSpine
#print axioms Lean4Lean.SExpr.WHRedS.major
#print axioms Lean4Lean.SExpr.WHRedS.determ
#print axioms Lean4Lean.SExpr.IsDefEq.subst
#print axioms Lean4Lean.SExpr.IsDefEq.mkS
#print axioms Lean4Lean.SExpr.IsDefEqStrong.forallE_inv'
#print axioms Lean4Lean.SExpr.IsDefEqStrong.weak0
#print axioms Lean4Lean.SExpr.LE_Interp.mono_l
#print axioms Lean4Lean.SExpr.LE_Interp.closed_iff
#print axioms Lean4Lean.SExpr.LE_Interp.soundS
#print axioms Lean4Lean.SExpr.LR.Adequate.mono_r
#print axioms Lean4Lean.SExpr.LR.DefEq.lift
#print axioms Lean4Lean.SExpr.LR.SubstWF.symm
#print axioms Lean4Lean.SExpr.WHRedS.defeq
#print axioms Lean4Lean.VEnv.HasType.lam_inv
#print axioms Lean4Lean.SExpr.Params.extra_pat
#print axioms Lean4Lean.SExpr.spine_inj
