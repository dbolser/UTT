import Lean4Lean.Experimental.E6a.FieldLower
/-! E6a check: axioms, tracer, signature, statement fidelity against
`docs/const-case/plan/historical/RhsLowerStmt.lean:208-234`. -/

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

namespace Lean4Lean.SExpr
open Lean4Lean.SExpr

#print axioms LR.rhs_lower
#print axioms T.pinned_false_const
#print axioms T.pinned_false_iota
#eval traceSorries [``LR.rhs_lower]
#eval traceSorries [``T.pinned_false_const, ``T.pinned_false_iota]
#check @LR.rhs_lower

variable [Params]

/-! ### Fidelity (1): `T.PinnedRhsLower rank` IS `RhsLowerStmt.lean:208-234` with
`gen := Pattern.gen`, `idx := Pattern.pathIdx p` (text copied; closed by `fun H => H`). -/
example (rank : Name → Nat) : T.PinnedRhsLower rank →
    ∀ {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name} {ls : List SLevel}
    {R : TShape → SExpr → Prop} (LIH : LR.LocalIH rank Γ₀ ρ₀ c R)
    {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} {mC : TShape}
    (hP : Params.Pat p r) (hMt : LE_Interp.Matches p c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1)
    (g : PatGen) (hg : Pattern.gen Params.env rank Params.classify p r.1 = some g)
    {fields : List TShape} {ρ : Valuation} {m : Nat} (hm : g.ctx.length = fields.length + m)
    (hfit : (Valuation.lowerCtx fields ρ m).Fits Γ₀ (g.ctx.map (SExpr.mkInst ls) ++ Γ₀))
    (hvar : ∀ path {n} {y b : WShape n}, y.T ≤ m2 path → y.HasType b →
      LE_Interp (Valuation.lowerCtx fields ρ m) b.T
        (SExpr.mkInst ls ((g.ctx.getD (Pattern.pathIdx p path) (.sort .zero)).liftN
          (Pattern.pathIdx p path + 1))) →
      y.T ≤ Valuation.lowerCtx fields ρ m (Pattern.pathIdx p path)),
    ∃ selfs : List TShape, selfs.length = g.self.length ∧
      (∀ j s, selfs[j]? = some s → ∃ (me : TShape) (c' : Name) (ls' : List SLevel) (ci' : VConstant),
        R me (.const c' ls') ∧ rank c' = rank c ∧ Params.env.constants c' = some ci' ∧
        ls'.length = ci'.uvars ∧ me ≤ s ∧
        SExpr.mkInst ls (g.self.getD j (.sort .zero)) = SExpr.mkInst ls' ci'.type ∧
        (∃ (k : Nat) (x b : WShape k), s = x.T ∧ x.HasType b ∧
          LE_Interp ρ₀ b.T (SExpr.mkInst ls' ci'.type)) ∧
        LR.ConstGoal Γ₀ ρ₀ s c' ls' ci') ∧
      ∀ {n'} {y' a' : WShape n'}, y'.T ≤ mC → y'.HasType a' →
        LE_Interp (Valuation.lower selfs fields ρ m) a'.T
          (SExpr.mkInst ls (g.type.liftN g.self.length)) →
        LE_Interp (Valuation.lower selfs fields ρ m) y'.T (SExpr.mkInst ls g.rhsAbs) :=
  fun H => H

/-! ### Fidelity (2): the general statement (`gen`, `idx` variables, as typechecked in
`RhsLowerStmt.lean`) implies `T.PinnedRhsLower`. -/
example (rank : Name → Nat)
    (H : ∀ {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name} {ls : List SLevel}
      {R : TShape → SExpr → Prop} (_LIH : LR.LocalIH rank Γ₀ ρ₀ c R)
      {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
      {m2 : p.Path → TShape} {mC : TShape}
      (_hP : Params.Pat p r) (_hMt : LE_Interp.Matches p c rargs m2)
      (_hRHS : LE_Interp.RHS ls m2 R mC r.1)
      (gen : VEnv → (Name → Nat) → (Name → Option Classification) → (p : Pattern) → p.RHS →
        Option PatGen)
      (g : PatGen) (_hg : gen Params.env rank Params.classify p r.1 = some g)
      (idx : p.Path → Nat)
      {fields : List TShape} {ρ : Valuation} {m : Nat} (_hm : g.ctx.length = fields.length + m)
      (_hfit : (Valuation.lowerCtx fields ρ m).Fits Γ₀ (g.ctx.map (SExpr.mkInst ls) ++ Γ₀))
      (_hvar : ∀ path {n} {y b : WShape n}, y.T ≤ m2 path → y.HasType b →
        LE_Interp (Valuation.lowerCtx fields ρ m) b.T
          (SExpr.mkInst ls ((g.ctx.getD (idx path) (.sort .zero)).liftN (idx path + 1))) →
        y.T ≤ Valuation.lowerCtx fields ρ m (idx path)),
      ∃ selfs : List TShape, selfs.length = g.self.length ∧
        (∀ j s, selfs[j]? = some s → ∃ (me : TShape) (c' : Name) (ls' : List SLevel) (ci' : VConstant),
          R me (.const c' ls') ∧ rank c' = rank c ∧ Params.env.constants c' = some ci' ∧
          ls'.length = ci'.uvars ∧ me ≤ s ∧
          SExpr.mkInst ls (g.self.getD j (.sort .zero)) = SExpr.mkInst ls' ci'.type ∧
          (∃ (k : Nat) (x b : WShape k), s = x.T ∧ x.HasType b ∧
            LE_Interp ρ₀ b.T (SExpr.mkInst ls' ci'.type)) ∧
          LR.ConstGoal Γ₀ ρ₀ s c' ls' ci') ∧
        ∀ {n'} {y' a' : WShape n'}, y'.T ≤ mC → y'.HasType a' →
          LE_Interp (Valuation.lower selfs fields ρ m) a'.T
            (SExpr.mkInst ls (g.type.liftN g.self.length)) →
          LE_Interp (Valuation.lower selfs fields ρ m) y'.T (SExpr.mkInst ls g.rhsAbs)) :
    T.PinnedRhsLower rank :=
  by
  intro Γ₀ ρ₀ c ls R LIH p r n rargs m2 mC hP hMt hRHS g hg fields ρ m hm hfit hvar
  exact H LIH hP hMt hRHS Pattern.gen g hg (Pattern.pathIdx p) hm hfit hvar

/-! ### Fidelity (3): the pinned statement is false. -/
-- at the delta rule `def c : Type := Prop` (no self leaf; `R` unconstrained):
example (rank : Name → Nat) {c : Name} {r : (Pattern.const c).RHS × (Pattern.const c).Check}
    {cl : (VExpr.sort .zero).Closed} {g : PatGen} {ci : VConstant}
    (hP : Params.Pat (.const c) r) (hr : r.1 = .fixed (.sort .zero) cl)
    (hg : Pattern.gen Params.env rank Params.classify (.const c) r.1 = some g)
    (hci : Params.env.constants c = some ci) (hty : ci.type = .sort (.succ .zero)) :
    ¬T.PinnedRhsLower rank :=
  fun H => T.pinned_false_const H hP hr hg hci hty
-- at every iota rule with a self leaf (e.g. `Nat.rec`'s succ rule), under `RankParams`:
example (RP : RankParams) {rec c' : Name} {mm k : Nat}
    {r : (Pattern.iota rec mm c' k).RHS × (Pattern.iota rec mm c' k).Check} {g : PatGen}
    (hP : Params.Pat (.iota rec mm c' k) r)
    (hg : Pattern.gen Params.env RP.rank Params.classify (.iota rec mm c' k) r.1 = some g)
    (hne : g.self ≠ []) : ¬T.PinnedRhsLower RP.rank :=
  fun H => T.pinned_false_iota RP H hP hg hne

/-! ### Fidelity (4): the statement as proved, in the pinned layout. Differences, marked:
`(RP : RankParams)` for the variable `rank` (`rank := RP.rank`); `gen := Pattern.gen`;
`idx := Pattern.pathIdx p`; NEW `hR`; NEW `hhead`; CHANGED self clause. Closed by
`LR.rhs_lower`. -/
example (RP : RankParams) {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name} {ls : List SLevel}
    {R : TShape → SExpr → Prop} (LIH : LR.LocalIH RP.rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e)                                    -- NEW
    {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} {mC : TShape}
    (hP : Params.Pat p r) (hMt : LE_Interp.Matches p c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1)
    (g : PatGen) (hg : Pattern.gen Params.env RP.rank Params.classify p r.1 = some g)
    {fields : List TShape} {ρ : Valuation} {m : Nat} (hm : g.ctx.length = fields.length + m)
    (hfit : (Valuation.lowerCtx fields ρ m).Fits Γ₀ (g.ctx.map (SExpr.mkInst ls) ++ Γ₀))
    (hvar : ∀ path {n} {y b : WShape n}, y.T ≤ m2 path → y.HasType b →
      LE_Interp (Valuation.lowerCtx fields ρ m) b.T
        (SExpr.mkInst ls ((g.ctx.getD (p.pathIdx path) (.sort .zero)).liftN (p.pathIdx path + 1))) →
      y.T ≤ Valuation.lowerCtx fields ρ m (p.pathIdx path))
    (hhead : ∀ path, m2 path ≤ Valuation.lowerCtx fields ρ m (p.pathIdx path) ∨     -- NEW
      ∃ (I' : Name) (us : List VLevel) (k : Nat), g.ctx[p.pathIdx path]? = some (.const I' us) ∧
        Params.classify I' = some (.indTy k)) :
    ∃ selfs : List TShape, selfs.length = g.self.length ∧
      (∀ j s, selfs[j]? = some s → ∃ (c' : Name) (us : List VLevel) (ci' : VConstant),
        (r.1.selfLeaves (Pattern.sameRank RP.rank p.head))[j]? = some (.const c' us) ∧  -- NEW
        RP.rank c' = RP.rank c ∧ Params.env.constants c' = some ci' ∧ us.length = ci'.uvars ∧
        SExpr.mkInst ls (g.self.getD j (.sort .zero)) =
          SExpr.mkInst (us.map (SLevel.instV ls)) ci'.type ∧
        (∃ (k : Nat) (x b : WShape k), s = x.T ∧ x.HasType b ∧
          LE_Interp ρ₀ b.T (SExpr.mkInst (us.map (SLevel.instV ls)) ci'.type)) ∧
        LR.ConstGoal Γ₀ ρ₀ s c' (us.map (SLevel.instV ls)) ci' ∧
        ((∃ k, s = (WShape.bot (n := k)).T) ∨                                    -- CHANGED
          ∃ me, R me (.const c' (us.map (SLevel.instV ls))) ∧ me ≤ s)) ∧
      ∀ {n'} {y' a' : WShape n'}, y'.T ≤ mC → y'.HasType a' →
        LE_Interp (Valuation.lower selfs fields ρ m) a'.T
          (SExpr.mkInst ls (g.type.liftN g.self.length)) →
        LE_Interp (Valuation.lower selfs fields ρ m) y'.T (SExpr.mkInst ls g.rhsAbs) :=
  LR.rhs_lower RP LIH hR hP hMt hRHS g hg hm hfit hvar hhead

end Lean4Lean.SExpr
