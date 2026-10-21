# Experiment E6a (the pattern-leaf field lowering): PASS, with a corrected statement

2026-10-20. Plan: `../../PLAN.md` §1 D4 "RHS step" steps 1-2, §2 row E6a. Base: commit `3bccfa8`
plus E3's module (attempt a's for attempt a, attempt b's for attempt b). Run: two independent Opus
attempts, each checked by an independent adversarial verifier instructed to re-derive any claimed
obstruction itself and to judge whether an added hypothesis can really be supplied by the pattern
leaf. Verdicts: attempt a passes (flagged statement change accepted as forced and suppliable);
attempt b's verifier confirmed the same analysis and the same corrected lemma but failed it "by the
letter" because the pinned statement itself is unprovable; its fix round died on an Opus session
limit. Both attempts reached the same conclusions independently.

## 0. Outcome

**The plan's pinned lowering statement (`historical/RhsLowerStmt.lean:208-226`) is false.** Two
sorry-free refutations (`FieldLower.lean`, last section; `P2.lean` is b's verifier's independent
one):

- `T.pinned_false_iota`: for any iota rule with a same-rank self leaf (ℕ's `succ` rule), take
  `R := ∅` and `hRHS := RHS.bot` with all-⊥ shapes; every other hypothesis holds, yet the pinned
  self clause demands an `R`-witness for each self entry. b's `P2.lean` sharpens this: the pinned
  statement forces `g.self = []` for every rule.
- `T.pinned_false_const`: `R` is not linked to the interpretation, so a non-self fixed leaf is
  unconstrained (rule `def c : Type := Prop`, `R := fun _ e => e = Prop`).

**D4's argument [A] holds, option (a) works, the fallback (b) is not needed.** The corrected
`LR.rhs_lower` is proved with no sorry (`FieldLower.lean:448`; axioms `propext`,
`Classical.choice`, `Quot.sound`; tracer at every constant of the module: 0 sorry). The changes,
each forced and each suppliable at the pattern leaf:

1. **`hR : ∀ m e, R m e → LE_Interp ρ₀ m e`** (new). It is the last premise of `LE_Interp.const`,
   available in `LR.const_local` at the same `ρ` as `LIH`. **Upstream change: `LR.const_spine` and
   `LR.pat_leaf_1a` take `hR` too**, since `R` is fixed through the `Const` induction
   (`ConstLocalHR.lean`: `const_local` still proves, passing the premise). b's verifier showed the
   two stubs are themselves false as E3 stated them without `hR` (a junk `R` entry at a
   definition body). Landed in the repo with R7+R8 (`3a28c52`).
2. **`hhead`** (new, attempt a): for each path, either `m2 path ≤` its lowered entry (recursor
   arguments: from the spine lemma's `hρ` and `Matches`) or the path's context type is a `.const
   I' us` with `I'` an inductive type (constructor fields: from `gen_head_ctor` and
   `ctor_fields_closed`). a's verifier proved the supply lemma `V.hhead_supply` sorry-free for
   every iota rule (`HheadSupply.lean`). Attempt b split the same fact into `hrec` and `hfield`
   and proved `LR.rhs_lower_iota`, deriving both from `hρ`, `fields.length = n` and
   `ctor_fields_closed`. Stage 2 will need a new argument for field variables in function
   position.
3. **Self clause weakened at ⊥ and pinned to the occurrence**: the `R`-witness `R me (.const c'
   ls') ∧ me ≤ s` is required only when `s ≠ ⊥`; in exchange the clause names the j-th same-rank
   leaf (`selfLeaves[j]? = some (.const c' us)`), fixes `ls' = us.map (SLevel.instV ls)`, and
   keeps `us.length = ci'.uvars` unconditionally (from `pat_defeq` by inversion; b's verifier's
   `SelfLen.lean` shows this is derivable, and `Adequate.cons` needs it for the ⊥ entries too).
   `ConstGoal`, the typed `s` and the type equation are kept unconditionally.
4. `rank := RP.rank`, `gen := Pattern.gen`, `idx := Pattern.pathIdx p` (a) / `Pattern.genIdx p`
   (b): the intended instantiation. `RP` also supplies the RHS typing (`pat_typed`), without which
   an ill-typed RHS breaks the main conjunct (argued).

The main conjunct is verbatim the pinned one. `hm` is unused.

## 1. The lemma as proved (attempt a, `FieldLower.lean:448`)

```lean
theorem LR.rhs_lower (RP : RankParams) {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name}
    {ls : List SLevel} {R : TShape → SExpr → Prop} (LIH : LR.LocalIH RP.rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e)                                         -- NEW
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
        (r.1.selfLeaves (Pattern.sameRank RP.rank p.head))[j]? = some (.const c' us) ∧   -- pinned occurrence
        RP.rank c' = RP.rank c ∧ Params.env.constants c' = some ci' ∧ us.length = ci'.uvars ∧
        SExpr.mkInst ls (g.self.getD j (.sort .zero)) = SExpr.mkInst (us.map (SLevel.instV ls)) ci'.type ∧
        (∃ (k : Nat) (x b : WShape k), s = x.T ∧ x.HasType b ∧
          LE_Interp ρ₀ b.T (SExpr.mkInst (us.map (SLevel.instV ls)) ci'.type)) ∧
        LR.ConstGoal Γ₀ ρ₀ s c' (us.map (SLevel.instV ls)) ci' ∧
        ((∃ k, s = (WShape.bot (n := k)).T) ∨                                      -- CHANGED
          ∃ me, R me (.const c' (us.map (SLevel.instV ls))) ∧ me ≤ s)) ∧
      ∀ {n'} {y' a' : WShape n'}, y'.T ≤ mC → y'.HasType a' →
        LE_Interp (Valuation.lower selfs fields ρ m) a'.T (SExpr.mkInst ls (g.type.liftN g.self.length)) →
        LE_Interp (Valuation.lower selfs fields ρ m) y'.T (SExpr.mkInst ls g.rhsAbs)
```

`Valuation.lowerCtx` and `Valuation.lower` are verbatim `RhsLowerStmt.lean:195-201`. Attempt b's
`LR.rhs_lower'` (`FieldLower-b.lean`) is the same lemma with `hhead` split into `hrec`/`hfield`
and `idx := p.genIdx`, plus `LR.rhs_lower_iota` which discharges `hrec`/`hfield` from the leaf's
data.

## 2. How the proof goes (both attempts)

By induction on `hRHS : LE_Interp.RHS` against the syntax-directed strong typing of `rhsAbs` at
`ρ_low` (from `pat_typed` via `strong_below`, `weak_append`, `mono below_le`, `strongSoundS`;
`ρ_low` `Fits` the extended context by `hfit` and the self types from `EnvStrongR`). Every node
yields a typed upper bound that interprets it: fixed leaves by `hR` (and closedness), self leaves
by the `LocalIH` bound (`ConstGoal`'s `.inr`), recursor arguments by `hhead`'s left disjunct, and
applications by soundness (`SoundTy` at `ρ_low`). At an application the function's typed bound is
a `lam` with `HasDom`, so an untyped argument shape collapses to a typed part below it with the
same output (`T.app_collapse`, the core of [A]); the argument then only needs the downward claim,
which `hvar` gives at variables. A constructor-field variable never sits in function position:
its type is `const I' us` at `indTy`, and `forallE ⊥ ⊥` is not below `indTy`
(`T.const_indTy_not_forallE`). Self entries: `R`-witnessed ones give `s` from the `ConstGoal`
bound; under `RHS.bot`, `s := ⊥`. Where each hypothesis is used: `hfit` once (the `Fits` base);
`hvar` only at variable nodes; `LIH` only at witnessed self leaves; the `a'`-premise only when the
RHS root is a bare field variable; `hR` at fixed leaves; `hhead` in the `app` case; `hMt` only for
`p.head = c`; `hP`/`hg` for `pat_typed`, `pat_defeq`, `EnvStrongR.ctx`, `gen_self`.

Helper lemmas (R10 lands them): valuation/lift plumbing (`foldr_push_add/lt`, `liftK_add`,
`mkInst_liftN`, `liftK_const`, `LE_Interp_foldr_push_liftK`, `lookup_eq`), shape lemmas
(`forallE_bot_interp`, `forallE_not_le_indTy/bot`, `const_indTy_not_forallE`, `app_collapse`),
`Pattern.gen` plumbing (`matches_head`, `pathIdx_lt`, `gen_head_ctx`), lowering
(`fits_foldr_push`, `const_inv`, `SelfFact`, `selfFact_exists`, `rhs_lower_core`), level count
(`onCtx_append_right`, `strong_env`, `leaf_levels`, `pat_leaf_levels`). 711 lines against the
plan's ~200.

## 3. Verification output (verbatim, attempt a, `Check.lean`)

```
'Lean4Lean.SExpr.LR.rhs_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lean4Lean.SExpr.T.pinned_false_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lean4Lean.SExpr.T.pinned_false_iota' depends on axioms: [propext, Classical.choice, Quot.sound]
== roots: [Lean4Lean.SExpr.LR.rhs_lower]
axioms reached (3):
  Classical.choice
  Quot.sound
  propext
constants directly containing sorry (0):
== roots: [Lean4Lean.SExpr.T.pinned_false_const, Lean4Lean.SExpr.T.pinned_false_iota]
axioms reached (3):
  Classical.choice
  Quot.sound
  propext
constants directly containing sorry (0):
```

The tracer rooted at all 33 constants of the module reaches the same three axioms and no sorry.
`Check.lean` also restates the pinned text (`T.PinnedRhsLower`) and shows it is the literal
`RhsLowerStmt.lean` statement with `gen := Pattern.gen`, `idx := Pattern.pathIdx p`. The verifier
scratch files kept here: `HheadSupply.lean` (a's verifier: `hhead` for every iota rule, sorry-free),
`ConstLocalHR.lean` (a's verifier: `const_local` with an `hR`-taking `const_spine`), `P2.lean`
(b's verifier: the pinned statement forces `g.self = []`), `SelfLen.lean` (b's verifier:
`us.length = ci'.uvars` for every self occurrence from `pat_defeq`).

## 4. What changes downstream

- D4 step 2's statement is the one in §1. D4 step 1 (building `W_p`) must supply `hhead`
  (`HheadSupply.lean` shows how) and, for ⊥ self entries, `Γ₀ ⊢ const c' ls' : A` from the
  unconditional level count via `Params.const_wf`, with `LR.bot` as the `DefEq`.
- `LR.const_spine` and `LR.pat_leaf_1a` carry `hR` (done, `3a28c52`). R9 and R10 prove the
  landed statements.
- E6 (the pattern leaf) runs on the landed tree with this module ported (`RankParams` → the class
  fields).

## 5. Rebuilding

`Lean4Lean/Experimental/E6a/FieldLower.lean` in a built copy of `3bccfa8` with E3's
`Lean4Lean/Experimental/E3/Measure7.lean` (attempt a's; attempt b's for `FieldLower-b.lean`)
built; `lake build Lean4Lean.Experimental.E6a.FieldLower`, then `lake env lean Check.lean`. The
run used `/tmp/utt-snap16a` and `/tmp/utt-snap16b` (scratch `/tmp/utt-exp/e6a/{a,b}`).
