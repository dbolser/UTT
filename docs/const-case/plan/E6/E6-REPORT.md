# Experiment E6 (the pattern leaf): PASS, with two kernel invariants added to `Params`

2026-10-20. Plan: `../../PLAN.md` §1 D4 "RHS step" steps 1-6 as amended by E6a, §2 row E6. Base:
commit `4a92d1a` (R7+R8 landed) plus E6a's lowering module ported to the class fields. Run: two
independent Opus attempts, each checked by an adversarial verifier with fix rounds. Both attempts
proved the pinned statement of `LR.pat_leaf_1a` (checked by `example : (type_of% @LR.pat_leaf_1a)
:= …`) up to the **same two facts**, which the landed `Params` did not state and which the spine
lemma cannot supply because they are properties of the rule, not of the derivation:

- **(A)** the head `I` of the recursor's major domain `const I us` is an inductive type (not a
  `symb` with a delta rule). Needed so that `const I ls'` is a whnf and the constructor clause's
  reduct levels `ls₂` equal the pattern's `us.map (SLevel.instV ls)`; otherwise that equality needs
  level injectivity under definitional equality, i.e. unique typing itself.
- **(B)** a rule's right-hand side is never a bare constructor-field variable. At such a root the RHS
  shape is the major's raw field shape, while a Prop-sorted field is lowered to `⊥`, and excluding a
  non-`⊥` element shape there needs sort uniqueness for the rule. Lean's recursor rules have RHS
  `minor fields ihs`.

Both are invariants of Lean's recursor rules. They are now the `Params` fields `rec_major_indTy`
and `rhs_not_field` (R10; `SExpr.lean`, after `ctor_fields_closed`), proved for `natParams`
(`docs/params/NatParams.lean`) and vacuous for `emptyParams`. With them the leaf is proved with no
sorry; attempt b's fix round also proved `T.pat_leaf_1a_restricted`, the pinned statement under
exactly these two candidate fields, before they existed. Delta rules were fully proved by both
attempts without either fact.

## 1. What is here

`a/` is attempt a (over E3 attempt a's `Pattern.pathIdx`): `Helpers`, `RhsCore`, `Parts`,
`IotaData`, `Iota` (`T.pat_leaf_iota`, taking the two facts as hypotheses `hgapI`/`hgapF`),
`PatLeaf` (`T.pat_leaf_gap`, the one sorry, stating exactly (A) ∧ (B) for an iota rule, with the
full argument in its docstring; `T.pat_leaf_1a`), `Check.lean`, `LOG.md`. This is what R10 landed
(`ShapeLogRelAdequacy.lean`, sections "Field lowering for the pattern leaf (E6a)" and "The pattern
leaf (PLAN D4, E6/R10)"), with `T.pat_leaf_gap` proved from the two fields. `b/` is attempt b (over
E3 attempt b's `Pattern.genIdx`): `Basic`, `Lower`, `Selfs`, `Delta`, `Iota1`-`Iota8`, `PatLeaf`,
`Check.lean`, `LOG.md`; its two gap helpers are `T.gap_major_levels` and `T.gap_prop_root_sort`
(`Iota7.lean`), and `T.pat_leaf_1a_restricted` is the proof under the two candidate fields. Both
import the E6a module (`Lean4Lean.Experimental.E6a.FieldLower`, the port in `../E6a/`) and E3's
module, and were built in `/tmp/utt-snap19a` and `/tmp/utt-snap19b`.

## 2. What the proof does (both attempts, R10's text)

For an iota rule `rec x₁ … xₘ (c' z₁ … zₙ)` at the leaf: the major entry of the spine's
substitution gives the constructor clause (`LRS.CtorDefEq`: typed reductions of both majors to
constructor spines, the fields' equations and `FieldRel`); (A) makes the clause's levels the
pattern's. Step 1 builds the lowered substitution `W_p` over `self ++ ctx` by `Adequate.cons`:
recursor arguments from the spine's entries, fields lowered to their typed part (`⊥` for untyped
or Prop-valued fields; `hhead` from the spine's `hρ` and `ctor_fields_closed`), self entries from
`rhs_lower`'s `selfs` (typed by `Params.const_wf`, related by `ConstGoal`), each entry's `ihA` from
the well-founded hypothesis on `EnvStrongR.ctx`. Step 2 is E6a's lowering. Step 3 gets the
adequacy of `rhsAbs` from the well-founded hypothesis on `EnvStrongR.rhs`; a plan correction: the
`a'` premise is not obtainable from the goal's `a` (the major's raw fields may be untyped), so the
RHS shape's interpretation comes from `rhs_lower_core`'s root conjunct, a typed pair above it from
soundness at `ρ_low`, and the type is transferred back to `B` at `ρ` through "interpretations of a
constructor spine lie below `ctor'` of the argument shapes". Step 4 rewrites with the
`Pattern.gen` lemmas ((c) `gen_rhsAbs`, (f) `gen_rhs`). Step 5 is the typed head reduction of each
goal side: `appDF` with the clause's typed major reduction, then `WHRed.extra` on the instance
(`gen_lhs_matches`, `pat_check`), typed by `pat_defeq` through `IsDefEq.mkS` and the substitution.
Step 6 converts the types with `tyV` at the substitution with the major replaced. Delta rules
(`.const c`) are the same chain with an empty context.

## 3. Verification

Attempt a's verifier (round 1) and attempt b's (rounds 1-2) confirmed: the pinned statement is
reproduced, all 99 (a) / 186 (b) module constants contain sorry only in the gap helper(s), the
gaps are real and not suppliable by R9, and the two candidate fields close them. R10's landing was
verified separately (clean rebuild, tracer, frozen statements, both docs check scripts): the
tracer for `IsDefEq'.uniq` reads `axioms reached (3): Classical.choice, Quot.sound, propext;
constants directly containing sorry (0)`.

## 4. Rebuilding

`a/*.lean` as `Lean4Lean/Experimental/E6/*.lean` in a built copy of `4a92d1a` with
`Lean4Lean/Experimental/E6a/FieldLower.lean` (the ported E6a module) built; `lake build
Lean4Lean.Experimental.E6.PatLeaf`, then `lake env lean a/Check.lean`. Likewise `b/` with E3
attempt b's names. Against the current tree the landed names clash; these are records.
