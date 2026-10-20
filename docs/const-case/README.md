# The `const` case of `LR.adequacy`: design notes

The last research gap on the route to unique typing (see `STATUS.md` §6):
three independent design analyses, a five-lens adversarial review of them,
and the merged plan, each backed by Lean experiments against the current tree.

Start with `PLAN.md`.

## Documents

- `PLAN.md`: the merged, audited implementation plan. Decisions D1–D6 (the
  constructor clause, `TyDefEq` at `indTy`, parametric fields, the measure and
  rule typing, `extra_patV`, typed reductions), ordered work items, the first
  experiment to run (E1, the typed-LR spike), open questions with fallbacks,
  and what stays excluded. Its audit log records what the two auditors found
  and how each finding was applied.
- `DESIGN-fuel-measure.md` (design B): shows the lemma is false with the
  relation unchanged (`Stuck.lean`, `Subst1.lean`) and designs the induction
  measure for rule right-hand sides (`Fuel.lean`).
- `DESIGN-ctor-clause-from-artifact.md` (design C): ports the constructor
  clauses of the paper's Lean artifact (`DomainSemantics`: ℕ and the fixpoint
  combinator) to arbitrary inductive types (`CtorClause.lean`).
- `DESIGN-ctor-code-shape.md` (design A): puts the constructor's field
  type-codes into the shape data, `ctor c l k`. Kept verbatim; its status
  header lists the corrections the review found.

## Experiments

All `.lean` files begin with `import Lean4Lean.Experimental.ShapeLogRelAdequacy`
and are not part of the build. `./check.sh` typechecks every one against the
current tree (last checked at `1710175`, whose `Lean4Lean/` equals `3c35f59`).
They are written against today's definitions, so as the plan's changes to
`ShapeLogRel.lean` and `SExpr.lean` land they will stop compiling; the plan
(`PLAN.md` R1, R13) then marks them historical and pins the check to `3c35f59`.
Files marked "deliberate sorries" contain `sorry`s that mark the statements
under design (each is commented); the others are sorry-free.

Backing the design notes (written against earlier snapshots, kept compiling):

- `Stuck.lean`, `Subst1.lean`: the lemma is false with `LRS.DefEq` `True` at
  `indTy` (design B §2).
- `Fuel.lean`: the local induction on the interpretation derivation
  (design B §3; one deliberate sorry).
- `CtorClause.lean`: design C's clause with `left`/`symm` and the statement of
  the spine lemma (two deliberate sorries).

From the five-lens review and the plan (written against HEAD `3c35f59`):

- `CounterC.lean`: design C's field clause (universal over valid type shapes,
  the "Subst1 form") is not level-invariant; the ⇐ direction of
  `LR.lift_succ_aux` fails for it. So field type-shapes must be finite code
  data, not quantified.
- `ClauseA.lean`: design A's clause with codes as finite data (`SpineTyped`,
  `SpineDefEq`, `CtorDefEq`) and the `LogRel` field proofs that depend on the
  clause's form: `left`, `symm`, `conv`, `trans`, `mono`, `lift_aux` in both
  directions, `whr`. This is the stage-1b clause of the plan.
- `Reconcile.lean`: `LR.field_retype`, `LR.Subst1.tyValid_below`. The
  consumer-side retype at the pattern leaf (constructor's parameter term versus
  recursor's) closes with the existing fields, provided both type shapes are
  bounded by one parameter shape. Stage 2 of the plan.
- `IHVacuous.lean`: the local induction on `hM` alone gives an induction
  hypothesis that fires only at the self-constant; delta bodies and other
  members of a recursive block need an outer source. This is why the plan's
  measure is a well-founded induction on an environment rank (deliberate
  sorries; the point is the printed goals).
- `Measure.lean`: the rank measure. `VEnv.below`, an environment-indexed strong
  judgment, `EnvStrongR`, the `adequacy_rank` skeleton with the local `hM`
  induction, and the pattern-leaf reduction chain (`major` then `extra`).
  Three marked sorries: a mechanical weakening lemma, the spine lemma plus
  pattern leaf, and the thirteen existing cases.
- `Inert.lean`: the `IsStruct`/`ctor'` collapse in the shape algebra is inert
  for every shape the model produces, so the clause need not handle it.

The plan's own evidence files (the typed-reduction lemmas, the stage-1a clause
over an abstract `IH`, the audit counterexamples) are in `plan/`; see
`plan/README.md`.

**Historical experiments.** `CounterC.lean`, `ClauseA.lean` and the files in
`plan/historical/` were typechecked at `3c35f59` and stopped compiling when the
typed logical relation landed (plan items R1+R2): they use the old untyped
`whr`/`sort_iff` fields, or define `TyRedS`/`TWHRedS` themselves, which now live
in `ShapeLogRel.lean`. `CtorClause.lean` and `Subst1.lean` followed when the
stage-1a constructor clause landed (R3): the first defines its own
`LRS.CtorDefEq`, the second proves that the relation is trivial at `indTy`,
which is now false by design. `Measure.lean` and eight more files in `plan/`
(`WeakE`, `MkSE`, `ForallInvE`, `EmptyBelow`, `JunkGen`, `PatLeafStmt`,
`PatLeafStmt2`, `RhsLowerStmt`, now in `plan/historical/`) followed when
`IsDefEqStrong` got its environment index (R4): they define their own
`VEnv.below`, `IsDefEqStrongE`, `mkSE` or `telescope`, which now live in
`SExpr.lean`. Each carries a `-- historical:` line after its import. Their claims concern the earlier relation and are kept for the record;
`check.sh` skips them.

References to `/tmp/utt-snap*`, `/tmp/utt-exp/...` and
`/tmp/utt-ref/paper-artifacts/...` in the documents are build snapshots of this
tree, scratch directories, and a local copy of the paper's supplementary Lean
code (`domain-semantics-lean-BEE7`).
