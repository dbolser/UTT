# The `const` case of `LR.adequacy`: design notes

Two independent design analyses of the last research gap on the route to
unique typing (see `STATUS.md` §6), with the Lean experiments that back them.

- `DESIGN-fuel-measure.md`: shows the lemma is false with the relation
  unchanged (experiments `Stuck.lean`, `Subst1.lean`), and designs the
  induction measure for rule right-hand sides (`Fuel.lean`).
- `DESIGN-ctor-clause-from-artifact.md`: ports the constructor-value clauses
  of the paper's Lean artifact (`DomainSemantics`, ℕ and the fixpoint
  combinator) to arbitrary inductive types (`CtorClause.lean`).

The `.lean` files are experiments, not part of the build. They begin with
`import Lean4Lean.Experimental.ShapeLogRelAdequacy`; some contain deliberate
`sorry`s marking the statements under design. `./check.sh` typechecks all
four against the current tree (they were written against earlier snapshots,
commits `8fae8db` and `cb5fae8`, and have been kept compiling since).
References to `/tmp/utt-snap1`, `/tmp/utt-snap3`, `/tmp/utt-exp/...` and
`/tmp/utt-ref/paper-artifacts/...` in the documents are those snapshots, the
scratch directories, and a local copy of the paper's supplementary Lean code
(`domain-semantics-lean-BEE7`).
