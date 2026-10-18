# `Params` instances

`SExpr.Params` (`Lean4Lean/Experimental/SExpr.lean`, top) is the hypothesis
package the route assumes (`STATUS.md` §5). These files show what it takes to
inhabit it. They are experiments, not part of the build; `./check.sh`
typechecks both against the current tree.

- `EmptyParams.lean`: `emptyParams`, an instance for `VEnv.empty`. Every field
  is vacuous or `rfl`; no `sorry`. Shows the package is satisfiable.
- `NatParams.lean`: `natParams`, an instance for the environment with the four
  constants `Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec` (encodings cross-checked
  against Lean's own declarations at elaboration time) and `Pat` holding the two
  iota patterns. `henv` (`envC_ordered`, including the typing of `Nat.rec`),
  `pat_simple`, `pat_wf`, `pat_uniq` (a finite `decide`), and `ctor_syn` are
  proven. Three deliberate `sorry`s, each marked `-- SORRY`: `iotaZeroLam_wf`,
  `iotaSuccLam_wf` (routine typing of the lambda-wrapped rules, only used by
  `envA_ordered`), and `ctor_sort_nat` (blocked on the repo's own sorried
  `IsDefEqU.sort_inv`, `Theory/Typing/Injectivity.lean`).

## Finding: `extra_patV` as stated does not fit schematic rules

`extra_patV` demands that every environment rule `df`, instantiated at levels,
be a `Pattern.Matches` instance of some `Pat p r` with `rhs = r.1.apply`. A
schematic iota rule can be encoded in `VDefEq` in two ways, and neither works:

- Lambda-wrapped (Lean4Lean's own `vdefeq` convention, cf. `quotDefEq`): the
  lhs is a `lam`, and `Pattern.Matches` has no `lam` case. So `extra_patV` is
  false for `envA` (the constants plus the two wrapped iota rules), for every
  choice of `Pat`: `extra_patV_false_envA`. `envA` is `Ordered`
  (`envA_ordered`, modulo the two routine typing sorries).
- Open `bvar`s as metavariables: pattern-matchable (`iotaZeroOpen_matches`),
  but not `VDefEq.WF` in any `Ordered` environment, since well-typed closed
  terms are closed: `iotaZeroOpen_not_wf`.

So `extra_patV` holds only vacuously, for rule-free environments (`emptyParams`;
`natParams` over the constants-only `envC`). Nothing in `Params` requires
`Pat ⊆ env.defeqs`, so `Pat` may still carry the schematic patterns.

**Open item:** reformulate `extra_patV` so lambda-wrapped iota rules are
pattern instances (strip the binders, or state it on the beta-applied form),
and re-derive `SExpr.Params.extra_pat` and its model-side uses.
