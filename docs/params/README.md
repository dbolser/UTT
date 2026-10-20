# `Params` instances

`SExpr.Params` (`Lean4Lean/Experimental/SExpr.lean`, `class Params`) is the
hypothesis package the route assumes (`STATUS.md` §5). These files show what it
takes to inhabit it. They are experiments, not part of the build; `./check.sh`
typechecks them against the current tree, checks each file's number of
`sorry` warnings (`EmptyParams` 0, `NatParams` 1), and traces the sorries
reaching `natParams` (exactly `ctor_sort_nat`).

## The fields

- `env` (with `henv : env.Ordered`), `univs`, `Pat` (the rewrite patterns, each
  with its right-hand side and side condition), `classify`.
- `pat_simple`, `pat_wf`, `pat_uniq`: every pattern is a `SimplePattern`,
  well-formed for `classify`, and patterns do not overlap.
- `extra_patV` (λ-form, PLAN D5, landed by R6): every rule of `env`,
  instantiated at well-formed levels, is the λ-closure over a telescope `Δ` of
  a well-typed open equation `Δ.reverse ⊢ L ≡ R : T` (lhs, rhs and type are
  `Δ.foldr .lam L`, `Δ.foldr .lam R`, `Δ.foldr .forallE T`), whose left side
  `L` is a `Pat` instance with its side conditions holding, and whose right side
  `R` is the pattern's right-hand side. This is Lean4Lean's `vdefeq`
  convention (`Theory/Meta.lean`; cf. `quotDefEq`, `Theory/Quot.lean`). With
  `Δ = []` it is the field before R6 plus the rule's own typing.
- `ctor_syn`, `ctor_sort`: a constructor's type is syntactically a Π-telescope
  over its inductive type, and every derivable sort of it is non-zero.
- The ten rank fields (PLAN D4/D3, landed by R5): `rank`, `rank_ordered`,
  `type_below`, `pat_rank`, `pat_gen`, `pat_typed`, `pat_defeq` (every `Pat`
  rule's generated open equation is a definitional equality of `env`),
  `pat_check`, `indTy_closed`, `ctor_fields_closed`.
- The two iota-rule invariants (PLAN D4, found by experiment E6, landed by
  R10), both kernel invariants of Lean's recursor rules: `rec_major_indTy` (the
  head of a recursor's major domain is an inductive type, so the major's
  constructor clause is at the pattern's levels) and `rhs_not_field` (a rule's
  right-hand side is never a bare constructor-field variable; Lean's recursor
  rules have RHS `minor fields ihs`).

## The files

- `EmptyParams.lean`: `emptyParams`, an instance for `VEnv.empty`. Every field
  is vacuous or `rfl` (`extra_patV`: `VEnv.empty` has no rules;
  `rank_ordered`: every rank prefix of `∅` is `∅`); no `sorry`. Shows the
  package is satisfiable.
- `NatParams.lean`: `natParams`, an instance for `envA`: the four constants
  `Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec` (encodings cross-checked against
  Lean's own declarations at elaboration time) plus the two iota rules in
  Lean4Lean's convention (closed, λ-wrapped), with `Pat` holding the two iota
  patterns and ranks `Nat 0, zero 1, succ 1, rec 2`. Experiment E4's proofs
  (`docs/const-case/plan/E4/NatParamsA.lean`), landed by R12. Every field is
  proven except `ctor_sort`: `henv` (`envA_ordered`, including the typings of
  `Nat.rec` and of both λ-wrapped rules), `extra_patV` (each rule is the
  λ-closure of its open equation `zero_open`/`succ_open`, whose lhs matches the
  pattern), `pat_defeq` (the same open equations), `pat_uniq` (a finite
  `decide`), `ctor_syn`, the rank fields (`Pattern.gen` evaluated by `rfl`),
  and the two iota-rule invariants (`Nat.rec`'s major domain is `Nat`; the
  rules' right-hand sides are `z` and an application).
  One deliberate `sorry`, marked `-- SORRY`: `ctor_sort_nat`, blocked on the
  repo's own sorried `IsDefEqU.sort_inv` (`Theory/Typing/Injectivity.lean`).
- `Schema.lean` (historical: typechecked at `3c35f59`, no longer compiles
  since R6): `Pattern.Matches.not_lam` and `Params.no_lam_rule`: under the
  field before R6, no `Params` environment contains a rule whose left-hand side
  is a lambda. The finding below, made precise.

## Finding (resolved by R6): `extra_patV` as stated did not fit schematic rules

Before R6, `extra_patV` demanded that every environment rule `df`,
instantiated at levels, be itself a `Pattern.Matches` instance of some `Pat p r`
with `rhs = r.1.apply` (the `Δ = []` form). A schematic iota rule can be
encoded in `VDefEq` in two ways, and neither worked:

- Lambda-wrapped (Lean4Lean's own `vdefeq` convention, cf. `quotDefEq`): the
  lhs is a `lam`, and `Pattern.Matches` has no `lam` case. So the old field is
  false for `envA`, for every choice of `Pat`: `extra_patV_false_envA`, stated
  against `ExtraPatVOld`, the old field's body over `envA` (`NatParams.lean`).
- Open `bvar`s as metavariables: pattern-matchable (`iotaZeroOpen_matches`),
  but not `VDefEq.WF` in any `Ordered` environment, since well-typed closed
  terms are closed: `iotaZeroOpen_not_wf`.

So the old field held only vacuously, for rule-free environments, and the ℕ
instance then lived over the constants-only `envC`, with `pat_defeq` false
there. R6 restated `extra_patV` on the λ-telescope (PLAN D5): `L` a pattern
instance, together with the rule's *open typed equation*
`Δ.reverse ⊢ L ≡ R : T` (the plan's audit found that the typed beta steps
need the body typed at the declared codomain, and nothing else supplies that
without Pi-injectivity). R12 then moved `natParams` to `envA`, where the two
rules' open equations prove both `extra_patV` and `pat_defeq`.
