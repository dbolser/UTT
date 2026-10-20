# `Params` instances

`SExpr.Params` (`Lean4Lean/Experimental/SExpr.lean`, top) is the hypothesis
package the route assumes (`STATUS.md` §5). These files show what it takes to
inhabit it. They are experiments, not part of the build; `./check.sh`
typechecks them against the current tree.

- `EmptyParams.lean`: `emptyParams`, an instance for `VEnv.empty`. Every field
  is vacuous or `rfl` (`rank_ordered`: every rank prefix of `∅` is `∅`); no
  `sorry`. Shows the package is satisfiable.
- `NatParams.lean`: `natParams`, an instance for the environment with the four
  constants `Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec` (encodings cross-checked
  against Lean's own declarations at elaboration time) and `Pat` holding the two
  iota patterns. `henv` (`envC_ordered`, including the typing of `Nat.rec`),
  `pat_simple`, `pat_wf`, `pat_uniq` (a finite `decide`), and `ctor_syn` are
  proven. So are the ten rank fields of PLAN D4/D3 (landed by R5): `rank`
  (`Nat 0, zero 1, succ 1, rec 2`), `rank_ordered`, `type_below`, `pat_rank`,
  `pat_gen` (`Pattern.gen` evaluated by `rfl`), `pat_typed`, `pat_check`,
  `indTy_closed`, `ctor_fields_closed`, with E4's proofs
  (`docs/const-case/plan/E4/NatParamsA.lean`) carried over to `envC`. Four
  deliberate `sorry`s, each marked `-- SORRY`: `iotaZeroLam_wf`,
  `iotaSuccLam_wf` (routine typing of the lambda-wrapped rules, only used by
  `envA_ordered`), `ctor_sort_nat` (blocked on the repo's own sorried
  `IsDefEqU.sort_inv`, `Theory/Typing/Injectivity.lean`), and `pat_defeq_nat`
  (`pat_defeq` is false over `envC`, which has no rules; R12 moves the instance
  to `envA`, where E4 proves it, and proves the two `*Lam_wf` there too).
- `Schema.lean`: `Pattern.Matches.not_lam` and `Params.no_lam_rule`: no `Params`
  environment contains a rule whose left-hand side is a lambda. This is the
  finding below made precise, in two lemmas; no `sorry`.

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
pattern instances, and re-derive `SExpr.Params.extra_pat` and its model-side
uses. The plan (`docs/const-case/PLAN.md`, D5) restates it on the λ-telescope:
`df.lhs = Δ.foldr .lam L`, `df.rhs = Δ.foldr .lam R`, `L` a pattern instance,
together with the rule's *open typed equation* `Δ.reverse ⊢ L ≡ R : T` (the
plan's audit found that the typed beta steps need the body typed at the
declared codomain, and nothing else supplies that without Pi-injectivity). With
`Δ = []` it is today's field. The plan also adds `pat_defeq` (every `Pat` rule
is a definitional equality of `env`; landed by R5), which the current `natParams`
violates (`env := envC` has no rules), so the ℕ instance moves to `envA`; its two
routine typing sorries are exactly the open typed equations of the two rules.
