# Experiment E4 (the ℕ instance of the new `Params` fields): PASS

2026-10-20. Plan: `../../PLAN.md` §2 row E4; §1 D5's satisfiability table; D4/D3's fields. Base:
commit `3bccfa8` plus E3's module (attempt a's `Measure7.lean` for attempt a, attempt b's for
attempt b, so both E3 variants were exercised). Run: two independent Opus attempts, each checked
by an independent adversarial verifier (clean rebuild, grep for cheats, tracer rooted at every
constant of the module, mechanical field-by-field text comparison, `rfl` checks that the instance
is over the real `envA` with both λ-rules). Verdicts: both pass, first round, no issues. The first
run of both attempts died on an Opus session limit; the second run reused the partial modules.

## 0. Outcome

**R5's field list holds for ℕ exactly as written.** `ParamsR` (21 fields) is today's `class
Params` (`SExpr.lean:98-149`) minus the old `extra_patV`, plus D5's λ-`extra_patV` (the body of
`ExtraPatVLam`, `../E5/LamRules.lean`), plus E3's ten `RankParams` fields, each text for text
with `Params.env`/`univs`/`Pat`/`classify` read as the structure's own fields. Both attempts
checked this mechanically (`cmp_fields-b.py`; attempt a's verifier scripted its own diff), and
`natParamsR : ParamsR` over `envA` (the four ℕ constants plus the λ-wrapped `iotaSuccLam`,
`iotaZeroLam`; `Pat` = the two iota rules) proves every field except `ctor_sort`:

- `rank`: ℕ 0, `zero` 1, `succ` 1, `rec` 2 (`GenNat.lean`'s; D5's table had `succ` 2, `rec`
  3). `envA.below rank k` is extensionally `∅`, `env1`, `env3`, `envA` for `k = 0, 1, 2, ≥ 3`,
  proved equal by `VEnv.ext` (`funext` + `propext`), so `rank_ordered` is the existing `Ordered`
  chain. Real instances will need the same extensional step.
- `type_below`: each constant's type typed in the prefix of its own rank (`succCI_wf1` at
  `env1` is new; NatParams had it at `env2`).
- `pat_gen`: `Pattern.gen` evaluated by `rfl` on `envA` for both rules; the outputs are the open
  bodies of `iotaSuccLam` (4 binders stripped: `ctx = [n, s, z, motive]`, `self = [rec.type]`)
  and `iotaZeroLam` (3 binders, no self), agreeing between E3's two `Pattern.gen`s.
- `pat_typed`: `[self : rec.type, n, s, z, motive] ⊢ s n (self motive z s n) : motive (succ n)`
  in `env3` (no `rec`), and the zero rule's, with the context well-formed; the closed self type
  enters by `HasType.weak0` with `env3_ordered`.
- `pat_defeq` and the λ-`extra_patV`'s open equation are the same derivation and use **no
  inversion**: the rule's `extra` instance in `envA` at `[]`, then per binder weaken + `appDF`
  with `bvar 0`, and `beta` on each side with the λ-layers typed directly (`lam_step`/`app_step`,
  or b's `lam_open_tel`); `symm`/`trans` gives `succ_open`/`zero_open`. Spec lemma (f) was not
  needed because the output is computed by `rfl`. For `extra_patV`: `Δ` = the reversed binders,
  `OnCtx` from the binder typings lifted to `envA`, the equation by `VEnv.IsDefEq.instL`
  (`Theory/Typing/Lemmas.lean:595`, no `Ordered` needed), pattern data from NatParams'
  `zero_instance`/`succ_instance`.
- `pat_rank`, `pat_check`, `indTy_closed`, `ctor_fields_closed`, `ctor_syn`, `pat_uniq` (NatParams'
  finite `decide`): as in NatParams or routine.
- **Bonus:** NatParams' two routine sorries `iotaSuccLam_wf` and `iotaZeroLam_wf` are proved
  (layer-by-layer typing of the λ-closures), so `envA_ordered` is sorry-free.
- `ctor_sort_nat` stays sorried, restated over `envA`: it needs `IsDefEqU.sort_inv`
  (`Theory/Typing/Injectivity.lean`, itself a sorry), i.e. unique typing, as before.

Tracer at `[natParamsR]` and at all 207 (a) / 214 (b) constants of the module: exactly one
constant directly containing sorry, `ctor_sort_nat`. No field statement had to change for `envA`
(`findings_for_r5`: none, both attempts).

## 1. `ParamsR` (verbatim, attempt a; `NatParamsA.lean:22-110`)

The first eleven fields are `class Params`' `env`, `henv`, `univs`, `Pat`, `classify`,
`pat_simple`, `pat_wf`, `pat_uniq`, (λ-)`extra_patV`, `ctor_syn`, `ctor_sort`; then:

```lean
  rank : Name → Nat
  rank_ordered : ∀ k, (env.below rank k).Ordered
  type_below : ∀ {c : Name} {ci : VConstant}, env.constants c = some ci →
    (env.below rank (rank c)).IsType ci.uvars [] ci.type
  pat_rank : ∀ {p : Pattern} {r : p.RHS × p.Check} {c' : Name} {us : List VLevel},
    Pat p r → .const c' us ∈ r.1.fixedLeaves → rank c' ≤ rank p.head
  pat_gen : ∀ {p : Pattern} {r : p.RHS × p.Check}, Pat p r →
    (Pattern.gen env rank classify p r.1).isSome
  pat_typed : ∀ {p : Pattern} {r : p.RHS × p.Check} {g : PatGen} {ci : VConstant},
    Pat p r → Pattern.gen env rank classify p r.1 = some g → env.constants p.head = some ci →
    OnCtx (g.self ++ g.ctx) (fun Γ A => (env.below rank (rank p.head)).IsType ci.uvars Γ A) ∧
    (env.below rank (rank p.head)).HasType ci.uvars (g.self ++ g.ctx) g.rhsAbs (g.type.liftN g.self.length)
  pat_defeq : ∀ {p : Pattern} {r : p.RHS × p.Check} {g : PatGen} {ci : VConstant},
    Pat p r → Pattern.gen env rank classify p r.1 = some g → env.constants p.head = some ci →
    env.IsDefEq ci.uvars g.ctx g.lhs g.rhs g.type
  pat_check : ∀ {p : Pattern} {r : p.RHS × p.Check}, Pat p r → r.2 = .true
  indTy_closed : ∀ {I : Name} {k : Nat} {ci : VConstant}, classify I = some (.indTy k) →
    env.constants I = some ci → k = 0 ∧ ∃ u, ci.type = .sort u
  ctor_fields_closed : ∀ {c : Name} {cl : Classification} {ci : VConstant},
    (cl matches .ctor .. | .etaCtor ..) → classify c = some cl → env.constants c = some ci →
    ∃ (I : Name) (Ts : List VExpr), ci.type = Ts.foldr .forallE (.const I (VLevel.params ci.uvars)) ∧
      ∀ T ∈ Ts, ∃ (I' : Name) (us : List VLevel), T = .const I' us ∧ classify I' = some (.indTy 0)
```

The λ-`extra_patV` field is D5's text with `env`/`univs`/`Pat` the structure's fields (the full
`#print ParamsR` is in `Check.out` of the run; `../E5/E5-REPORT.md` §1 has the text).

## 2. Verification output (verbatim, attempt a)

```
== roots: [Lean4Lean.NatEnvA.natParamsR]
axioms reached (4):
  Classical.choice
  Quot.sound
  propext
  sorryAx
constants directly containing sorry (1):
  Lean4Lean.NatEnvA.ctor_sort_nat
'Lean4Lean.NatEnvA.natParamsR' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

`#print axioms` gives `[propext, Quot.sound]` for `pat_typed`, `pat_defeq`, `rank_ordered`,
`type_below`, `extra_patV`, `envA_ordered`, `iotaSuccLam_wf`, `iotaZeroLam_wf`, `pat_uniq_nat`,
`pat_gen`, `pat_rank`, `gen_succ`, `gen_zero`.

## 3. Notes for R5 and R12

- R5 can take `ParamsR` as the `Params` field list unchanged (replacing the old `extra_patV`).
- R12 (the ℕ instance in `docs/params/`) is essentially `NatParamsA.lean` with `ParamsR`
  replaced by the class: `natParams` moves from `envC` to `envA`, two of its three sorries close,
  `ctor_sort_nat` stays blocked on sort inversion. `docs/params/Schema.lean`'s `no_lam_rule` is
  false by design once the λ-field lands (R6).
- The module has an unscoped `deriving instance DecidableEq for Pattern` (copied from NatParams'
  `pat_uniq` section); the repo has none. Fine for an experiment; R12 should scope or keep it.

## 4. Rebuilding

`Lean4Lean/Experimental/E4/NatParamsA.lean` in a built copy of `3bccfa8` with E3's
`Lean4Lean/Experimental/E3/Measure7.lean` (attempt a's for `NatParamsA.lean`, attempt b's for
`NatParamsA-b.lean`) built; `lake build Lean4Lean.Experimental.E4.NatParamsA`, then
`lake env lean Check.lean` from the copy's root. The run used `/tmp/utt-snap15a` and
`/tmp/utt-snap15b` (scratch `/tmp/utt-exp/e4/{a,b}`).
