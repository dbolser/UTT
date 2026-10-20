# Unique typing for Lean's type theory: where this fork stands

**Repo:** [dbolser/UTT](https://github.com/dbolser/UTT), a fork of
[digama0/lean4lean](https://github.com/digama0/lean4lean). Base your work on
branch `unique-typing` (the default). `main` mirrors upstream `master`
(`67f63b0`, 2026-10-10). Everything here builds on Mario Carneiro's
metatheory in `Lean4Lean/Theory/` and his 2026 experimental work in
`Lean4Lean/Experimental/`. Licence: Apache-2.0, as upstream; contributions are
accepted under the same licence and should end up as pull requests to upstream
(its issue #16 invites proofs).

This document says what is proven, what is assumed, what is left, and how to
check each claim. The tracer (§3) is authoritative; prose is not.

## 1. The theorem

Lean4Lean Conjecture 2.7 (Carneiro, [arXiv:2403.14064](https://arxiv.org/abs/2403.14064)):

> If `Γ ⊢ e : α` and `Γ ⊢ e : β`, then `Γ ⊢ α ≡ β : U_ℓ` for some `ℓ`.

The judgment is `VEnv.IsDefEq` in `Lean4Lean/Theory/Typing/Basic.lean`, a
single inductive relation `Γ ⊢ e ≡ e' : A` over `VExpr` (de Bruijn kernel
terms, `Theory/VExpr.lean`) in an environment `VEnv` (`Theory/VEnv.lean`),
with definitional proof irrelevance, η, environment rewrite rules (`extra`)
and a typed conversion rule. The conjecture is open: the 2019 thesis proof
has a gap (its stratification does not respect substitution), and as of
October 2026 nobody has closed it. Pi- and sort-injectivity (Conjecture 2.9)
are the sister conjectures.

On the `VExpr` side, `Theory/Typing/UniqueTyping.lean` already derives
`IsDefEq.uniq` from two sorried inversion lemmas in
`Theory/Typing/Injectivity.lean` (`IsDefEqU.sort_inv`,
`IsDefEqU.forallE_inv_stratified`). It also inherits, through `VEnv.WF`, the
sorried inductive-type stubs in `Theory/Inductive.lean` (`addInduct`,
`addInduct_WF`, `VInductDecl.WF`): the inductive-type specification upstream
has not been started. So the problem on that side is **definitional inversion**.

## 2. The route (Carneiro, January–June 2026)

All the action is in `Lean4Lean/Experimental/`. Four of its sixteen modules
form the route:

| file | lines | what it is |
|---|---|---|
| `SExpr.lean` | ~3000 | `SExpr`: the same syntax with universe levels quotiented semantically (`SLevel`). `SExpr.IsDefEq` is the same rule set **plus one rule** `trans'`: transitivity where the middle term may sit at a different sort. The `Params` class (§5) bundles the environment and the pattern data. Lines ~1046–2115 are this fork's port of `Theory/Typing/Strong.lean` (`IsDefEqStrong`, `Ctx.WF`, `CtxStrong`, `EnvStrongS`, `IsDefEq.strong`). `IsDefEq.mkS` (line ~903) translates `VEnv.IsDefEq` into `SExpr.IsDefEq`. |
| `ShapeLogRel.lean` | ~6200 | A finitary domain model ("shapes", `WShape`), the interpretation of terms into it (`LE_Interp`, line ~3333), and a logical relation over it (`LogRel`, `LRS.DefEq`, `LRS.TyDefEq`). This is the Lean form of [*Definitional Inversion, Without Normalisation*](https://arxiv.org/abs/2607.13662) (Carneiro, Coquand, Frabetti Mathieu, Lennon-Bertrand, Melliès, Weirich, 2026), extended with constants, constructor shapes and pattern rules. No normalisation is used anywhere; Lean's theory is not normalising. |
| `ShapeLogRelAdequacy.lean` | ~560 | The fundamental lemma `LR.adequacy`, and from it Pi-injectivity `forallE_inv`, sort injectivity `sort_inv` and sort/Pi disjointness `sort_forallE_inv`, all for the `trans'` system. |
| `UniqueTyping.lean` | ~390 | Unique typing for the `trans'` system by plain induction (`HasTypeS.uniq`); `uniq_sort`; `IsDefEq.iff_isDefEq'`, showing `trans'` is admissible, so the `trans'` system equals `IsDefEq'`, which has exactly Lean's rules; the final corollary; and reflection of sort injectivity and sort/Pi disjointness back to `VExpr`. |

The final theorem, for `SExpr` and under a well-formed context, exactly as
`Theory/` states things with `OnCtx Γ (env.IsType U)`:

```lean
theorem IsDefEq'.uniq (hΓ : ⊢ Γ) (h1 : IsDefEq' Γ e₁ e₂ A) (h2 : IsDefEq' Γ e₂ e₃ B) :
    ∃ u, IsDefEq' Γ A B (.sort u)
```

Why `trans'` matters: the naive induction needs to chain `α ≡ β : U_i` with
`β ≡ γ : U_j` before knowing `i = j`, and `i = j` is itself an instance of
unique typing. `trans'` lets the induction go through first; sort uniqueness
then shows `trans'` was admissible all along.

## 3. Check the claims yourself

Building from scratch: install [elan](https://github.com/leanprover/elan);
the toolchain is pinned in `lean-toolchain` (`v4.33.0-rc2`, a release
candidate) and Batteries in `lake-manifest.json`, which the first build
downloads. The first build compiles Batteries, the `Theory` library and the
6200-line logical relation; expect several minutes. Later builds of the route
take about a minute. Warnings about `sorry` are expected: the `#print axioms`
lines in the route files run at build time.

```sh
lake build Lean4Lean.Experimental.UniqueTyping   # the route (plain `lake build` does not build Experimental)
lake env lean scripts/TraceSorry.lean
```

`scripts/TraceSorry.lean` walks the dependency graph of each root and prints
the axioms it reaches and every constant whose own body contains `sorry`. Its
first block, for the final theorem, is at present:

```
== roots: [Lean4Lean.SExpr.IsDefEq'.uniq]
axioms reached (4):
  Classical.choice
  Quot.sound
  propext
  sorryAx
constants directly containing sorry (1):
  Lean4Lean.SExpr.LR.pat_leaf_1a
```

No project-specific axioms remain. The one sorry on the path is the pattern
leaf of the fundamental lemma's `const` case (§6): since plan items R7, R8
and R9 landed, the `const` case and its spine lemma are proved up to that
leaf. The environment-side theorems
(`Params.const_wf`, `defeq_wf`, `extra_pat`, `ctor_ty`, `envStrongS`,
`IsDefEq.strong`) reach no sorry at all. The tracer reports the path only:
`grep sorry` finds about twenty more sorried lemmas in `SExpr.lean` and
`ShapeLogRel.lean` inherited from upstream and off the path (for example
`WHRed.subst`, `WHRedS.defeq`, `InferType.hasType`, `Shape.WF.plift`).
The plan in §6 is built not to need `WHRedS.defeq` (subject reduction): it
puts typed reductions into the relation and the typing of rules into `Params`.

Upstream CI (`.github/workflows/ci.yml`) builds the whole `Experimental`
library, all sixteen modules, so keep `lake build Lean4Lean.Experimental`
green too. The tracer is not yet a pass/fail CI check (a good first task, §8).

## 4. What this fork changed

`git log main..unique-typing` lists the commits. In short:

- Two sorried statements upstream were false or unprovable as written.
  `Ctx.SubstEq.lift` could not be proven because `Ctx.SubstEq` had only an
  identity base case; it now has a `weak` constructor (`8fae8db`). And
  `IsDefEq.strong : Γ ⊢ e1 ≡ e2 : A → IsDefEqStrong Γ e1 e2 A` is false
  without a well-formed context: `[bvar 5] ⊢ bvar 0 : bvar 6` holds in the
  weak system and has no strong derivation (`IsDefEq.strong_counterexample`,
  `SExpr.lean` ~1464). The fix threads `⊢ Γ` (`Ctx.WF`, ~1185) through the
  whole chain; internally `CtxStrong` (~1471) is the strong form built from it
  via `Params.envStrongS` (~1946), and `IsDefEq.strongS` (~1767) is the actual
  induction (`30996fa`, `cd97547`).
- `WHRed.determ` is proven, from `pat_simple` and `pat_uniq` alone (`e8c6bd8`).
- The axiom `Params.extra_pat` and the sorried `Params.ctor_ty` are now
  theorems derived from `VExpr`-level `Params` fields (`09407ee`, `cb5fae8`,
  `ae87af1`). Constructor types had to be assumed *syntactically* a
  Π-telescope, which is what Lean's kernel guarantees; a defeq-only assumption
  leaves a circularity when strengthening derivations.
- Typing of environment constants in `SExpr` (`Params.const_wf`,
  `Params.defeq_wf`) is derived from `henv : env.Ordered` through the
  translation (`c6fe5e8`).
- The translation `IsDefEq.mkS` is a port of the closed upstream PR #37
  (argumentcomputer), including its `mkInst` fix for universe parameters
  (`e13a52d`). Sort injectivity and sort/Pi disjointness reflect back to
  `VExpr` (`sort_invS`, `sort_forallE_invS`); Pi-injectivity reflects only to
  an `SExpr` statement so far (`forallE_invS`), see §7.
- The `major` rule for `SExpr`'s `WHRed` (reduction in major-premise
  position, §6) is in, with `IsMajorPremise`, determinism and weakening
  lemmas, and no new `Params` fields (`b2516c4`). `WHRed.subst` and
  `WHRedS.weakU_inv` now take an explicit defeq-transport hypothesis, because
  their `extra` cases were sorried upstream; the off-path `InferType` lemmas
  keep named, documented sorries for it.
- The syntactic spine lemmas of the ctor-clause plan (§6): `spine`, `headE`,
  `args`, `spine_inj`, `Pattern.head`, `Pattern.WF.head_symb`,
  `Pattern.MatchesS.headE`/`head_eq`/`not_symb`, `WHNF.of_headE`,
  `WHNF.ctorSpine`, `WHNF.indTySpine`, `WHRedS.ctorSpine_eq`,
  `WHRedS.ctorSpine_determ`. Pure syntax, no new `Params` fields.
- `LR.Adequate.mono_r` (`ShapeLogRelAdequacy.lean`): retype an `Adequate` fact
  down to a compatible shape, a port of the artifact's lemma that every
  const-case design uses (`3c35f59`).
- The stage-1a constructor clause of the plan (`LRS.CtorDefEq` at
  `(ctor c l, indTy)`, `TyDefEq` at `indTy` as a typed reduction to one
  `const I ls`), with every `LogRel` field and the lift lemmas re-proved at
  the new cases and `ShapeLogRelAdequacy.lean` unchanged (plan D1/D2, item R3,
  after experiment E2; `2c5a205`). The tracer output is identical.
- The strong judgment indexed by an environment: `IsDefEqStrong (E : VEnv)`
  with `⊢ₛ` as `IsDefEqStrong Params.env`, `IsDefEqStrong.mono`, the
  rank-bounded sub-environment `VEnv.below` and its lemmas, `exists_below`,
  the translation `mkSE` over any `E` (`mkS` is now its `Params.env`
  instance), `weak_append`, the Π-telescope inversion `telescope`, and `E`
  forms of `defeq` and `LE_Interp.soundS`. `IsDefEq.strong`, `strongS`,
  `envStrongS`, `mkS` and every statement in `ShapeLogRelAdequacy.lean` keep
  their types (plan D4, item R4; `9dcefbc`). The tracer output is identical.
- `Pattern.gen`, the computed pattern context of a rewrite rule (`PatGen`,
  `VExpr.piTelescope`, the per-occurrence self variables), with its seven
  specification lemmas, and the ten `Params` fields of the rank measure and
  the stage-1a restriction (`rank`, `rank_ordered`, `type_below`, `pat_rank`,
  `pat_gen`, `pat_typed`, `pat_defeq`, `pat_check`, `indTy_closed`,
  `ctor_fields_closed`), text for text as experiments E3 and E4 pinned them.
  The definitions sit before `class Params` in `SExpr.lean`; the `SExpr`-level
  lemmas are the new module `Experimental/PatternGen.lean` (plan item R5).
  The tracer output is identical. Until R6 and R12, `emptyParams` is the only
  sorry-free instance of the class: `natParams` (over the rule-free `envC`)
  carries `pat_defeq` as a marked sorry, since that field is false without
  the rules (`docs/params/README.md`).
- The fundamental lemma by well-founded induction on the rank bound:
  `LR.adequacy_rank` proves the 14 cases over derivations in
  `Params.env.below rank k` with the well-founded hypothesis `LR.WFIH`, the
  13 existing case proofs going through unchanged (sub-derivations pass
  through `soundSE`/`defeqE` and `VEnv.below_le`), and the `const` case is
  the local induction `LR.const_local` (experiment E3) down to the pinned
  spine-lemma stub `LR.const_spine`, which calls the pinned pattern-leaf stub
  `LR.pat_leaf_1a`; `EnvStrongR`, `LR.WFIH`/`ConstGoal`/`LocalIH` and
  `Valuation.ofRargs` come with it. `LR.adequacy` keeps its statement and is
  recovered through `exists_below` and `Nat.strongRecOn` (plan items R7+R8;
  `3a28c52`). The one sorry on the route moved from `LR.adequacy` to
  `LR.const_spine`; the axiom set is unchanged.
- `extra_patV` restated on λ-telescopes with the rule's open typed equation
  (plan D5, experiment E5): `Params.extra_pat` is its `SExpr` translation, and
  the `extra` cases of `LE_Interp.strongSoundS` and `LR.adequacy_rank` are
  re-proved for λ-rules (`strongSoundS_extra_lam`, `LR.lamRule`) without
  `IsDefEq.extra`. The ℕ instance `natParams` moves to the environment with
  its two λ-wrapped rules, every field proved but `ctor_sort_nat`;
  `docs/params/check.sh` asserts the sorry counts (items R6+R12). The tracer
  output is identical.
- The spine lemma `LR.const_spine` proved (item R9): induction on the `Const`
  derivation, with `Const.beyond` for arguments past the syntactic
  Π-telescope, the `(lam, forallE)` row at the pushed valuation with
  `Adequate.cons` on the next domain, the `(ctor, indTy)` row read off the
  substitution entries, `TyDefEq`'s `indTy` row, and the pattern leaf at
  `Const.pat`. Two independent attempts proved it with the same statement;
  the one sorry on the route moved to `LR.pat_leaf_1a`.
- Typed reductions in the logical relation (`TyRedS`, `TWHRedS`, `AmbSort`;
  the `sort_iff`, `sort_iff_ty`, `whr`, `whr_ty` fields take typed reductions,
  `(⊥, ·)` stays `True`; the other fifteen fields and every statement in
  `ShapeLogRelAdequacy.lean` are unchanged), with the 13 proven cases of
  `LR.adequacy` re-proved over it: plan item D6, landed as R1+R2 after
  experiment E1 (`c6b258f`). The tracer output is identical before and after.

## 5. What is assumed: the `Params` class

`SExpr.Params` (`SExpr.lean`, top) is a hypothesis package, not an axiom. Two
instances live in `docs/params/` (experiments, not part of the build; see its
`README.md`). Its fields:

- `env`, `henv : env.Ordered`, `univs`: the environment and ambient universe count.
- `Pat`, `classify`, `pat_simple`, `pat_wf`, `pat_uniq`: every rewrite rule is
  a simple pattern (delta or iota), heads are classified (`symb`, `ctor`,
  `etaCtor`, `indTy`), and overlapping patterns coincide.
- `extra_patV`: every instantiated environment rule is the λ-closure, over
  its binder telescope, of a well-typed open equation whose left-hand side is
  an instance of such a pattern, with its side conditions holding (plan D5,
  landed by R6).
- `ctor_syn`, `ctor_sort`: constructor types are syntactically a Π-telescope
  over the inductive type, at a sort that is never `Prop`.
- `rank`, `rank_ordered`, `type_below`, `pat_rank`, `pat_gen`, `pat_typed`,
  `pat_defeq`, `pat_check`: a rank on constants such that each rank-bounded
  sub-environment is ordered, every constant's type lives below its rank, and
  every rule's right-hand side is typed in its computed pattern context
  (`Pattern.gen`) below the head's rank, and is a definitional equality of the
  environment (plan D4, landed by R5).
- `indTy_closed`, `ctor_fields_closed`: the stage-1a restriction, every
  inductive type is a closed sort and every constructor field is a closed
  inductive constant (plan D3; `ℕ`, `Bool`, monomorphic lists and trees; not
  `List α` or `Prod`).

`extra_patV` was first stated for rules whose left-hand side is a bare pattern
instance, which does not fit schematic rules: for the `ℕ` environment with its
two iota rules lambda-wrapped (Lean4Lean's own `vdefeq` convention) that form
is false for every choice of `Pat`, because `Pattern.Matches` has no `lam` case
(`docs/params/NatParams.lean`: `extra_patV_false_envA`, kept against the old
form), and the open-`bvar` encoding is pattern-matchable but not `VDefEq.WF`
(`iotaZeroOpen_not_wf`). The field is now stated on λ-telescopes with the
rule's open typed equation (D5 of `docs/const-case/PLAN.md`, experiment E5,
landed by R6), and `natParams` lives over the environment that contains the
two λ-wrapped rules, with every field proved except `ctor_sort` (experiment
E4, landed by R12; `docs/params/README.md` has the details). The remaining
sorry there, `ctor_sort_nat`, is blocked on the repo's own sorried
`IsDefEqU.sort_inv`.

Building a `Params` instance for the environments Lean4Lean actually produces
depends on the inductive-type specification in `Theory/Inductive.lean`, which
is a stub. The paper's conclusion names (co)inductive types and proof
irrelevance with axiom K as not yet covered. This fork's shape model
additionally excludes K-like reduction, iota on Prop-valued inductives
(`Eq.rec`, `Acc.rec`), universe-polymorphic inductives instantiable at `Prop`
(`PUnit`, and `Quot.mk`, so quotients are excluded too), and structure eta on
variables; see `docs/const-case/DESIGN-fuel-measure.md` §7 for how each
exclusion is encoded (`pat_wf`, `ctor_sort`, the absence of a `major`-style eta
rule). These are limitations of the current model, not of the route.

## 6. The open problem: the `const` case of `LR.adequacy`

`LR.adequacy` (`ShapeLogRelAdequacy.lean`) is proven by well-founded
induction on a rank bound and then on the strong derivation
(`LR.adequacy_rank`); all 14 cases are in, and the `const` case goes through
the local induction `LR.const_local` and the spine lemma `LR.const_spine`
(induction on the constant's interpretation, R9) down to the pattern leaf
`LR.pat_leaf_1a`, which is the one remaining sorry (its statement is pinned;
experiment E6 is its proof). The `const` case had been a sorry since the model started
interpreting constants non-trivially (April 2026). Three
independent design analyses on this fork, a five-lens adversarial review of
them, and a merged, audited plan are in `docs/const-case/`; start with
`docs/const-case/PLAN.md`. `./check.sh` there typechecks every experiment
against the current tree.

**It is a design gap, not a proof gap.** The logical relation is `True` at
inductive type-shapes: `LRS.DefEq` (`ShapeLogRel.lean` ~5619) has
`| .indTy => True` (~5633), and `LRS.TyDefEq` (~5438) is `True` at `ctor` and
`indTy`. So a variable can be related at a constructor shape such as
`succ zero`, the model then fires a recursor rule at the shape level, and
adequacy demands a syntactic head reduction of `rec … (bvar 0)` that cannot
happen. With the relation unchanged the lemma is false, not merely unproven
(`Stuck.lean`, `Subst1.lean`, and §2 of `DESIGN-fuel-measure.md`). Both
`True` clauses have to change.

**What has to change** (the plan's decisions; Lean statements, evidence and
the ordered work items are in `PLAN.md`).

1. **A constructor clause** (stage 1a done, `2c5a205`) in `LRS.DefEq` at `(m = ctor c l, a = indTy)`:
   both terms head-reduce, *with a typed equation*, to `c` applied to a spine
   whose fields are related at the shapes in `l`. This is the paper's
   treatment of `ℕ`; its Lean mechanisation (supplementary material at
   [anonymous.4open.science/r/domain-semantics-lean-BEE7](https://anonymous.4open.science/r/domain-semantics-lean-BEE7))
   has it for `ℕ`, `Σ`, unit, `Id`, `Prop` and a fixpoint combinator, with
   every logical-relation field re-proved. The question for arbitrary
   inductives is where a field's *type* shape comes from. Quantifying over
   type shapes (design C) is not level-invariant (`CounterC.lean`), so the
   codes must be finite data on the constructor shape (design A,
   `ClauseA.lean`). The plan stages this: stage 1a relates fields at the one
   canonical type shape `indTy`, which works when every field type is a
   closed inductive constant (`ℕ`, `Bool`, `Int`, monomorphic lists and
   trees), and changes no shape definition; stage 1b adds the Π-codes. The
   stage-1a clause is in (`LRS.CtorDefEq`, `LRS.FieldRel`, `LRS.FieldsEq`;
   experiment E2, `docs/const-case/plan/E2/`), with all 19 fields and the
   lift lemmas re-proved and the adequacy cases untouched. `TyDefEq` at
   `indTy` is now "both types reduce, typed, to the same `const I ls`".
2. **A `major` rule** in `SExpr`'s `WHRed` (reduction in major-premise
   position), so a recursor whose argument merely *reduces* to a constructor
   can fire. Done (`b2516c4`), together with the syntactic spine lemmas and
   `LR.Adequate.mono_r` (§4).
3. **A termination measure** for rule right-hand sides, which are not
   subderivations. The local induction on the interpretation derivation `hM`
   (from the mechanisation's fixpoint case) is necessary but not sufficient:
   its hypothesis fires only at the self-constant (`IHVacuous.lean`). The
   outer source is well-founded induction on an environment rank, over an
   environment-indexed strong judgment `IsDefEqStrong (E : VEnv)`, in
   lexicographic order (rank bound, derivation, `hM`, then the `Const`/`RHS`
   premises). `IsDefEqStrong.const` gets no new premise; `IsDefEq.strongS`
   and `envStrongS` are unchanged; `mkS` is generalised. The judgment,
   `VEnv.below`, `mkSE`, `weak_append` and `telescope` are in (R4,
   `9dcefbc`); the rank itself is next. New `Params` fields
   give the rank, the rank-bounded typing of constant types and of each rule's
   right-hand side in a computed pattern context (`Pattern.gen`), and the rule
   as a definitional equality (`pat_defeq`). Experiment E3 (two verified
   attempts, 2026-10-20; `docs/const-case/plan/E3/`) has `Pattern.gen` as a
   function with its seven specification lemmas, the ten fields exactly, and
   the local induction `const_local` proved up to the spine lemma; all of it
   landed as R5 (the fields and `Pattern.gen`), R7 (`LR.adequacy_rank`), R8
   (the measure, `3a28c52`) and R9 (the spine lemma). What is left of this
   item is the pattern leaf (E6, R10).
4. **Typed reductions in the relation** (done, `c6b258f`). All three designs missed this. At
   the pattern leaf the rule's right-hand side has type `motive (c Zs)` and
   the goal has type `motive x` with `x ⤳* c Zs`; converting between them at
   a Π result shape needs a *typed* `Γ ⊢ x ≡ c Zs : I`. The untyped `whr`
   field cannot supply it, and subject reduction (`WHRedS.defeq`) is a sorry
   whose `VExpr` twin already reaches `sorryAx`. So `whr` and `whr_ty` are now
   typed (`TWHRedS`, `TyRedS`), `(⊥, ·)` stays `True`, and the hard case, a
   typed `whr` at `(lam, forallE)`, goes through without a `⊢ Γ` index
   (`LRS.LamDefEq.whr_typed`). This was the plan's main bet; experiment E1
   tested it and R1+R2 landed it.
5. **`extra_patV` on λ-telescopes.** Lean4Lean's rules are λ-closed schemas
   (§5). The restated field strips the binders and, the audit found, must
   also carry the rule's open typed equation `Δ ⊢ L ≡ R : T`: each typed beta
   step needs the body typed at the declared codomain, and the only other
   source is Pi-injectivity, a consequence of adequacy. The ℕ instance moves
   to the environment that contains its rules (`envA`). Experiment E5 (two
   verified attempts, 2026-10-20; `docs/const-case/plan/E5/`) proves both
   `extra` cases for λ-rules from the restated field exactly as written, with
   no amendment; the landing is plan item R6.

Stage 1a is a restriction: its `Params` fields (`indTy_closed`,
`ctor_fields_closed`) rule out every parametric or indexed inductive with
rules, so the stage-1a theorem does not cover Lean's prelude. Stage 2
(parameters: syntactic argument equalities plus semantic relatedness in
`TyDefEq` at `indTy`, `Reconcile.lean` for the field retype) is designed as a
route only.

**First experiment, E1 (the typed-LR spike).** Copy the `LogRel` block of
`ShapeLogRel.lean` (lines ~5272–6117) and the `Adequate` definitions into a
scratch namespace, make `sort_iff`, `whr` and `whr_ty` typed, and re-prove
`LR0`, the 19 fields of the `LRS` instance and the lift lemmas. Pass: no
`sorry`. If it fails, the fallback is the artifact's full typed design (`bot`
takes `TyDefEq A A a`; an `isType` field), which costs an obligation at each
of the 15 `bot` call sites in `ShapeLogRelAdequacy.lean`. `PLAN.md` §2–3.

**E1 passed (2026-10-19).** Two independent attempts, each checked by an
independent verifier: the typed relation closes all 19 fields, both lift
directions and `Subst1`/`SubstWF` with no sorry, and all 13 proven cases of
`LR.adequacy` go through over it with the `const` case as the only sorry. No
fallback was needed; subject reduction was not used. Forced side changes:
`LR0.DefEq` takes the ambient type, the simp lemma `LRS.DefEq.sort_a` splits
in two, `LRS.LamDefEq.whr` becomes typed. Report and files:
`docs/const-case/plan/E1/`. The transcription into `ShapeLogRel.lean` and
`ShapeLogRelAdequacy.lean` (plan items R1+R2) landed as `c6b258f`; the eleven
`docs/` experiments that were written against the untyped fields are marked
historical (`0fadc0c`). The stage-1a constructor clause followed the same
route (experiment E2, two verified attempts, then R3 as `2c5a205`), and the
environment-indexed strong judgment landed as R4 (`9dcefbc`, verified
independently; nine more `docs/` experiments went historical). E3 (the rank
measure and `Pattern.gen`), E5 (λ-wrapped rules) and E4 (the ℕ instance of
the new fields) passed on 2026-10-20, two verified attempts each, and R5 (the
fields, `Pattern.gen` and its lemmas in the repo) landed the same day, as did
R7 and R8 (`3a28c52`: the rank induction and the measure; the one sorry is now
the spine lemma). E6a (the pattern-leaf field lowering) found the plan's
pinned lowering statement false and proved a corrected one; its one upstream
change, the hypothesis `hR` on the spine lemma and the pattern leaf, is in.
R6 and R12 (the λ-rule field and the ℕ instance over the environment with
rules) and R9 (the spine lemma, two verified attempts) landed the same
evening. Next: E6 (the pattern leaf proper), then R10 (landing it) and R11.

**Known risks** (`PLAN.md` §4 and its audit log). The shape-level iota match
binds a field variable to the raw field shape, and a constructor shape counts
as typed at `indTy` whatever its fields are (`ctor succ [sort]`), while
`SubstWF.cons` needs typed entries. Experiment E6a (2026-10-20,
`docs/const-case/plan/E6a/`) settled this: lowering fields to their typed part
at the leaf works, with the lowering lemma proved sorry-free, but the plan's
pinned statement of it was false (two formal refutations) and the corrected
one needs the pattern leaf to pass the interpretation of the rule's fixed
leaves (`hR`, now a hypothesis of the spine lemma and the pattern leaf) and a
small fact about recursor-argument and field positions. The spine lemma must
be stated for every valuation above `Valuation.ofRargs`, because `Const.lam`
ranges over graph pairs rather than typed inputs. Parametric fields are stage 2.

## 7. After the `SExpr` theorem

Backward reflection to `VExpr` is incomplete for Pi-injectivity: an inverse
translation `IsDefEq' → VEnv.IsDefEq` is needed (choose representatives for
levels and preimages for intermediate terms). With it, the two sorries in
`Theory/Typing/Injectivity.lean` on the path can be discharged and
`Theory/Typing/UniqueTyping.lean` becomes a theorem about Lean's `VExpr`
theory, under a `Params` instance and modulo the `Theory/Inductive.lean` stubs.

## 8. Contributing

Workflow that has worked here:

- Prove in a scratch file first (`import Lean4Lean.Experimental.SExpr` or
  `...ShapeLogRelAdequacy`, `namespace Lean4Lean.SExpr`, `variable [Params]`),
  check `#print axioms`, then splice. The tracer function in
  `scripts/TraceSorry.lean` can be pasted into any scratch file.
- Statements matter as much as proofs: two sorried statements upstream were
  false as written. Never claim a result while the tracer shows `sorryAx` or a
  custom axiom on its path.
- Keep commits per lemma; keep `lake build Lean4Lean.Experimental` green;
  include the tracer's first block in the PR description.
- Open pull requests against `unique-typing` here. Upstream is
  `digama0/lean4lean`; the TYPES 2025 talk
  ([slides](https://msp.cis.strath.ac.uk/types2025/slides/TYPES2025-slides31.pdf))
  ends its unique-typing section with "Type theorists wanted!".

Good first tasks:

- Turn `scripts/TraceSorry.lean` into a pass/fail check (expected sorry set
  for `IsDefEq'.uniq` is exactly `{LR.adequacy}`, no axioms beyond the three
  standard ones) and add it to CI on this fork.
- Experiments E3 (the rank measure and `Pattern.gen`, `docs/const-case/PLAN.md`
  §2) and E6a (field-entry lowering): scratch only, on the plan's critical path
  now that E1 has passed.
- Restate `extra_patV` on λ-telescopes with the rule's open typed equation
  (`PLAN.md` D5) and re-derive `Params.extra_pat` (`SExpr.lean` ~1006) and its
  model-side uses; then move the ℕ instance to `envA` (`docs/params/`).
- `ctor_sort` for `ℕ` (`docs/params/NatParams.lean`, `ctor_sort_nat`) needs
  `IsDefEqU.sort_inv` (`Theory/Typing/Injectivity.lean`); currently `sorry`.
- Prove `WHRedS.defeq` in `SExpr.lean` (head reduction is a definitional
  equality at the term's type). Off the path and not used by the plan, but
  an inherited sorry worth closing.

## 9. Reading list

- Lean4Lean paper, §2.4 (the conjectures): [arXiv:2403.14064](https://arxiv.org/abs/2403.14064).
- *Definitional Inversion, Without Normalisation*: [arXiv:2607.13662](https://arxiv.org/abs/2607.13662),
  and its Lean mechanisation (link in §6).
- Carneiro's thesis, *The Type Theory of Lean* (2019), for the original
  gapped proof and the `≡p` Church–Rosser statement:
  [github.com/digama0/lean-type-theory](https://github.com/digama0/lean-type-theory).
- Upstream issue #16 (contributing proofs) and closed PR #37 (the translation).
