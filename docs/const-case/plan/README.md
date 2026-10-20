# Evidence files for `PLAN.md`

Scratch Lean files written by the synthesizer, the refuters and the auditors
of the plan, copied verbatim (their docstrings cite `/tmp/utt-snap6`, a build
of commit `3c35f59`, and `/tmp/utt-exp/plan/...` scratch paths). Each imports
`Lean4Lean.Experimental.ShapeLogRelAdequacy` (`AxDepsV.lean` only
`Theory.Typing.Strong`); none is part of the build. The files in `historical/`
were typechecked at `3c35f59` and stopped compiling when the plan's changes
landed; `../check.sh` skips that directory. `TypedWhr.lean` and
`CtorClause1a.lean` clash with the repo's own `TyRedS`/`TWHRedS`/`whr_typed`
since R1+R2, which is where they went. `WeakE`, `MkSE`, `ForallInvE`,
`EmptyBelow`, `JunkGen`, `PatLeafStmt`, `PatLeafStmt2` and `RhsLowerStmt`
clash with `VEnv.below`, `IsDefEqStrong E`, `mkSE` and `telescope` since R4,
likewise. `../check.sh` typechecks the rest. All are sorry-free except the
four `*Stmt*.lean` files, whose theorem bodies are deliberate sorries (they
pin statements for the experiments). `PLAN.md` cites them by bare name, with the tag [T].

The plan's own constructions (D1, D6):

| file | shows |
|---|---|
| `TypedWhr.lean` | `TyDefEq_forallE_typed`: converting along a Π type shape needs a *typed* equation of the arguments. `inst_congr_beta`, `LRS.LamDefEq.whr_typed`: the typed `whr` at `(lam, forallE)` goes through without a `⊢ Γ` index. |
| `FieldRelLift.lean` | `FieldRel.lift_aux` on its own (also inside `CtorClause1a.lean`): the stage-1a field relation is level-invariant in both directions. |
| `CtorClause1a.lean` | The stage-1a clause (`TyRedS`, `TWHRedS`, `FieldRel`, `FieldsEq`, `CtorDefEq`) over an abstract `IH`, with `left`, `symm`, `trans`, `mono_l`, typed `whr`, `conv`, `not_sort` (so `trans'` is vacuous) and `lift_aux` in both directions. |
| `AxSR.lean` | `#print axioms` of the `VExpr` subject-reduction lemma `WHRedS.defeq` reaches `sorryAx`, so subject reduction is not available to the plan. |

Why the alternatives fail (§0 of the plan):

| file | shows |
|---|---|
| `GenericIH.lean` | A two-type spine clause `SpineDefEq2` over an abstract `IH` with `left`/`symm`/`trans`/`mono`/`lift_aux`; `whr_fails_symb`: the clause must store `classify c = .ctor`. Stage 1b's clause. |
| `GenericSpine.lean`, `WeirdLR.lean` | `ClauseA.lean`'s clause is over the concrete tower `LR Γ`; over an abstract `IH` its `conv`/`symm`/`trans` need an inter-level lift that is not a `LogRel` field, and a `LogRel` exists for which it fails. |
| `ArityBound.lean`, `Depth.lean` | With `hasType (ctor c l k) indTy := SpineTyped l k` unrelaxed, a level-1 constructor shape can carry at most one field. Why stage 1b lets a `⊥` code type `⊥` fields. |
| `NaiveMono.lean`, `NotDownClosed.lean` | Design B's `∃ t` field clause fails `mono_l`: `HasType` is not downward closed in the element shape. |
| `RealisedC.lean`, `CFull.lean` | `CounterC.lean` refutes one conjunct of design C's clause, not the full clause; the full clause's lift ⇐ direction is simply unproven (it is the fundamental lemma one level up). |
| `MonoL.lean` | Design C's "store the valuation" fix for `mono_l` rests on the wrong direction of `LE_Interp.mono_l`; the `∀ q ≤ p` weakening is what is needed. |
| `CtorNoLink.lean`, `RefuteModel.lean` | Design C's `IndTyRed` ambient relates the type to no particular inductive spine, so it carries nothing about parameters; other model-lens checks. |
| `KappaMonoR1.lean` | Codes on the *type* shape (κ, `indTy qs kI K`) make `LogRel.mono_r_1` false. Why codes go on the constructor element. |
| `Mismatch.lean`, `FieldRetypeT.lean` | Parametric fields: a compatible-but-incomparable pair of parameter type shapes with a non-trivial common element; the field retype (`Reconcile.lean`) goes through with a `TShape` bound, one level above the fields. Stage 2. |
| `RestrictVacuous.lean` | The "proof field" disjunct of a shape-closed field restriction is vacuous as stated. |
| `QuotLevel.lean` | `Quot.mk.{0}` lives in `Prop`, so `ctor_sort` excludes quotients. |

The measure (D4):

| file | shows |
|---|---|
| `HasTypeGap.lean` | `HasType` is not downward closed, and `SubstWF.cons` pushes typed shapes only, so the motive must carry an ∃-typed-upper-bound. |
| `PatTypedDegenerate.lean` | An existentially quantified typing of the rule right-hand side is satisfied by junk witnesses; the pattern context must be *computed* (`Pattern.gen`). |
| `../Measure.lean` | The rank measure and the `adequacy_rank` skeleton (three marked sorries). |
| `../IHVacuous.lean` | The local `hM` induction alone is not enough. |

Audit round 1 (see the plan's audit log):

| file | shows |
|---|---|
| `LamRuleTyped.lean` | Typed beta for a λ-wrapped rule needs the body typed at the declared codomain; λ-inversion gives *some* type, and matching it is Pi-injectivity, a consequence of adequacy. With the rule's open typed equation the step is two lines. Why `extra_patV` carries that equation. |
| `UntypedField.lean` | `ctor c [sort]` is typed at `indTy` by `rfl` while its field is typed at nothing; the shape-level iota match binds a field variable to that raw shape; the stage-1a `FieldRel` is vacuous there. Open risk in `STATUS.md` §6. |
| `WeakE.lean` | `IsDefEqStrong` with an explicit environment `E ≤ Params.env`: `closedN`, `weak'`, `weak0` re-proved for it. Needed by the rank induction. |
| `PatLeafStmt.lean` | The statements of `LR.pat_leaf_1a` (the interface between the spine lemma and the pattern leaf, experiment E6) and of the amended spine lemma `LR.const_spine`, typechecked as statements with stand-ins for the not-yet-existing typed relation, `Params.rank` and `IsDefEqStrong E`. Bodies are marked sorries. |

Audit round 2:

| file | shows |
|---|---|
| `JunkGen.lean` | `pat_leaf_1a` as first stated took `g : PatGen` with nothing tying it to the rule; a junk `g` satisfies its typing hypotheses for every rule. Hence the hypothesis `Pattern.gen … = some g` and the `Pattern.gen` specification lemmas. |
| `PatLeafStmt2.lean` | `pat_leaf_1a` restated with the hypothesis `Pattern.gen … = some g` (supersedes `PatLeafStmt.lean`); statements only, two marked sorries. |
| `Beyond.lean` | `Const.beyond`: a `Const` derivation at more arguments than the syntactic Π-telescope of the constant's type is `⊥`, from three arity bounds (`ctor_syn`, `indTy_closed`, `pat_gen`). Closes the `lam` case of the spine lemma when the remaining type is a Π only after delta. |
| `AxDeps.lean`, `AxDepsV.lean` | `#print axioms` of every repo lemma the plan uses as a building block: all sorry-free except `WHRedS.defeq`, which the plan does not use. |

Audit round 3:

| file | shows |
|---|---|
| `MkSE.lean` | `mkSE`, the translation lemma over an environment-indexed strong judgment, ported from `mkS` with env-generic `hasTypeS`/`isType'` and a `CtorProviderE`. Pins R4's real size. |
| `EmptyBelow.lean` | `rank_ordered` holds for the empty environment: `VEnv.below` of `∅` is `∅`. |
| `SelfType.lean` | `mkInst_instL`: the type of a self entry in the pattern context, `mkInst ls (ci.type.instL us)`, is the constant's own instantiated type, so the local induction hypothesis plugs into `Adequate.cons` for self entries. Hence the `gen_self` specification lemma. |
| `ForallInvE.lean` | `IsDefEqStrong.forallE_inv'` over an arbitrary environment, and the telescope lemma that gives the spine lemma's `lam` case a rank-bounded derivation of each domain type. |
| `ExtraLamStmt.lean` | The statement of the `extra` case of `strongSoundS` for λ-wrapped rules, with the λ-form `extra_patV` as an explicit hypothesis (experiment E5); one marked sorry. |
| `RhsLowerStmt.lean` | `Valuation.lower` and the statement of the lowering lemma `rhs_lower` for the pattern leaf (experiment E6a); three marked sorries, two inherited from `PatLeafStmt2.lean`. |

## E5/ (λ-wrapped rules, PASSED 2026-10-20)

`E5/E5-REPORT.md` is the report. `E5/LamRules.lean` has D5's λ-`extra_patV` as the hypothesis
`ExtraPatVLam` (verbatim `ExtraLamStmt.lean`), its `SExpr` translation `T.extra_pat_lam` and
`T.strongSoundS_extra_lam` (the `extra` case of `strongSoundS` for a λ-rule, statement as
`ExtraLamStmt.lean:25`), all sorry-free; `E5/LamAdequacy.lean` is `ShapeLogRelAdequacy.lean:9-562`
with `hlam` threaded and the `extra` case re-proved for λ-rules (only the `const`-case sorry).
`E5/LamRules-b.lean` is the second attempt's variant (per-binder context conjunct). `E5/Check.lean`
and `E5/Reach.lean` are the axiom, tracer and reachability checks. Module files, excluded from
`../check.sh`; the report's §5 says how to rebuild. D5 needs no amendment; R6 lands it.

## E2/ (the stage-1a constructor clause, PASSED 2026-10-19)

`E2/E2-REPORT.md` is the report. `E2/CtorLR.lean` is the typed `LogRel` block
(`ShapeLogRel.lean:5280-6216` at `dc61a99`) with D1 and D2 wired in, sorry-free;
`E2/CtorAdequacy.lean` is the adequacy lemma over it, byte-identical to the repo's
(only the `const`-case sorry). `E2/Check.lean` is the axiom and tracer check.
Module files, excluded from `../check.sh`; the report's §4 says how to rebuild.

## E1/ (the typed-LR spike, PASSED 2026-10-19)

`E1/E1-REPORT.md` is the report. `E1/TypedLR.lean` is `ShapeLogRel.lean:5272-6117` with
D6 applied (sorry-free, standard axioms); `E1/TypedAdequacy.lean` is
`ShapeLogRelAdequacy.lean:8-515` over it (only the `const`-case sorry). They import each other
as modules, so `../check.sh` does not cover them; the report's §7 says how to rebuild them,
and `E1/CheckLR.lean`, `E1/CheckAdequacy.lean` are the axiom and tracer checks.
