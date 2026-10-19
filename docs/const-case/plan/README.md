# Evidence files for `PLAN.md`

Scratch Lean files written by the synthesizer, the refuters and the auditors
of the plan, copied verbatim (their docstrings cite `/tmp/utt-snap6`, a build
of commit `3c35f59`, and `/tmp/utt-exp/plan/...` scratch paths). Each begins
with `import Lean4Lean.Experimental.ShapeLogRelAdequacy`; none is part of the
build; `../check.sh` typechecks them all. All are sorry-free except
`PatLeafStmt.lean`, whose two theorem bodies are deliberate sorries (it pins
statements). `PLAN.md` cites them by bare name, with the tag [T].

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
