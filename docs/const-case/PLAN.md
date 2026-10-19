# PLAN: the `const` case of `LR.adequacy` (merged implementation plan)

> **Landed in the repo 2026-10-19.** Written by an Opus synthesizer from three design notes, five
> lens analyses and their adversarial refutations, then audited for completeness and circularity;
> audit round 1 (14 amendments) is applied, see §6 at the end. Round 2 is in progress and will be
> folded in. Evidence files tagged [T] are in `plan/` (see `plan/README.md`) or in this directory;
> `/tmp/utt-snap6` in their docstrings is a build of commit `3c35f59`, which is what every line
> number here refers to. Paths into `/tmp/utt-ref/paper-artifacts/` are a local copy of the paper's
> supplementary Lean code (`domain-semantics-lean-BEE7`). Scratch files not copied here: the
> `Probe*.lean` and `Exp2_recheck.lean` probes and `Retype.lean` (no longer typechecks at HEAD).


Critic-synthesizer, 2026-10-18; amended 2026-10-19 (audit round 1, §6). Repo `/home/dan/Build/UTT`, branch `unique-typing`, HEAD `3c35f59`.
`/tmp/utt-snap6` is a built copy of HEAD (`diff -rq` of `Lean4Lean/`: identical). Line numbers are
HEAD's. Inputs: design A `DESIGN-ctor-code-shape.md`, design B
`docs/const-case/DESIGN-fuel-measure.md`, design C `docs/const-case/DESIGN-ctor-clause-from-artifact.md`,
the five lens reports and all refutations (dossier + task text).

Evidence tags: **[T]** typechecked at `/tmp/utt-snap6` (file named; sorry-free unless said),
**[R]** read at file:line, **[A]** argued, not checked in Lean.

New synthesizer files (`plan/`, all sorry-free, axioms `[propext, Classical.choice, Quot.sound]` or fewer):

| file | content |
|---|---|
| `TypedWhr.lean` | `TyDefEq_forallE_typed`, `inst_congr_beta`, `LRS.LamDefEq.whr_typed` |
| `CtorClause1a.lean` | the stage-1a clause over an abstract `IH`: `left`, `symm`, `trans`, `mono_l`, typed `whr`, `conv`, `not_sort` (trans'), `lift_aux` |
| `FieldRelLift.lean` | `FieldRel.lift_aux` alone (also inside `CtorClause1a.lean`) |
| `AxSR.lean` | `#print axioms Lean4Lean.VEnv.WHRedS.defeq` prints `sorryAx` |

Run any of them: `cd /tmp/utt-snap6 && ~/.elan/bin/lake env lean plan/<File>.lean`.

---

## 0. Verdict

1. None of A, B, C closes the const case as written; the plan is a staged hybrid whose first
   milestone (**stage 1a**) changes no definition in the shape algebra or in `LE_Interp`.
2. **All three designs miss typed reductions.** The pat leaf must convert the rule RHS's type
   `motive (c Zs)` into the goal type `motive x` (where `x ⤳* c Zs`), and at a Π result shape that
   conversion demands a typed `Γ ⊢ x ≡ c Zs : I` (`TypedWhr.lean: TyDefEq_forallE_typed` [T]).
3. The untyped `whr` field (`ShapeLogRel.lean:5297`) cannot carry any typed fact about `M`, and
   subject reduction is circular (`WHRedS.defeq`, `SExpr.lean:2665`, is a sorry; its VExpr twin
   reaches `sorryAx` through `uniqU`, `AxSR.lean` [T]); the paper builds the conversion into the
   relation for exactly this reason (`paper.txt:1317-1320`).
4. So D6 adds typed reductions to the LR; the step that looked hardest, a typed `whr` at
   `(lam, forallE)`, goes through without a `⊢ Γ` index (`LamDefEq.whr_typed`, `inst_congr_beta` [T]).
5. Stage 1a covers non-parametric, non-indexed inductives whose fields are closed inductive
   constants (Nat, Int, Bool, monomorphic lists and trees): fields are related at the canonical
   type shape `indTy` below the recorded shape (the artifact's `TmEqNat`), and `CtorClause1a.lean`
   proves the clause's non-trivial field obligations, `lift` included [T]. Its two restriction
   fields are not kernel invariants: they exclude every environment with rules for a parametric or
   indexed inductive (D3).
6. Tension (i), code placement: for stage 1b, codes go on the constructor element as `(a₁, f)`
   (clause lens + `GenericIH.lean` [T]), codes on the type are refuted (`KappaMonoR1.lean` [T]), and
   since neither placement removes `P ≡ P'`, stage 2 must carry it syntactically and semantically
   in `TyDefEq` at `indTy`.
7. Tension (ii), the measure: the local induction on `hM` is necessary but not sufficient
   (`IHVacuous.lean` [T]); the outer source is a well-founded rank induction over an env-indexed
   strong judgment (patleaf lens), with no `Block` (bare leaves have `rank ≤ rank head`) and the
   artifact's ∃-typed-upper-bound motive (`HasTypeGap.lean` [T]).
8. B's new `IsDefEqStrong.const` premises are rejected: now that `IsDefEq.strong` is proven they
   would need a rank induction inside `envStrongS` anyway (patleaf C10, upheld).
9. Tension (iii), `trans'`: a typed, level-free ambient conjunct `TyRedS Γ A (.const I ls)` makes
   `trans'` vacuous (`CtorDefEq1a.not_sort` [T]), so A's new `trans'` premise is unnecessary.
10. The rule RHS is typed in a computed pattern context (`Pattern.gen`), because existential
    witnesses are junk-satisfiable (`PatTypedDegenerate.lean` [T]).
11. A new `Pat → env` field `pat_defeq` is needed for the typed iota step; today's `natParams`
    (rule-free `envC`, rules only in `Pat`) violates it, so `extra_patV` is restated for λ-wrapped
    rules and N moves to `envA`.
12. B was right that the lemma is false with the relation unchanged (`Stuck.lean`, `Subst1.lean`)
    and right about the `hM` induction, but its assumed clause fails `mono_l`/`trans`
    (`NotDownClosed.lean`, `NaiveMono.lean` [T]) and its R1 mini-adequacy is circular (patleaf C14).
13. C's ∀-over-type-shapes clause has no `lift` ⇐ proof (`CounterC` refuted only one conjunct,
    `RealisedC.lean`, `CFull.lean` [T]; the full ⇐ is the fundamental lemma one level up [A]), its
    ∃-valuation fix rests on a wrong direction (`MonoL.lean` [T]), "no env-ordered induction is
    needed" is false, and `IndTyRed` is too weak for parameters (`CtorNoLink.lean` [T]).
14. A's `Exp2_Spine.lean` fails at HEAD, its `k : Shape n` is ill-typed (it must be `(a₁, f)`), its
    clause is over the concrete `LR`, its `rank_pat` is inconsistent for mutual recursors, and it
    calls quotients covered when they are excluded (`QuotLevel.lean` [T]).
15. STATUS.md §3 says the plan will need `WHRedS.defeq`; it does not, and this plan never uses it.
    That includes R6's λ-rule `extra` case: D5's `extra_patV` now supplies the typed open equation
    (`LamRuleTyped.lean` [T]).

Evidence files cited by bare name (all typecheck at `/tmp/utt-snap6`; the paths are below):

| file | path |
|---|---|
| `GenericIH`, `NaiveMono`, `RealisedC`, `ArityBound` | `plan/` |
| `CFull`, `Depth`, `GenericSpine`, `WeirdLR` | `plan/` |
| `KappaMonoR1`, `FieldRetypeT`, `RestrictVacuous` | `plan/` |
| `HasTypeGap`, `PatTypedDegenerate`, `Measure6` (= `Measure.lean`) | `plan/` |
| `IHVacuous` | `./` |
| `MonoL` | `plan/` |
| `CtorNoLink`, `RefuteModel` | `plan/` |
| `CounterC`, `NotDownClosed` | `plan/` |
| `QuotLevel`, `Inert` | `plan/` |
| `Reconcile`, `Mismatch` | `plan/` |
| `Schema` | `plan/` |
| `Retype` | `plan/` |
| `LamRuleTyped`, `UntypedField` | `plan/` |
| `WeakE` | `plan/` |
| `PatLeafStmt` (statements only; its 2 theorem bodies are marked sorries) | `plan/` |
| `Stuck`, `Subst1`, `CtorClause`, `Fuel` | `./` |
| `EmptyParams`, `NatParams` | `../params/` |
| artifact `LogRel.lean`, `Adequacy.lean` | `/tmp/utt-ref/paper-artifacts/domain-semantics-lean-BEE7/DomainSemantics/` |

---

## 1. Decisions

### D1. Clause shape

**Stage 1a (the milestone).** No `ShapeS` change. Definitions below are checked in
`synth/CtorClause1a.lean`, where they take the `LogRel` field behaviour as explicit hypotheses.

```lean
-- ShapeLogRel.lean, before `structure LogRelBase` (5272). Shared with D6.
def TyRedS (Γ : List SExpr) (A A' : SExpr) : Prop := (∃ w, Γ ⊢ A ≡ A' : .sort w) ∧ Γ ⊢ A ⤳* A'
def TWHRedS (Γ : List SExpr) (M M' A : SExpr) : Prop := Γ ⊢ M ≡ M' : A ∧ Γ ⊢ M ⤳* M'

/-- A field whose declared type is a closed inductive constant: related at the canonical
type shape `indTy`, at every typed element shape below the recorded one (artifact `TmEqNat`). -/
def LRS.FieldRel {Γ} : ∀ {n}, LogRel Γ n → SExpr → SExpr → SExpr → WShape n → Prop
  | 0, _, _, _, _, _ => True
  | _+1, IH, X, Y, T, p => ∀ q, q ≤ p → q.HasType .indTy → IH.DefEq X Y T q .indTy

inductive LRS.FieldsEq {Γ} {n} (IH : LogRel Γ n) :
    List SExpr → List SExpr → List SExpr → List (WShape n) → Prop
  | nil : FieldsEq IH [] [] [] []
  | cons : Γ ⊢ X ≡ Y : T → LRS.FieldRel IH X Y T p → FieldsEq IH Ts Xs Ys l →
      FieldsEq IH (T :: Ts) (X :: Xs) (Y :: Ys) (p :: l)

def LRS.CtorDefEq {Γ} {n} (IH : LogRel Γ n) (M N A : SExpr) (c : Name) (l : List (WShape n)) : Prop :=
  ∃ (I : Name) (ls : List SLevel) (ci : VConstant) (Ts Xs Ys : List SExpr),
    Params.classify c = some (.ctor l.length) ∧ Params.classify I = some (.indTy 0) ∧
    Params.env.constants c = some ci ∧ SExpr.mkInst ls ci.type = Ts.foldr .forallE (.const I ls) ∧
    TyRedS Γ A (.const I ls) ∧
    TWHRedS Γ M (spine (.const c ls) Xs) A ∧ TWHRedS Γ N (spine (.const c ls) Ys) A ∧
    LRS.FieldsEq IH Ts Xs Ys l
```
Wiring into `LRS.DefEq` (5619), replacing `| .indTy => True` (5633). This part is [A] (to be checked in E2):
```lean
  | .indTy => match hm : m.1 with
    | .bot => True
    | .ctor c l => LRS.CtorDefEq IH M N A c (l.pmap Subtype.mk (hm ▸ m.2).1)
    | _ => False
```
Why each piece:
- `classify c = .ctor l.length` is stored. Without it `whr` fails at symb-named shapes
  (`GenericIH.lean: whr_fails_symb` [T]), and `trans` uses `WHRedS.ctorSpine_determ` (SExpr.lean:2716).
- `mkInst ls ci.type = Ts.foldr .forallE (.const I ls)` pins the telescope.
  `foldr_forallE_const_inj` [T] gives `Ts = Ts'` in `trans`. That is the residual `sorry` in
  `docs/const-case/CtorClause.lean:92`, now closed.
- `TyRedS Γ A (.const I ls)` is the typed ambient. It kills `trans'` (`not_sort` [T]) and makes `conv` produce
  typed `A ≡ B` from `TyDefEq` alone, so the `conv` signature does not change (`CtorDefEq1a.conv` [T]).
- `TWHRedS Γ M (spine …) A` is the typed reduction that the pat leaf needs (§0.2). It needs the typed
  `whr` of D6 (`CtorDefEq1a.whr` [T]).
- `FieldRel` uses the `∀ q ≤ p` form. `mono_l` then needs no field typing, so `Shape.hasType (.ctor _ _) .indTy = true`
  (2494) stays (`CtorDefEq1a.mono_l` [T]). The `lift` ⇐ direction instantiates at `p` itself, which is a
  ctor shape and therefore typed (`FieldRel.lift_aux` [T]). Fields are related at `indTy` only:
  in stage 1a every field type is a closed inductive constant, whose type shapes are `⊥`/`indTy`
  (`Const.indTy` leaf, `ShapeLogRel.lean:3329`); only `⊥` if it is Prop-valued (`UntypedField.lean: indTy_not_prop` [T]).
- Cost of keeping 2494: a ctor shape's field shapes can be untyped (`ctor c [sort]` is typed at `indTy`),
  `Matches.var` binds them to iota pattern variables (3310), and `FieldRel` is vacuous there
  (`UntypedField.lean: ctor_sortField_typed`, `matches_binds_untyped`, `fieldRel_sort_trivial` [T]).
  So the pat leaf lowers field entries (D4 step 1, item E6a).
- Typed field equalities `Γ ⊢ X ≡ Y : T` are kept for every field. `Adequate.cons` needs `hx`
  (`ShapeLogRelAdequacy.lean:45-50`).

The 19 `LogRel` fields at the new case:
- `left`, `symm`, `trans`, `mono_l`, `whr`, `conv`, `trans'`, and the new case of `LR.lift_succ_aux` (6011): [T] in `CtorClause1a.lean`.
- `mono_r_2`, `mono_r_1`, `mono_r_2_ty`: `indTy` is a single point (`WShape.le_indTy` 1274, `indTy_le` 1277) [R].
- `join_ty`: `indTy ⊔ indTy = indTy`, trivial.
- `bot`: `(⊥, indTy)` stays True.
- `sort_iff` and `toType`: untouched.

The simp lemmas `LRS.DefEq.indTy_a` / `TyDefEq.indTy_m` (5661-5662) become false. Re-prove their
5 uses (5746, 5763, 5801, 5823, 5846). The `(⊥, indTy) = trivial` site in `lamDF` (ShapeLogRelAdequacy ~305) survives.

**Stage 1b (after the milestone).** Arbitrary closed field types need finite codes, because a
∀-over-type-shapes clause is not lift-safe (§0.13).
- `ShapeS.ctor : Name → List Shape → Shape → List (Shape × Shape) → ShapeS Shape` stores the Π-code of
  the constructor's type as `(a₁, f)`, the same data as `forallE` (clause lens C10, upheld).
- The clause is `GenericIH.lean`'s `SpineDefEq2` (two-type, abstract `IH`; `left`/`symm`/`trans`/`mono`/`lift_aux` [T]) with two changes:
  - the typed conjuncts `Γ ⊢ A₁ ≡ A₁'`, `Γ ⊢ x ≡ y` are taken for every field,
    the semantic ones only while the code is `forallE`;
  - a `⊥` code types only `⊥` fields. This bounds arity per level without making shapes untypable
    (`ArityBound.lean`, `Depth.lean` [T] show the unrelaxed `SpineTyped` fails at level 1).
- Code validity `LE_Interp .nil (forallE a₁ f).T (mkInst ls ci.type)` is stored in the clause, so the consumer
  does not depend on `Matches.app`'s code.
- κ is rejected (§0.6).

### D2. `TyDefEq` at `indTy`

Stage 1a, replacing the `True` at `LRS.TyDefEq` (5439):
```lean
  | ⟨.indTy, _⟩ => ∃ (I : Name) (ls : List SLevel), Params.classify I = some (.indTy 0) ∧
      TyRedS Γ M (.const I ls) ∧ TyRedS Γ N (.const I ls)
```
`⟨.ctor _ _, _⟩` stays `True`.
- Same head `I` and same `ls` are required: `conv` needs them, through determinism of the whnf
  (`WHNF.indTySpine`, SExpr.lean:2615).
- `left`/`symm`/`trans` are by determinism. `whr_ty` uses typed `TyRedS` composition (D6). `join_ty`
  and `mono_r_2_ty` are trivial. It is level-free, so `lift` holds.
- Producers: the `Const.indTy` leaf (`M = const I ls`, refl, typed by `IsDefEq.const`), and `whr`
  at the beta/extra cases.

Stage 2 (open): an `I`-spine with argumentwise typed `SynArgs`, plus semantic argument
relatedness at shapes stored on the type (`indTy qs`). See D3.

### D3. Parametric-field reconciliation

**Stage 1a: a restriction.** These Params fields are removed in stage 2:
```lean
  indTy_closed : classify I = some (.indTy k) → env.constants I = some ci → k = 0 ∧ ∃ u, ci.type = .sort u
  ctor_fields_closed : (cl matches .ctor .. | .etaCtor ..) → classify c = some cl → env.constants c = some ci →
    ∃ (I : Name) (Ts : List VExpr), ci.type = Ts.foldr .forallE (.const I (VLevel.params ci.uvars)) ∧
      ∀ T ∈ Ts, ∃ I' us, T = .const I' us ∧ classify I' = some (.indTy 0)
```
- Covered: Nat, Int (`ofNat`/`negSucc`), Bool, monomorphic unit/enum types, monomorphic lists and trees of these.
- Excluded: List, Option, Prod, Sigma, Fin, Vector, function-typed fields.
- These two fields are not kernel invariants; they restrict the whole environment. `extra_patV` puts
  every env rule in `Pat`, and `pat_wf` (SExpr.lean:18-21) makes its argument heads `.ctor`. So an
  environment with an iota rule for a parametric or indexed inductive in Type (`List.rec`, `Prod.rec`)
  violates `ctor_fields_closed`, and via `ctor_syn` (`classify I = .indTy args.length`) `indTy_closed`.
  Stage-1a `Params` is satisfiable only by environments with no such inductive (not Lean's prelude).
  Both fields go in stage 2.
- `indTy_closed` allows `u = 0`. Prop-valued field types get type shape `⊥` in D4 step 1; no extra field.
- Both fields are vacuous for `emptyParams`. For N: `Nat : Sort 1`; `zero : Nat` (`Ts = []`);
  `succ : Nat → Nat` (`Ts = [.const Nat []]`).
- No reconciliation is needed: the recursor and the constructor share the closed telescope. The
  consumer uses `Adequate.cons` on lowered field entries (D4 step 1), not on the raw `l_i`.

**Stage 2 (open; route only).** These are the refuters' requirements, all upheld:
- `TyDefEq` at `indTy` must carry syntactic `SynArgs` (typed argument equalities; trans/symm need
  `IsDefEq.subst` with `⊢ Γ`, or the `inst_congr_beta` trick [T] per argument). It must also carry
  semantic relatedness of the parameters at shapes stored in the type shape (`indTy qs`, hybrid, unverified).
  The constructor clause's nil conjunct must be stated at the element's own parameter shapes.
- A field of parameter type `P` uses `LR.field_retype_T` with `LR.Subst1.tyValid_below_T`
  (`FieldRetypeT.lean` [T]; TShape-bounded, because the recursor's entry `q` sits one level above the fields).
- Compound field types are converted along the PiDefEq of the constructor's own type (adequacy via
  the WF IH) at related parameters [A].
- `LR.Adequate.mono_r` (ShapeLogRelAdequacy.lean:105-146) is the same-term retype; it does not
  solve the cross-valuation case by itself (model refuter X4/X5).
- Rule `Check`s become `(rec-param ≡ ctor-param)` and are discharged from `SynArgs`. `pat_check` is
  dropped, because with linear patterns `pat_check` plus a typed RHS is unsatisfiable for parametric
  rules (model refuter, upheld).

### D4. Measure and RHS typing

Measure, lexicographic: (1) WF on a rank bound `k`; (2) structural on `H : IsDefEqStrong (env.below rank k) …`,
which covers the 13 existing cases; (3) in the const case only, structural on `hM`; (4) structural on
`Const` and `RHS`.
- symm/trans/trans' feed fresh `hM'` from `soundS` only into level (2), on sub-derivations
  (patleaf C4, upheld; `ShapeLogRelAdequacy.lean:163-179`).
- `const_local`'s only recursive calls are `ih7` on `a7 m e hR`, a strict sub-derivation, and the WF IH at `rank c₀ < k`.

**`IsDefEqStrong` signature.** It gains a first explicit parameter `(E : VEnv)`. `const` uses
`E.constants` and `extra` uses `E.defeqs`. Constructor arities and premises are unchanged, so
**`IsDefEqStrong.const` gets no new premise**. `⊢ₛ` becomes notation for `IsDefEqStrong Params.env`.
```lean
theorem IsDefEqStrong.mono (h : E ≤ E') : IsDefEqStrong E Γ e1 e2 A → IsDefEqStrong E' Γ e1 e2 A
def VEnv.below (env : VEnv) (rank : Name → Nat) (k : Nat) : VEnv            -- Measure6.lean:44
theorem IsDefEqStrong.exists_below (rank : Name → Nat) :
    Γ ⊢ₛ e1 ≡ e2 : A → ∃ k, IsDefEqStrong (Params.env.below rank k) Γ e1 e2 A  -- Measure6.lean:204 [T]
theorem _root_.Lean4Lean.VEnv.IsDefEqStrong.mkSE (hE : E ≤ Params.env) (hctor : CtorProviderE E)
    (H : E.IsDefEqStrong Params.univs Γ e₁ e₂ A) (hΓ : OnCtx Γ (fun _ A => A.LevelWF Params.univs)) :
    IsDefEqStrong E (Γ.map mk) (mk e₁) (mk e₂) (mk A)
```
Re-proof cost:
- `IsDefEq.strongS` (SExpr.lean:1767) and `Params.envStrongS` (1946) are unchanged (`E := Params.env`).
- `mkS` (1818) is generalised to `mkSE`. `CtorProvider` (1805) is restated over `E`, with
  `CtorProvider.synE` using `ctor_syn`/`ctor_sort` through `E ≤ env` and `HasType.mono`
  (Theory/Typing/Lemmas.lean:402). About 60 lines. The refuter is right that this is not 5 lines.
- 14 statement sites spell `IsDefEqStrong Γ …` and need `Params.env` inserted: 11 in SExpr (1044-1046, 1081,
  1334-1335, 1465, 1821, 1827, 1833, 1949), 2 in ShapeLogRel (5055, 5264), 1 in ShapeLogRelAdequacy (48).
  UniqueTyping.lean:141 inducts on it; `E` is a parameter, so it should compile, but it must be rebuilt.
- `closedN` (1367), `weak'` (1387) and `weak0` (1426) are restated for any `E` with `hE : E ≤ Params.env`.
  Their const/extra cases use `constType_closed h1`/`defeq_closed h1` (1396, 1419), transported by
  `hE.1`/`hE.2` (`WeakE.lean: IsDefEqStrongE.closedN'`, `weak'`, `weak0'` [T]).

**New Params fields** (VExpr level; `VEnv.below` and `Pattern.gen` are defined before `class Params`):
```lean
  rank : Name → Nat
  rank_ordered : ∀ k, (env.below rank k).Ordered
  type_below : env.constants c = some ci → (env.below rank (rank c)).IsType ci.uvars [] ci.type
  pat_rank : Pat p r → .const c' us ∈ r.1.fixedLeaves → rank c' ≤ rank p.head
  pat_gen : Pat p r → (Pattern.gen env rank classify p r.1).isSome
  pat_typed : Pat p r → Pattern.gen env rank classify p r.1 = some g → env.constants p.head = some ci →
    OnCtx (g.self ++ g.ctx) (fun Γ A => (env.below rank (rank p.head)).IsType ci.uvars Γ A) ∧
    (env.below rank (rank p.head)).HasType ci.uvars (g.self ++ g.ctx) g.rhsAbs (g.type.liftN g.self.length)
  pat_defeq : Pat p r → Pattern.gen env rank classify p r.1 = some g → env.constants p.head = some ci →
    env.IsDefEq ci.uvars g.ctx g.lhs g.rhs g.type
  pat_check : Pat p r → r.2 = .true                                 -- stage 1a only
```
- `Pattern.RHS.fixedLeaves` is at Measure6.lean:69.
- Unlike D3's two restriction fields, these are kernel invariants [A]: `rank` is declaration order
  (I < ctors < rec; mutual recursors share a rank); recursor rules are generated as well-typed open
  equations over syntactic telescopes (`pat_gen`, `pat_typed`, `pat_defeq`); non-K iota rules have no
  side conditions (`pat_check`). All are vacuous for `emptyParams`.
- `Pattern.gen` (item R5) is a *function*: it strips syntactic Π-telescopes off the head's and the
  constructor's types (`VExpr.piTelescope k`). Its result:
  ```lean
  structure PatGen where
    ctx : List VExpr     -- innermost first: ctor field types, then the head's first m binder types
    self : List VExpr    -- one closed type per bare-leaf occurrence with rank = rank head
    lhs rhs rhsAbs type : VExpr
  ```
  For iota `app (varN (const rec) m) (varN (const c) n)` (Pattern.lean:239):
  - path `inl (some^i none)` ↦ `bvar (n+i)` and `inr (some^i none)` ↦ `bvar i` (`Matches.var` binds the last argument);
  - `lhs := (spine (const rec params) recVars).app (spine (const c us) fieldVars)`, where `us` is read
    off the recursor's major domain `const I us`;
  - `type` := the recursor's body with the major instantiated by that ctor spine;
  - `rhsAbs` maps each same-rank bare leaf occurrence (by RHS position, not by `VExpr`) to its own
    `self` variable. This is the patleaf code refuter's fix for `node l r`.
  
  For delta `.const c` the result is `ctx = []`, `lhs = const c params`, `type = ci.type`.
  Being a function, it leaves no junk witnesses (`PatTypedDegenerate.lean` [T]).

Measure statements:
```lean
theorem LR.adequacy_rank (k : Nat) : ∀ {Γ M N A}, IsDefEqStrong (Params.env.below Params.rank k) Γ M N A →
    ∀ {ρ n} {m a : WShape n}, LE_Interp ρ m.T M → LE_Interp ρ a.T A → m.HasType a →
    LR.Adequate Γ₀ Γ ρ M N A m a        -- Nat.strong_induction_on k, then induction H
-- LR.adequacy (148) is recovered from `(H.strong hΓ).exists_below Params.rank`.

theorem LR.const_local {k c₀}
    (WFIH : ∀ k' < k, ∀ {Γ M N A}, IsDefEqStrong (Params.env.below Params.rank k') Γ M N A →
      ∀ {ρ n} {m a : WShape n}, LE_Interp ρ m.T M → LE_Interp ρ a.T A → m.HasType a →
      LR.Adequate Γ₀ Γ ρ M N A m a)
    (hΓ₀ : ⊢ Γ₀) (hc₀ : Params.rank c₀ < k) :
    ∀ {ρ mT M} (hM : LE_Interp ρ mT M) {c ls ci}, M = .const c ls → Params.rank c ≤ Params.rank c₀ →
      Params.env.constants c = some ci → ls.length = ci.uvars →
      (∃ n, mT = (WShape.bot (n := n)).T) ∨
      ∃ (n : Nat) (m' a' : WShape n), mT ≤ m'.T ∧ m'.HasType a' ∧ LE_Interp ρ a'.T (mkInst ls ci.type) ∧
        ∀ {n'} (m a : WShape n'), m.T ≤ m'.T → LE_Interp ρ a.T (mkInst ls ci.type) → m.HasType a →
          (LR Γ₀).DefEq (.const c ls) (.const c ls) (mkInst ls ci.type) m a
```
- The ∃-typed-upper-bound form is what `SubstWF.cons` can push for a self occurrence
  (`HasTypeGap.lean: typed_above_not_below`, `LE_Interp.const_typed_ub` [T]).
- `rank ≤` replaces `Block`: mutual recursors share a rank. This generalises the refuter's ties.
- Type validity of a nested `c'` comes from `type_below` plus the WF IH at `rank c' < k`.
- The spine lemma (item R9) is `LR.const_spine` (`PatLeafStmt.lean` [T as a statement]). It amends C's
  `adequacy_const_spine` (`docs/const-case/CtorClause.lean:109-124`): it holds at every `ρ` with
  `(Valuation.ofRargs rargs).LE ρ` that a `SubstWF` covers, not at `ofRargs rargs` itself.
  - Why: `Const.lam` ranges over the pairs of an arbitrary graph `f` (ShapeLogRel.lean:3325-3326),
    `LE_Interp.lam` only over typed inputs (3339-3342). At an untyped `x` no `SubstWF` exists at
    `ofRargs (x :: rargs)`, so C's IH says nothing, yet the consumer needs the typed `p ≥ x` from `LamDefEq`.
  - Lam case: use `ρ.push p` and move the `Const`/`R` data up with `LE_Interp.mono_l` (3407). `lamDF`'s
    template (ShapeLogRelAdequacy.lean:284-357) does not carry over verbatim.
  - `ihR` becomes `LR.LocalIH` (same-rank bare-constant leaves) plus `LR.WFIH`. The lemma carries the
    semantic type validity `tyV` at every `SubstWF` over `ρ`, layer by layer from `PiDefEq`.

**`pat_leaf_1a`, the E6 interface** (R9 calls it at `Const.pat`; R10 proves it). `PatLeafStmt.lean`
[T as a statement]; stand-ins there: the repo's `LR` for `T.LR`, a variable `rank` for `Params.rank`,
`IsDefEqStrongE` for R4's `IsDefEqStrong E`, `PatGen` and the `pat_typed`/`pat_defeq` conclusions as hypotheses.
```lean
def LR.WFIH (Γ₀ : List SExpr) (k : Nat) : Prop :=
  ∀ k' < k, ∀ {Γ M N A}, IsDefEqStrongE (Params.env.below rank k') Γ M N A →
    ∀ {ρ n} {m a : WShape n}, LE_Interp ρ m.T M → LE_Interp ρ a.T A → m.HasType a →
      LR.Adequate Γ₀ Γ ρ M N A m a
-- LR.ConstGoal Γ₀ ρ mT c ls ci := const_local's conclusion above (⊥, or the ∃-typed-upper-bound form)
def LR.LocalIH (Γ₀ : List SExpr) (ρ₀ : Valuation) (c : Name) (R : TShape → SExpr → Prop) : Prop :=
  ∀ m e, R m e → ∀ c' ls' ci', e = .const c' ls' → rank c' = rank c →
    Params.env.constants c' = some ci' → ls'.length = ci'.uvars → LR.ConstGoal Γ₀ ρ₀ m c' ls' ci'

theorem LR.pat_leaf_1a (WFIH : LR.WFIH rank Γ₀ k) (hc : rank c < k)
    (h1 : Params.env.constants c = some ci) (h2 : ls.length = ci.uvars) (LIH : LR.LocalIH rank Γ₀ ρ₀ c R)
    (hP : Params.Pat p r) (hMt : LE_Interp.Matches p c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1) (hchk : r.2 = .true)
    (g : PatGen)                                   -- `Pattern.gen … p r.1 = some g`
    (hty : OnCtx (g.self ++ g.ctx) (fun Γ A => (Params.env.below rank (rank c)).IsType ci.uvars Γ A) ∧
      (Params.env.below rank (rank c)).HasType ci.uvars (g.self ++ g.ctx) g.rhsAbs (g.type.liftN g.self.length))
    (hdef : Params.env.IsDefEq ci.uvars g.ctx g.lhs g.rhs g.type)
    (hT : mkInst ls ci.type = Ts.foldr .forallE B) (hk : rargs.length = Ts.length)
    (hρ : (Valuation.ofRargs rargs).LE ρ) (W : LR.SubstWF Γ₀ σ σ' (Ts.reverse ++ Γ₀) ρ)
    {m a : WShape n'} (le : m.T ≤ mC) (hA : LE_Interp ρ a.T B) (hmem : m.HasType a)
    (tyV : ∀ {τ τ'}, LR.SubstWF Γ₀ τ τ' (Ts.reverse ++ Γ₀) ρ → (LR Γ₀).TyDefEq (B.subst τ) (B.subst τ') a) :
    (LR Γ₀).DefEq ((openSpine c ls Ts.length).subst σ) ((openSpine c ls Ts.length).subst σ')
      (B.subst σ) m a
```
- The ctor clause and the typed `x ≡ c' Zs` are read off `W`'s major entry (`Subst1` at `ctor' c' rargs'.reverse`, `indTy`).
- `tyV` at every `SubstWF` also covers `σ` with the major replaced by `c' Zs` (step 6).
- `LR.const_spine` has the same hypotheses with `hC : LE_Interp.Const c ls R rargs mC` in place of `hP … hdef`.
- The R5 stage-1a fields (`indTy_closed`, `ctor_fields_closed`, `type_below`, `rank_ordered`) enter E6 as section hypotheses.

RHS step, R2 (patleaf C13 with its fixes):
1. Build `W_p : SubstWF Γ₀ σ_p σ_p' (g.self ++ g.ctx ++ Γ₀) ρ_low` by `Adequate.cons`, starting from
   `SubstWF.id hΓ₀` (ShapeLogRel.lean:6074). `SubstWF.cons` needs each pushed shape typed (`x.HasType a`),
   and a raw field shape may be untyped (D1), so field entries are lowered (E6a, option (a)). Sources:
   - recursor-argument entries from the spine lemma's SubstWF (typed `p`s);
   - field entries: `l_i` if it is `⊥` or a ctor shape, else `⊥`; `⊥` for Prop-valued field types.
     `hv` is `FieldRel` at the lowered shape; `hA₁` is the `Const.indTy` leaf (`⊥` for Prop);
   - self entries from `LR.LocalIH`;
   - each entry's `ihA` from the WF IH on `pat_typed`'s context typings.
2. `hM_rhs : LE_Interp ρ_low y' g.rhsAbs`, for the typed goal shape `y'` below the RHS shape, is E6a's
   lowering lemma, by induction on `LE_Interp.RHS` (ShapeLogRel.lean:3316). Every function position has a
   typed upper bound with `HasDom` (fixed leaves via `LE_Interp.const`'s `m'.HasType`, recursor arguments via
   the typed `p`, minor-premise variables via typed entries), so untyped arguments collapse to their typed parts [A].
   - Not from the raw `m''`: `RHS.var` (3319) needs `ρ ≥ m''`, which conflicts with typed entries.
   - The type shape for `g.type` comes from `soundS` at `ρ_low` (which `Fits`), not from the raw codomain shape.
   - Fallback (b): type ctor fields in `Shape.hasType`, as the artifact does (`succ v : nat` needs `v : nat`,
     artifact Shape.lean:3121-3125). It changes the shape algebra; re-check `mono_l`, `lift`, `join`.
3. Adequacy of `rhsAbs` comes from the WF IH at `rank head` on `pat_typed`, via `rank_ordered` +
   `VEnv.IsDefEq.strong` + `instL` + `mkSE`. This is the `EnvStrongR.of_params` pattern (Measure6.lean:298 [T, given MkSE]).
   The derivation lives in the closed context `g.self ++ g.ctx`; weaken it to `… ++ Γ₀` at `E = env.below …`.
   `IsDefEqStrong.weak0` (SExpr.lean:1426) only handles `[]`. The general case is a new ~20-line lemma
   via R4's E-version of `IsDefEqStrong.weak'` (`WeakE.lean: IsDefEqStrongE.weak'` [T]) with a `Ctx.Lift'`
   that skips the tail.
4. Rewrite with `toVExpr_subst` (Measure6.lean:467 [T]).
5. Typed `whr`: `rec Xs x ≡ rec Xs (c Zs)` by `appDF` with the clause's typed `x ≡ c Zs : I`;
   then `rec Xs (c Zs) ≡ rhs` by `pat_defeq` + `IsDefEq.subst` (SExpr.lean:2038, `⊢ Γ₀` from `W.wf₀`).
   Untyped: `pat_leaf_reduce` (Measure6.lean:452 [T]).
6. `conv` from `motive (c Zs)` to `motive x` by `PiDefEq.1` of the recursor's type at `(c Zs, x)`,
   which needs that typed equation.

### D5. Exclusions, `extra_patV`, `pat_defeq`; instances

**`extra_patV`, restated for λ-wrapped rules** (Lean4Lean's `vdefeq` convention, Theory/Meta.lean:97-98):
```lean
  extra_patV {df : VDefEq} {ls : List VLevel} {Γ : List VExpr} :
    env.defeqs df → (∀ l ∈ ls, l.WF univs) → ls.length = df.uvars →
    ∃ (Δ : List VExpr) (L R T : VExpr),
      df.lhs.instL ls = Δ.foldr .lam L ∧ df.rhs.instL ls = Δ.foldr .lam R ∧
      df.type.instL ls = Δ.foldr .forallE T ∧
      OnCtx Δ.reverse (env.IsType univs) ∧ env.IsDefEq univs Δ.reverse L R T ∧
      ∃ p r m1 m2, Pat p r ∧ p.Matches L m1 m2 ∧
        r.2.OK (env.IsDefEqU univs (Δ.reverse ++ Γ)) m1 m2 ∧ R = r.1.apply m1 m2
```
- Why the typed open equation: under D6 the λ-rule `extra` case needs typed beta steps
  `(λΔ.L)a⃗ ≡ L[a⃗]`, `(λΔ.R)a⃗ ≡ R[a⃗]` at `T[a⃗]`. `IsDefEq.beta` needs the body typed at the codomain
  (SExpr.lean:894). The only λ-inversion, `VEnv.HasType.lam_inv` (Theory/Typing/Strong.lean:784), types the
  body at some type; matching that to `T` is `forallE_inv` (ShapeLogRelAdequacy.lean:492), built on
  `LR.adequacy`, so circular. The other route, `WHRedS.defeq`, is a sorry. With the open equation the
  steps are sorry-free (`LamRuleTyped.lean: typed_beta_rule`, `typed_beta_rhs` [T]).
- Kernel invariant [A]: a recursor rule is the λ-closure, over its binder telescope, of a well-typed open equation.
- With `Δ = []` this is today's field plus `env.IsDefEq univs [] L R T`, which is the `extra` rule itself
  (Theory/Typing/Basic.lean:54), so delta rules and `emptyParams` are unaffected.
- It is satisfiable by `envA`, whose λ-wrapped iota rules match after stripping 3 binders (zero rule) and
  4 (succ rule) (NatParams.lean:117-127; `iotaZeroOpen_matches` [R]). The open equations come from direct
  typing of the open bodies, as for `pat_defeq`, with no inversion [A].
- Consumers to re-prove for `Δ ≠ []`:
  - `Params.extra_pat` (SExpr.lean:1006);
  - the `extra` case of `LE_Interp.strongSoundS` (ShapeLogRel.lean:5229-5260), through the `LE_Interp.lam`
    layers, then the current proof on the open body;
  - the `extra` case of `LR.adequacy` (ShapeLogRelAdequacy.lean:466-474), through `LamDefEq` (beta, then
    `WHRed.extra` on the open instance, then the RHS IH), each beta layer typed by `typed_beta_rule` from
    the open equation. This runs on the typed LR (E5 on E1).
- `Params.no_lam_rule` (Schema.lean [T]) becomes false by design.

**`pat_defeq` (Pat → env)** is required by step 5 of D4's RHS route. `extra_patV` is the converse
direction (env → Pat). The current `natParams` has `env := envC` (rule-free, NatParams.lean:287-288)
and `Pat` = the two iota rules, so `pat_defeq` fails for it [A: non-derivability of
`Nat.rec m z s Nat.zero ≡ z` in `envC` is argued]. That instance is incoherent:
`WHRed` (via `Pat`) reduces what `IsDefEq` cannot equate.

Satisfiability of every new field:

| field | `emptyParams` | N over `envA` |
|---|---|---|
| `rank` | `0` | Nat 0, zero 1, succ 2, rec 3 |
| `rank_ordered` | `∅.below = ∅` (extensional) | prefixes env1/env2/env3/envA (NatParams.lean:156-162); `envA_ordered` carries the two routine sorries already there |
| `type_below` | vacuous | rec's type mentions Nat/zero/succ only |
| `pat_rank` | vacuous | the succ rule's leaf `const Nat.rec [.param 0]` has rank 3 ≤ 3 |
| `pat_gen`/`pat_typed` | vacuous | `[self : rec.type, n, s, z, motive] ⊢ s n (self motive z s n) : motive (succ n)` in `env3` |
| `pat_defeq` | vacuous | `appDF`×4 + beta on `iotaSuccLam`/`iotaZeroLam` [A, routine] |
| `pat_check` | vacuous | both rules are `.true` (NatParams.lean:91-92) |
| `indTy_closed`, `ctor_fields_closed` | vacuous | see D3 |
| `extra_patV` (λ) | vacuous | strip 3 binders (zero rule), 4 (succ rule); open equations as for `pat_defeq` [A] |

`ctor_sort_nat` stays blocked on `IsDefEqU.sort_inv` (unchanged). Exclusions are listed in §5.

### D6 (new). Typed reductions

Changes to `ShapeLogRel.lean`. Proposed, to be checked by E1:
```lean
def AmbSort (Γ : List SExpr) (A : SExpr) : Prop := ∃ v w, Γ ⊢ A ≡ .sort v : .sort w
-- LogRel fields (5278-5298):
  sort_iff : DefEq M N A (.sort r) (.sort r') ↔ AmbSort Γ A ∧ ∃ u, TyRedS Γ M (.sort u) ∧ TyRedS Γ N (.sort u)
  sort_iff_ty : TyDefEq M N (.sort r) ↔ ∃ u, TyRedS Γ M (.sort u) ∧ TyRedS Γ N (.sort u)
  whr : TWHRedS Γ M M' A → TWHRedS Γ N N' A → (DefEq M N A m a ↔ DefEq M' N' A m a)
  whr_ty : TyRedS Γ A A' → TyRedS Γ B B' → (TyDefEq A B m ↔ TyDefEq A' B' m)
  -- bot, conv, symm, trans, trans', mono_*, join_ty, toType: signatures unchanged
-- LRS.ValTyPi2 (5395): `Γ ⊢ Mᵢ ⤳* .forallE Bᵢ Fᵢ`  ↦  `TyRedS Γ Mᵢ (.forallE Bᵢ Fᵢ)`
-- LRS.TyDefEq (5438) at sort: `∃ u, TyRedS Γ M (.sort u) ∧ TyRedS Γ N (.sort u)`
-- LRS.DefEq (5619):
  | .sort _ => match m.1 with | .bot => True | _ => AmbSort Γ A ∧ LRS.TyDefEq IH M N m
  | .forallE a₁ a₂ => … | .lam mg => ∃ A₁ A₂ u v, TyRedS Γ A (.forallE A₁ A₂) ∧ …   -- rest unchanged
-- LR0 (5305-5375): the same at level 0
```
Why each change:
- `whr` is typed at the ambient, which the clause needs. Every caller has the typed step from its
  derivation: the beta steps inside `lamDF` (ShapeLogRelAdequacy.lean:346, 353, 356, typed via `IsDefEq.beta` on the substituted premises), `beta` (436), `eta` (456), `extra` (474; for `Δ ≠ []` the typed beta layers come from D5's open equation), and the pat leaf (step 5 above).
- At `(lam, forallE)`, `whr` needs typed `A ≡ Π A₁ A₂`, hence `TyRedS` in that clause.
  `LamDefEq.whr_typed` [T] then builds the typed app congruences without `⊢ Γ`; the `N b` side
  uses `appDF` with the pair `(a, b)`.
- `conv`'s codomain conversions get typed `F.inst a ≡ F'.inst a` by `inst_congr_beta` [T], with no WF index.
- The typed ambient at `(m ≠ ⊥, sort)` lets `whr` turn `M ≡ M' : A` into `: sort v` for `whr_ty`.
  `(⊥, sort)` stays `True`, so the `bot` field and its 15 callers in ShapeLogRelAdequacy.lean are unchanged. That choice is
  the main bet; E1 tests it.
- Who produces the new ambient conjuncts [A]:
  - the `sort`/`forallEDF`/`lamDF` cases, whose types are syntactic;
  - `conv`, from the `TyRedS` inside `TyDefEq`;
  - the const case's lam rows and the pat-leaf output, from the type's own `TyDefEq`
    (`tyV`, or the recursor type's `PiDefEq` at `(x, x)`);
  - `mono_*`, `lift`, `left`/`symm`/`trans`, which only copy the conjunct.
- **Fallback if E1 fails:** the artifact's full design. `bot : a.HasType .type → TyDefEq A A a → DefEq M N A .bot a`,
  `AmbSort` at every `m`, and an `isType` field (LogRel.lean:63-84).

---

## 2. Ordered work items

"Scratch" means the item can be done independently against `/tmp/utt-snap6`, in parallel.
"Build" means `lake build Lean4Lean.Experimental` is green. "Tracer" means `lake env lean scripts/TraceSorry.lean`.

| id | file / definitions | statement or content | lines | deps | verify | risk | scratch |
|---|---|---|---|---|---|---|---|
| **E1** | `synth/TypedLR.lean` (copy of ShapeLogRel.lean:5272-6117 and ShapeLogRelAdequacy.lean:8-146 in a scratch namespace `T`) | D6 exactly as in §1; re-prove `LR0`, the `LRS` instance (19 fields), `LR.lift_succ_aux`, `LR.DefEq.lift`, `LR.TyDefEq.lift`; re-check `LR.Subst1`/`SubstWF`, `Adequate`, `Adequate.cons`, `toValTy`, `Adequate.mono_r` (transcription: their LR-field uses keep their signatures) | ~1 150 (mostly copied), ~200 changed | – | `#print axioms` of `T.LR0`, `T.LRS`, `T.LR.DefEq.lift`, `T.LR.TyDefEq.lift`, `T.LR.SubstWF.symm`, `T.LR.Adequate.cons`, `T.LR.Adequate.mono_r`: no `sorryAx` | med | yes, **first** |
| E2 | same file | wire D1/D2 into E1's `LRS.DefEq`/`TyDefEq` using `CtorClause1a.lean`; re-prove the fields at the new cases | ~200 | E1 | E1's axiom list again: no `sorryAx` | low | yes |
| E3 | `synth/Measure7.lean` (port of `Measure.lean`) | drop `Block`; `rank ≤` motive; ∃-typed-upper-bound motive; `Pattern.gen` with per-occurrence self; `const_local` up to the spine-lemma sorry | ~450 | – | only the marked spine/13-case sorries | med | yes |
| E4 | `synth/NatParamsA.lean` | N over `envA`: λ-`extra_patV` with the open typed equations (strip 3 binders for the zero rule, 4 for succ), `rank`, `pat_gen`/`pat_typed`/`pat_defeq` for both rules (`Pattern.gen` checked by `rfl` at those counts) | ~300 | E3 (`Pattern.gen` draft) | `#print axioms` of the instance: `sorryAx` only via `ctor_sort_nat`, `iotaSuccLam_wf`, `iotaZeroLam_wf` | low-med | yes |
| E5 | `synth/LamRules.lean` (on E1) | `extra` cases of `strongSoundS` and `LR.adequacy` for `Δ.foldr .lam` rules; the adequacy part on E1's typed `T.LR`, each beta layer by `typed_beta_rule` from D5's open equation | ~250 | E1 | `#print axioms` of `T.strongSoundS_extra_lam`, `T.adequacy_extra_lam`: no `sorryAx` | med | yes |
| E6a | `synth/FieldLower.lean` (on E1+E2) | field-entry typing for the pat leaf (D4 steps 1-2). Default (a): lowered valuation `ρ_low` and the lowering lemma `T.LR.rhs_lower` (`LE_Interp ρ_low y' g.rhsAbs` for typed `y'` below the RHS shape, by induction on `LE_Interp.RHS`). Fallback (b): typed ctor fields in `Shape.hasType`, then re-check `mono_l`/`lift`/`join` | ~200 | E1, E2, E3 | `#print axioms T.LR.rhs_lower`: no `sorryAx` | high | yes |
| E6 | `synth/PatLeaf1a.lean` (on E1+E2) | `T.LR.pat_leaf_1a`, statement as in D4 (`PatLeafStmt.lean`): prove the pat-leaf goal (D4 steps 1-6) | ~350 | E1, E2, E3, E6a | `#print axioms T.LR.pat_leaf_1a`: no `sorryAx` | **high** | yes |
| R1 | ShapeLogRel.lean 5272-6066 | D6 from E1; lands with R2 as one green commit | ~200 changed | E1 | `lake build Lean4Lean.Experimental.ShapeLogRel` (ShapeLogRelAdequacy stays red until R2) | med | no |
| R2 | ShapeLogRelAdequacy.lean (13 cases, `forallE_whRed_l`/`forallE_inv`/`sort_inv` 476-515), UniqueTyping.lean | typed `whr` callers (346, 353, 356, 436, 456, 474); `sort_iff` (183, 514); `WHNF.*.whRedS` on what is now `TyRedS` (274, 488, 495, 498, 515); `.rfl` ambient producers (327, 383, 396, 411); `whr_t.determ` (453); the other ambient producers (D6); `LogRelBase.TyDefEq.sort` (ShapeLogRel.lean:5300, now via `sort_iff_ty`) | ~150 | R1 | build; tracer still shows only `LR.adequacy` | med | no |
| R3 | ShapeLogRel.lean (`TyDefEq` 5438, `DefEq` 5619, simp lemmas 5661-5662, instance, `lift_succ_aux` 6011) | D1/D2 from E2. Same commit: mark `docs/const-case/{Stuck,Subst1,CtorClause,Fuel}.lean` historical (checked at 3c35f59) and drop them from its `check.sh`/README, because R3 adds `LRS.CtorDefEq` (clash with CtorClause.lean:34) and falsifies `LR.trivial_at_indTy` (Subst1.lean:51); R5's `RHS.fixedLeaves` clashes with Fuel.lean:12 | ~250 | R1, E2 | build; `docs/const-case/check.sh` | low | no |
| R4 | SExpr.lean (`IsDefEqStrong` 1046, its local notation 1044-1045, `⊢ₛ` notation 1334-1335, `closedN` 1367, `weak'` 1387, `weak0` 1426, `CtorProvider` 1805, `mkS` 1818; new defs before `class Params`, 37); ShapeLogRel.lean 5055, 5264; ShapeLogRelAdequacy.lean:48; UniqueTyping.lean:141 (rebuild) | `(E : VEnv)` parameter, `mono`; `closedN`/`weak'`/`weak0` for `hE : E ≤ Params.env`; `VExpr.OnConsts`, `VDefEq.OnConsts`, `rankBound`, `onConsts_rankBound`, `OnConsts.mono`/`mono_k`, `VEnv.below` + lemmas (all before `class Params`); `exists_below`, `mkSE`, `CtorProviderE`/`synE` | ~350 | – | build; `#print axioms IsDefEq.strong` unchanged | low | no: after R2 (it edits ShapeLogRel and ShapeLogRelAdequacy too), or rebase |
| R5 | SExpr.lean (before `class Params`, 37) + Pattern.lean | `piTelescope`, `PatGen`, `Pattern.gen`, `RHS.fixedLeaves`; the D4/D3 Params fields | ~200 | R4 | `lake build`, `lake build Lean4Lean.Tests`, `lake build Lean4Lean.Experimental` (Pattern.lean is in `Lean4Lean.Theory`, imported by Theory/Typing/ChurchRosser, Theory/Typing/UniqueTyping, Experimental/NormalEq); `docs/params/check.sh` (after R12) | med | partly (E3/E4) |
| R6 | SExpr.lean `extra_patV` (59), `Params.extra_pat` (1006); ShapeLogRel 5229-5260; Adequacy 466-474 | D5 λ-restatement (with the typed open equation) and the re-proofs, from E5 | ~250 | R5, R7, E5 | build; tracer unchanged | med | via E5 |
| R7 | ShapeLogRelAdequacy.lean | `LR.adequacy_rank` (WF on k, `induction H`); `.mono` at ~25 sub-derivation uses and at the rebuilt `.lamDF` (296), `.beta` (435), `.eta` (440-441), `.extra` (469) before `soundS`; env membership via `VEnv.below_le` at 195 (`henv.closedC h1`), 470 (`henv.closed.2 h1`), 473 (`extra_pat Γ₀ h1 h2`); `LR.adequacy` from it | ~150 | R2, R4, R5 | build; tracer first block: `constants directly containing sorry (1): Lean4Lean.SExpr.LR.adequacy_rank` | low | no |
| R8 | ShapeLogRelAdequacy.lean | `EnvStrongR` (rank-bounded strong typings from `type_below`/`pat_typed`), `LR.WFIH`/`ConstGoal`/`LocalIH`, `LR.const_local` (D4); `LR.const_spine` stated, body `sorry`; wire the const case to `const_local` at `c₀ := c` (moved here from R11) | ~280 | R5, R7, E3 | build; tracer: `(1): …LR.const_spine` | med | via E3 |
| R9 | ShapeLogRelAdequacy.lean | `LR.const_spine` (D4 statement): induction on `Const` (bot; lam at `ρ.push p` for `LamDefEq`'s typed `p`, data moved by `LE_Interp.mono_l`; ctor → `CtorDefEq` with typed refl; indTy → D2; pat → `LR.pat_leaf_1a`, stated, body `sorry`). Use `spine` (SExpr.lean:2288), not a port of `apps` (Measure6:429 clashes with Stuck.lean:15) | ~400 | R3, R8 | build; tracer: `(1): …LR.pat_leaf_1a` | med-high | no |
| R10 | ShapeLogRelAdequacy.lean | `LR.pat_leaf_1a` (D4 steps 1-6) from E6a + E6 | ~400 | R9, E6 | build; tracer: `constants directly containing sorry (0)`, axioms `Classical.choice`, `Quot.sound`, `propext` | high | via E6 |
| R11 | – | milestone gate (wiring moved to R8): `lake build`, `lake build Lean4Lean.Experimental`, `lake build Lean4Lean.Tests`, tracer | – | R10 | tracer: **no `sorryAx` under `IsDefEq'.uniq`** | low | no |
| R12 | docs/params/EmptyParams.lean, NatParams.lean, check.sh | new fields (trivial for empty); N over `envA` from E4; `check.sh` asserts the sorry-warning count and E4's axiom list (today it only greps `error`, and NatParams has 3 deliberate sorries) | ~350 | R5, R6, E4 | `docs/params/check.sh` | low-med | via E4 |
| R13 | STATUS.md §3/§5/§6, docs/const-case/ | record D6, the stage-1a scope (whole-environment restriction, D3), `WHRedS.defeq` *not* needed, quotients excluded; fix STATUS §6 "`./check.sh` typechecks the experiments" (historical since R3); move this plan to `docs/const-case/PLAN.md` | ~80 | R11 | read | – | no |
| S1 | (after milestone) ShapeS.ctor + ~55 shape declarations + `Const.ctor`/`Matches.app`/`build_spine` | stage 1b (D1); drop `ctor_fields_closed` | 800-1200 | R11 | build + tracer | high | partly |
| S2 | (after S1) | stage 2 (D2/D3 routes); drop `indTy_closed`, `pat_check` | open | S1 | – | open | – |

Critical path: E1 → R1+R2 → R7 → R8 → R9 → R10 → R11, gated by R4 → R5 (before R7), E3 (before R8),
E2 → R3 (before R9) and E6a → E6 (before R10).
- Off the critical path: R6 and R12 (λ-rules and the N instance), E4, E5; R13 after R11.
- Rough size of the stage-1a milestone: ~2 500 repo lines and ~2 950 scratch lines (mostly copied).

---

## 3. First experiment (cheapest falsifier): E1, the typed-LR spike

**Claim tested.** D6 can be added to lean4lean's existing LR (shapes `bot`/`sort`/`forallE`/`lam`;
`ctor`/`indTy` still `True`) while keeping the `bot`, `conv`, `symm`, `trans`, `trans'`, `mono_*`,
`join_ty` and `toType` signatures, with all 19 fields and the lift lemma re-proved.

**Procedure.**
1. Copy `ShapeLogRel.lean:5272-6117` and `ShapeLogRelAdequacy.lean:8-146` into `synth/TypedLR.lean` under `namespace Lean4Lean.SExpr.T`.
2. Add `TyRedS`/`TWHRedS`/`AmbSort` (§1 D1/D6) and apply the D6 edits.
3. Reuse `LRS.LamDefEq.whr_typed` and `inst_congr_beta` (`TypedWhr.lean`).
4. Re-prove until no `sorry` is left; check the E1 axiom list (§2).

**Outcomes.**
- The fields to watch are `whr` (sort and lam cases), `whr_ty`, `conv` (lam case), `mono_l` at `(m ≠ ⊥, sort)`,
  `trans'` and `sort_iff`.
- If any of them cannot be proved, D6-as-specified is false. Switch to the artifact's full design
  (`bot` with a `TyDefEq A A a` hypothesis, `isType`). That adds a `TyDefEq A A a` obligation at each
  of the 15 `bot`/`Adequate.bot` call sites in ShapeLogRelAdequacy.lean.
- If E1 passes, R1 is a transcription and the remaining D6 risk is R2.
- Cost: 1-2 days, scratch only, no other item needed.

E6a then E6 (the pat-leaf dry run) are the second experiment. They test whether D1 + D4 + D5 together
supply everything the pat leaf consumes, untyped field shapes included.

---

## 4. Open questions (with fallbacks)

1. **Can `bot` stay unchanged under D6?** (E1, R2.) Fallback: the artifact's `bot`/`isType` design (§3).
2. **Do the 13 cases supply `AmbSort`/`TyRedS` at every producer** of `(m ≠ ⊥, sort)` and `(lam, forallE)`?
   [A: yes; the list of producers is under D6.] Fallback: as in 1.
3. **Constructor universe levels in iota rules.** `Pattern.Matches.app` discards the argument
   pattern's levels (Pattern.lean:78-82: `app` keeps `f1`, drops `f2`), so `rec.{us} … (c.{us'} …)` matches for any `us'`.
   `Pattern.gen` reads `us'` off the recursor's major domain, and the clause's shared `ls` ties the ambient
   to the spine. Fallback: add `uvars = 0` for `indTy`/`ctor`-classified constants to the stage-1a fields.
4. **`rank_ordered` for Lean's real environment.** It needs `Theory/Inductive.lean:7` (`addInduct`,
   `sorry`) and an extensional prefix argument (patleaf code refuter). It stays a Params assumption and
   is fine for N. No fallback needed for the milestone.
5. **λ-rule re-proofs (E5/R6) are harder than estimated.** Fallback: keep `Δ = []`. Then
   `pat_defeq` is satisfiable only with `Pat` ⊆ closed env rules (N would need `Pat = ∅`), and Lean's
   λ-wrapped iota rules are listed as excluded. The const-case proof itself does not depend on R6:
   R10 does not, only R12 does.
6. **Pat-leaf integration (E6) needs more than the clause provides.** No cheap fallback.
   R1/mini-adequacy is circular (patleaf C14). If E6 shows a missing typed fact, add it to the clause
   as a further `TWHRedS`/typed conjunct; the pattern is that of `CtorDefEq1a`. A clause conjunct
   cannot repair untyped valuation entries; that is E6a (lowering, or typed ctor fields).
7. **Level bookkeeping in the spine lemma.** `LamDefEq` descends one level per argument, while
   `Const` keeps all `rargs` at one level (ShapeLogRel.lean:3323-3330). The plan uses a
   level-polymorphic statement at every `ρ ≥ ofRargs rargs` (`LR.const_spine`, D4) and `LR.DefEq.lift`,
   as `lamDF`/`appDF` already do. Fallback: none needed [A].
8. **Stage 1b codes vs the model (`build_spine` typedness of `rargs`, model lens A2 "HARD").**
   Fallback: stay at stage 1a and extend `ctor_fields_closed` to closed Π-types of closed
   inductives only if a canonical-shape argument exists [A, unexplored].
9. **Stage 2 (`indTy qs` hybrid).** Unverified. Falsifier: the `KappaMonoR1.lean` construction
   adapted to `indTy qs` (`mono_r_1` raising `qs`).

---

## 5. What stays excluded, and where each exclusion is encoded

| excluded | encoded by | evidence |
|---|---|---|
| K-like reduction (major is a variable + `Check`) | `pat_simple` (SimplePattern has no var major, Pattern.lean:234-240); `pat_check` (stage 1a) | [R] |
| iota on Prop-valued inductives (`Eq.rec`, `Acc.rec`, `And.rec`, subsingleton elimination) | `ctor_sort` (SExpr.lean:84-88) + `pat_wf` (SExpr.lean:18-21: pattern ctor heads must be `.ctor`) | model X2, upheld |
| structure eta on variables | no eta rule in `WHRed` (SExpr.lean:2458-2463) or `IsDefEq`; structures classified `.ctor` | B §7 [R] |
| `etaCtor` | inert: `etaCtor` constants interpret only to `⊥` | `Inert.lean` [T] |
| `PUnit` and universe-polymorphic inductives instantiable at Prop | `ctor_sort` | SExpr.lean:76-88 (doc + field) [R] |
| quotients | `ctor_sort` (`Quot.mk.{0}` lives in Prop); stage 1a also `indTy_closed` | `QuotLevel.lean` [T] |
| parameters, indices, non-inductive field types (stage 1a) | `indTy_closed`, `ctor_fields_closed`: a whole-environment restriction, not a kernel invariant (no env with rules for such an inductive) | D3 |
| nested/reflexive inductives (recursive call under a binder) | `Pattern.RHS` has no `lam` (Pattern.lean:104-107), so the rule cannot be in `Pat` | [R] |
| mutual definitions whose bodies mention same-rank constants non-bare | `pat_typed` (body typed in `env.below (rank head)`) | [A] |
| λ-wrapped rules (until R6 lands) | today's `extra_patV` (`extra_patV_false_envA`, `no_lam_rule`) | [T] |

---

## 6. Audit log

- r1 #1, D5/E5/R6/§0.15: `extra_patV` (λ) gains `df.type.instL ls = Δ.foldr .forallE T`, `OnCtx Δ.reverse`, `env.IsDefEq univs Δ.reverse L R T` (#10's form; it implies #1's two `HasType`s); E5 deps E1, runs on `T.LR`; §0.15 extended.
- r1 #2, R4/D4 step 3: `closedN`/`weak'`/`weak0` for `E ≤ Params.env` added to R4 and D4 re-proof cost (`WeakE.lean`); step 3 uses the E-version of `weak'`.
- r1 #3, E1/E6: E1 also copies ShapeLogRel.lean:6068-6117 and ShapeLogRelAdequacy.lean:8-146 into `T`; the +250 lines go on E1, not E6, since E5 needs them too.
- r1 #4, R4/R5/R7: `OnConsts`/`rankBound` and lemmas moved from R5 into R4, before `class Params`; R7 deps + R5; `below_le` transfers and the `.mono` of rebuilt derivations noted (line numbers corrected, see notes).
- r1 #5, §2 R10 + critical path: R6 dropped from R10 deps; critical path restated with the R4 → R5, E3, E2 → R3 and E6a → E6 gates.
- r1 #6, R1/R2/R4/D4: R1 verify is `lake build Lean4Lean.Experimental.ShapeLogRel` and R1 lands with R2; R2 lists the extra breakage sites (lines corrected); R4 file column + sequencing after R2; site count split 11 + 2 + 1.
- r1 #7, R3/R13/R9: docs/const-case retirement moved into R3's commit; STATUS §6 sentence in R13; R9 uses `spine`, not `apps`.
- r1 #8, §2 verify/D4: named axiom targets for E1, E2, E4, E5, E6a, E6; `pat_leaf_1a` and `const_spine` statements written in D4 and typechecked as statements (`PatLeafStmt.lean`); tracer expectations for R7-R10; R11's wiring moved into R8.
- r1 #9, R5/E4/R12: R5 verify adds `lake build` and `lake build Lean4Lean.Tests`; E4/R12 assert the sorry count and axiom list.
- r1 #10, D5/D6/E5: applied together with #1 (`LamRuleTyped.lean` cited in D5, D6 and §0.15).
- r1 #11, D1/D3/D4 steps 1-2/new E6a/§4 Q6: field entries lowered (option (a), default) or typed ctor fields (option (b), fallback), as item E6a before E6.
- r1 #12, D4 spine lemma/R9/§4 Q7: spine lemma stated at every `ρ ≥ ofRargs rargs` covered by a `SubstWF`; lam case via `ρ.push p` + `LE_Interp.mono_l`.
- r1 #13, §0.5/D3/D4 fields/§5: stage-1a fields stated as a whole-environment restriction; Prop fields at `⊥` (chosen over a `u ≠ 0` field); the other new fields recorded as kernel invariants [A].
- r1 #14, D5 + table/E4: 3 binders (zero rule), 4 (succ rule).

### Audit notes

- r1 #1: its evidence "no `lam_inv` in Theory/" is wrong: `VEnv.HasType.lam_inv` exists (Theory/Typing/Strong.lean:784). It types the body at some type only, so the gap stands (#10).
- r1 #4: cited lines were off. Actual: `henv.closedC h1` 195 (not 189), `henv.closed.2 h1` 470 (not 469), rebuilt `.lamDF` 296 (not 328), `.eta` 440-441 (not 443/445), `.extra` 469 (not 472); `class Params` is at SExpr.lean:37 (not 41).
- r1 #6: cited lines were off. Actual: `WHNF.forallE.whRedS red` 274 (not 281-283), `.rfl` producers 327/383/396/411 (not 331, 391-419), `whr_t.determ` 453 (not 446-447); 495, 498 and 515 also break.
