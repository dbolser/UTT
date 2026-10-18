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
| `ShapeLogRel.lean` | ~6100 | A finitary domain model ("shapes", `WShape`), the interpretation of terms into it (`LE_Interp`, line ~3333), and a logical relation over it (`LogRel`, `LRS.DefEq`, `LRS.TyDefEq`). This is the Lean form of [*Definitional Inversion, Without Normalisation*](https://arxiv.org/abs/2607.13662) (Carneiro, Coquand, Frabetti Mathieu, Lennon-Bertrand, Melliès, Weirich, 2026), extended with constants, constructor shapes and pattern rules. No normalisation is used anywhere; Lean's theory is not normalising. |
| `ShapeLogRelAdequacy.lean` | ~470 | The fundamental lemma `LR.adequacy`, and from it Pi-injectivity `forallE_inv`, sort injectivity `sort_inv` and sort/Pi disjointness `sort_forallE_inv`, all for the `trans'` system. |
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
6100-line logical relation; expect several minutes. Later builds of the route
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
  Lean4Lean.SExpr.LR.adequacy
```

No project-specific axioms remain. The one sorry on the path is the `const`
case of the fundamental lemma (§6). The environment-side theorems
(`Params.const_wf`, `defeq_wf`, `extra_pat`, `ctor_ty`, `envStrongS`,
`IsDefEq.strong`) reach no sorry at all. The tracer reports the path only:
`grep sorry` finds about twenty more sorried lemmas in `SExpr.lean` and
`ShapeLogRel.lean` inherited from upstream and off the path (for example
`WHRed.subst`, `WHRedS.defeq`, `InferType.hasType`, `Shape.WF.plift`).
`WHRedS.defeq` is one the plan in §6 will need.

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

## 5. What is assumed: the `Params` class

`SExpr.Params` (`SExpr.lean`, top) is a hypothesis package, not an axiom. Two
instances live in `docs/params/` (experiments, not part of the build; see its
`README.md`). Its fields:

- `env`, `henv : env.Ordered`, `univs`: the environment and ambient universe count.
- `Pat`, `classify`, `pat_simple`, `pat_wf`, `pat_uniq`: every rewrite rule is
  a simple pattern (delta or iota), heads are classified (`symb`, `ctor`,
  `etaCtor`, `indTy`), and overlapping patterns coincide.
- `extra_patV`: every instantiated environment rule is an instance of such a
  pattern, with its side conditions holding.
- `ctor_syn`, `ctor_sort`: constructor types are syntactically a Π-telescope
  over the inductive type, at a sort that is never `Prop`.

`extra_patV` as stated does not fit schematic rules. For the `ℕ` environment
with its two iota rules lambda-wrapped (Lean4Lean's own `vdefeq` convention) it
is false for every choice of `Pat`, because `Pattern.Matches` has no `lam` case
(`docs/params/NatParams.lean`: `extra_patV_false_envA`); that this environment
is `Ordered` rests on two routine typing sorries there. The open-`bvar`
encoding is pattern-matchable but not `VDefEq.WF` (`iotaZeroOpen_not_wf`). So
far the field holds only for rule-free environments
(`docs/params/EmptyParams.lean`; `natParams` over the constants-only `ℕ`
environment). Reformulating it is an open item (§8).

Building a `Params` instance for the environments Lean4Lean actually produces
depends on the inductive-type specification in `Theory/Inductive.lean`, which
is a stub. The paper's conclusion names (co)inductive types and proof
irrelevance with axiom K as not yet covered. This fork's shape model
additionally excludes K-like reduction, iota on Prop-valued inductives
(`Eq.rec`, `Acc.rec`), universe-polymorphic inductives instantiable at `Prop`
(`PUnit`), and structure eta on variables; see
`docs/const-case/DESIGN-fuel-measure.md` §7 for how each exclusion is encoded
(`pat_wf`, `ctor_sort`, the absence of a `major`-style eta rule). These are
limitations of the current model, not of the route.

## 6. The open problem: the `const` case of `LR.adequacy`

`LR.adequacy` (`ShapeLogRelAdequacy.lean`, line ~106; the sorry is in the
`const` case near line 150) is proven by induction on the strong derivation;
13 of its 14 cases are done. The `const` case has been a sorry since the
model started interpreting constants non-trivially (April 2026). Two
independent analyses on this fork reached the same conclusions; the write-ups
and the experiments backing them are in `docs/const-case/` (`./check.sh`
typechecks the experiments).

**It is a design gap, not a proof gap.** The logical relation is `True` at
inductive type-shapes: `LRS.DefEq` (`ShapeLogRel.lean` ~5619) has
`| .indTy => True` (~5633), and `LRS.TyDefEq` (~5438) is `True` at `ctor` and
`indTy`. So a variable can be related at a constructor shape such as
`succ zero`, the model then fires a recursor rule at the shape level, and
adequacy demands a syntactic head reduction of `rec … (bvar 0)` that cannot
happen. With the relation unchanged the lemma is false, not merely unproven
(`Stuck.lean`, `Subst1.lean`, and §2 of `DESIGN-fuel-measure.md`). Both
`True` clauses have to change.

**What has to change.**

1. A constructor clause in `LRS.DefEq` at `(m = ctor c l, a = indTy)`: both
   terms head-reduce to `c` applied to a spine whose arguments are related at
   the shapes in `l`. This is the paper's treatment of `ℕ` (clauses for `zero`
   and `succ`). The paper's Lean mechanisation, supplementary material at
   [anonymous.4open.science/r/domain-semantics-lean-BEE7](https://anonymous.4open.science/r/domain-semantics-lean-BEE7),
   has it worked out for `ℕ`, `Σ`, unit, `Id`, `Prop` and a fixpoint
   combinator, including the re-proofs of every logical-relation field; its
   umbrella file pins the axiom lists of `HasType.uniq`, `IsDefEq.iff` and
   eight more headline theorems with `#guard_msgs` (we read it; we did not
   rebuild it). The port to arbitrary inductives is designed in
   `DESIGN-ctor-clause-from-artifact.md`; the clause and its `left`/`symm`
   lemmas typecheck (`CtorClause.lean`).
2. A `major` rule in `SExpr`'s `WHRed` (reduction in major-premise position).
   `Theory/Typing/HeadReduction.lean` has it; the `SExpr` version dropped it.
   Without it a recursor whose argument merely *reduces* to a constructor can
   never fire. Done (`b2516c4`): `WHRed.major`, `IsMajorPremise`,
   `WHRedS.major`, and `WHRed.determ` re-proven with the new case.
3. A termination measure for rule right-hand sides, which are not
   subderivations. Taken from the mechanisation's fixpoint case: keep the
   outer induction on the derivation and, inside the `const` case only, induct
   on the *interpretation* derivation `hM : LE_Interp ρ m (const c ls)`. Its
   `R` premise makes every unfolding a strict subderivation, even for
   recursors that occur in their own right-hand sides. Closed leaves of a rule
   outside the same recursive block need typing premises on
   `IsDefEqStrong.const` and matching `Params` fields. See §3–4 of
   `DESIGN-fuel-measure.md`.

The ordered work plan is §9 of `DESIGN-ctor-clause-from-artifact.md`
("Required changes, in dependency order") together with §3 of
`DESIGN-fuel-measure.md`; a merged plan reconciling the two will be added as
`docs/const-case/PLAN.md`. The largest known risk is reconciling type shapes
for parametric constructor fields, since the model collapses all inductive
types to one code `indTy` (§7 of the artifact design).

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
- Reformulate `extra_patV` so lambda-wrapped iota rules are pattern instances
  (strip binders, or state it on the beta-applied form) and re-derive
  `Params.extra_pat` (`SExpr.lean` ~1006) and its model-side uses.
- `ctor_sort` for `ℕ` (`docs/params/NatParams.lean`, `ctor_sort_nat`) needs
  `IsDefEqU.sort_inv` (`Theory/Typing/Injectivity.lean`); currently `sorry`.
- Prove `WHRedS.defeq` in `SExpr.lean` (head reduction is a definitional
  equality at the term's type), which §6 needs.

## 9. Reading list

- Lean4Lean paper, §2.4 (the conjectures): [arXiv:2403.14064](https://arxiv.org/abs/2403.14064).
- *Definitional Inversion, Without Normalisation*: [arXiv:2607.13662](https://arxiv.org/abs/2607.13662),
  and its Lean mechanisation (link in §6).
- Carneiro's thesis, *The Type Theory of Lean* (2019), for the original
  gapped proof and the `≡p` Church–Rosser statement:
  [github.com/digama0/lean-type-theory](https://github.com/digama0/lean-type-theory).
- Upstream issue #16 (contributing proofs) and closed PR #37 (the translation).
