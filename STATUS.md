# Unique typing for Lean's type theory: where this branch stands

This is a fork of [digama0/lean4lean](https://github.com/digama0/lean4lean)
(branch `unique-typing`, based on upstream `master` at `67f63b0`, 2026-10-10).
Its only purpose is to finish a proof of the **unique typing** conjecture for
Lean's type theory. Everything here builds on Mario Carneiro's metatheory in
`Lean4Lean/Theory/` and his 2026 experimental work in `Lean4Lean/Experimental/`.
This document is the entry point for contributors. It states exactly what is
proven, what is assumed, what is left, and how to check each claim yourself.

## 1. The theorem

Lean4Lean Conjecture 2.7 (Carneiro, [arXiv:2403.14064](https://arxiv.org/abs/2403.14064)):

> If `Γ ⊢ e : α` and `Γ ⊢ e : β`, then `Γ ⊢ α ≡ β : U_ℓ` for some `ℓ`.

The typing judgment is `VEnv.IsDefEq` in `Lean4Lean/Theory/Typing/Basic.lean`,
a single inductive relation `Γ ⊢ e ≡ e' : A` with definitional proof
irrelevance, η, environment rewrite rules (`extra`) and a typed conversion rule.
The conjecture is open: the 2019 thesis proof has a gap (stratification does not
respect substitution), and as of October 2026 nobody has closed it. Pi- and sort-
injectivity (Conjecture 2.9) are its sister conjectures.

`Lean4Lean/Theory/Typing/UniqueTyping.lean` already derives unique typing from
three sorried inversion lemmas in `Lean4Lean/Theory/Typing/Injectivity.lean`.
So on the `VExpr` side the whole problem is **definitional inversion**.

## 2. The route (Carneiro, May–June 2026)

All the action is in `Lean4Lean/Experimental/`:

| file | lines | what it is |
|---|---|---|
| `SExpr.lean` | ~1850 | `SExpr`: the same syntax with universe levels quotiented semantically (`SLevel`). `SExpr.IsDefEq` is the same rule set **plus one extra rule** `trans'`: transitivity where the middle term may sit at a different sort. The `Params` class bundles the environment and the pattern data (§5). |
| `ShapeLogRel.lean` | 6100 | A finitary domain model ("shapes") and a logical relation over it. This is the Lean incarnation of [*Definitional Inversion, Without Normalisation*](https://arxiv.org/abs/2607.13662) (Carneiro, Coquand, Frabetti Mathieu, Lennon-Bertrand, Melliès, Weirich, 2026), extended with constants, constructor shapes and pattern rules. No normalisation is used anywhere, because Lean's theory is not normalising. |
| `ShapeLogRelAdequacy.lean` | ~470 | The fundamental lemma `LR.adequacy`, and from it Pi-injectivity `forallE_inv`, sort injectivity `sort_inv` and sort/Pi disjointness `sort_forallE_inv`, all for the `trans'` system. |
| `UniqueTyping.lean` | ~370 | With injectivity in hand, unique typing for the `trans'` system is a plain induction (`HasTypeS.uniq`). That gives `uniq_sort`, which makes `trans'` admissible: `IsDefEq.iff_isDefEq'` shows the `trans'` system equals `IsDefEq'`, which has exactly Lean's rules. The corollary `IsDefEq'.uniq` is the theorem for `SExpr`. The last section translates `VEnv.IsDefEq` into `SExpr.IsDefEq` (`IsDefEq.mkS`) and reflects sort injectivity and sort/Pi disjointness back to `VExpr`. |

Why `trans'` matters: the naive induction for unique typing needs to chain
`α ≡ β : U_i` with `β ≡ γ : U_j` before knowing `i = j`, and `i = j` is itself
an instance of unique typing. `trans'` lets the induction go through first; sort
uniqueness then shows `trans'` was admissible all along.

## 3. Check the claims yourself

```sh
lake build Lean4Lean.Experimental.UniqueTyping   # about one minute from a warm cache
lake env lean scripts/TraceSorry.lean
```

`scripts/TraceSorry.lean` walks the dependency graph of the final theorem and
prints two lists: the axioms it reaches, and every constant whose own body
contains `sorry`. On this branch, for `IsDefEq'.uniq`, the output is:

```
axioms reached (4): Classical.choice, Quot.sound, propext, sorryAx
constants directly containing sorry (4):
  Lean4Lean.SExpr.IsDefEq.defeqDF_l'
  Lean4Lean.SExpr.IsDefEq.strong
  Lean4Lean.SExpr.IsDefEq.subst
  Lean4Lean.SExpr.LR.adequacy
```

No project-specific axioms remain. Three of the four sorries are one cluster
(the strong judgment, §4.2). The fourth is the real gap (§6).

## 4. What this branch changed

Each item is one or a few commits; `git log upstream/master..unique-typing`
lists them.

### 4.1 Fixed statements that were false or unprovable as written

- `Ctx.SubstEq` had only an identity base case, so a substitution could never
  be pushed under a binder: `Ctx.SubstEq.lift` was unprovable, and its
  hypothesis was the wrong one. It now has a `weak` constructor; `lift` and
  `lookup` are proven. (`8fae8db`)
- `IsDefEq.strong : Γ ⊢ e1 ≡ e2 : A → IsDefEqStrong Γ e1 e2 A` is **false**
  without a well-formed-context hypothesis: `[bvar 5] ⊢ bvar 0 : bvar 6` holds
  in the weak system and has no strong derivation. A counterexample is
  formalised on branch `strong`. The fix threads `⊢ Γ` through the chain, as
  `Theory/` does with `OnCtx Γ (env.IsType U)`.
- `Params.ctor_ty` cannot be derived from a defeq-only description of
  constructor types (strengthening it is circular). Constructor types must be
  assumed *syntactically* a Π-telescope ending in the inductive type, which is
  what Lean's kernel guarantees. (branch `strong`, `ae87af1`)

### 4.2 Closed gaps

| gap | status |
|---|---|
| `IsDefEqStrong.defeq` | proven (`f29e16a`) |
| `WHRed.determ`, the `extra` cases | proven from `pat_simple` and `pat_uniq` alone (`e8c6bd8`) |
| axiom `Params.extra_pat` | now a theorem, derived from a `VExpr`-level `Params` field `extra_patV` (`09407ee`) |
| sorried `Params.ctor_ty` | now a theorem, derived from a `VExpr`-level field (`cb5fae8`; being replaced by the syntactic form on branch `strong`) |
| typing of environment constants in `SExpr` | `Params.const_wf`, `Params.defeq_wf`, derived from `henv : env.Ordered` through the translation (`c6fe5e8`) |
| translation `VEnv.IsDefEq → SExpr.IsDefEq` | `SExpr.IsDefEq.mkS`, a port of the closed upstream PR #37 including its `mkInst` fix (`e13a52d`, `ed87ab6`) |
| `IsDefEq.strong`, `IsDefEq.subst`, `IsDefEq.defeqDF_l'`, `IsDefEq.isType` | proven in scratch for the `⊢ Γ` versions, no sorry; integration in progress on branch `strong` |

When branch `strong` lands, the tracer should list exactly one sorry:
`LR.adequacy`.

## 5. What is assumed: the `Params` class

`SExpr.Params` is a hypothesis package, not an axiom. No instance exists in the
repo yet. Its fields:

- `env`, `henv : env.Ordered`, `univs`: the environment and ambient universe count.
- `Pat`, `classify`, `pat_simple`, `pat_wf`, `pat_uniq`: every rewrite rule is a
  simple pattern (delta or iota), heads are classified (`symb`, `ctor`,
  `etaCtor`, `indTy`), and matching patterns coincide.
- `extra_patV`: every instantiated environment rule is an instance of such a
  pattern, with its side conditions holding.
- `ctor_tyV` (to become `ctor_syn` + `ctor_sort`): constructor types are a
  Π-telescope over the inductive type, at a sort that is never `Prop`.

Building a `Params` instance for the environments Lean4Lean actually produces
is future work and depends on the still-unfinished inductive-type
specification in `Theory/Inductive.lean`. Known exclusions of the model, which
the paper's conclusion also names: K-like reduction, iota on Prop-valued
inductives (`Eq.rec`, `Acc.rec`), universe-polymorphic inductives that can be
instantiated at `Prop` (`PUnit`), and structure eta on variables. These are
limitations of the current shape model, not of the route.

## 6. The open problem: the `const` case of `LR.adequacy`

`LR.adequacy` (`ShapeLogRelAdequacy.lean`, around line 150) is proven by
induction on the strong derivation; 13 of its 14 cases are done. The `const`
case has been a sorry since the model started interpreting constants
non-trivially (April 2026). Two independent analyses on this branch reached
the same conclusions; the full write-ups and the experiments that back them are
in `docs/const-case/`.

**It is a design gap, not a proof gap.** The logical relation `LRS.DefEq` is
literally `True` at inductive type-shapes (`ShapeLogRel.lean`, `LRS.DefEq`,
case `indTy`). So a variable can be related at a constructor shape such as
`succ zero`, the model then fires a recursor rule at the shape level, and
adequacy demands a syntactic head reduction of `rec … (bvar 0)` that cannot
happen. With the relation unchanged the lemma is false, not merely unproven
(`docs/const-case/Stuck.lean`, `Subst1.lean`, and §2 of
`DESIGN-fuel-measure.md`).

**What has to change.**

1. A constructor clause in `LRS.DefEq` at `(m = ctor c l, a = indTy)`: both
   terms head-reduce to `c` applied to a spine whose arguments are related at
   the shapes in `l`. This is exactly the paper's treatment of `ℕ` (clauses for
   `zero` and `succ`); its public Lean artifact has the whole thing worked out,
   including the re-proofs of every logical-relation field. The port to
   arbitrary inductives is designed in `DESIGN-ctor-clause-from-artifact.md`;
   the clause and its `left`/`symm` lemmas typecheck (`CtorClause.lean`).
2. A `major` rule in `SExpr`'s `WHRed` (reduction in major-premise position).
   `Theory/Typing/HeadReduction.lean` has it; the `SExpr` version dropped it.
   Without it a recursor whose argument merely *reduces* to a constructor can
   never fire.
3. A termination measure for rule right-hand sides, which are not
   subderivations. The answer, taken from the artifact's fixpoint case: keep the
   outer induction on the derivation, and inside the `const` case induct on the
   *interpretation* derivation `hM : LE_Interp ρ m (const c ls)`. Its `R`
   premise makes every unfolding a strict subderivation, even for recursors
   that occur in their own right-hand sides. Closed leaves of a rule that are
   not in the same recursive block need typing premises on
   `IsDefEqStrong.const` (and `Params` fields for them). See §3–4 of
   `DESIGN-fuel-measure.md`.

The largest remaining risk is reconciling type shapes for parametric
constructor fields (the model collapses all inductive types to one code
`indTy`); see §7 of `DESIGN-ctor-clause-from-artifact.md`.

## 7. After the `SExpr` theorem

- Reflection to `VExpr`. `IsDefEq.mkS` goes forward. Backward, sort
  injectivity and sort/Pi disjointness reflect completely
  (`VEnv.IsDefEqU.sort_invS`, `sort_forallE_invS`), because their conclusions
  are a level equality or `False`. Pi-injectivity (`forallE_invS`) stops at an
  `SExpr` defeq: an inverse translation `IsDefEq' → VEnv.IsDefEq` is needed
  (choose representatives for levels and preimages for intermediate terms).
- Then the three sorries in `Theory/Typing/Injectivity.lean` can be discharged
  and `Theory/Typing/UniqueTyping.lean` becomes a theorem about Lean's
  `VExpr` theory, under a `Params` instance.

## 8. Working conventions on this branch

- Prove in a scratch file first (`import Lean4Lean.Experimental.SExpr` or
  `...ShapeLogRelAdequacy`, `namespace Lean4Lean.SExpr`, `variable [Params]`),
  check `#print axioms`, then splice. The tracer function in
  `scripts/TraceSorry.lean` can be pasted into any scratch file.
- Never claim a result while the tracer shows `sorryAx` or a custom axiom on
  its path. Statements matter as much as proofs: two sorried statements on
  upstream were false as written.
- Keep commits per lemma; keep `lake build Lean4Lean.Experimental` green.
- Upstream: `digama0/lean4lean`, issue #16 (contributing proofs), closed PR #37
  (the translation). The TYPES 2025 slides end with "type theorists wanted".

## 9. Reading list

- Lean4Lean paper, §2.4 (the conjectures): [arXiv:2403.14064](https://arxiv.org/abs/2403.14064).
- *Definitional Inversion, Without Normalisation*: [arXiv:2607.13662](https://arxiv.org/abs/2607.13662).
  Its Lean artifact (`DomainSemantics`) proves `HasType.uniq` and `IsDefEq.iff`
  for a small theory with `ℕ`, `Σ`, `Id` and a fixpoint combinator, with no
  sorries; it is the template for everything in §6.
- Carneiro's thesis (2019) for the original, gapped proof and the `≡p`
  Church–Rosser statement.
