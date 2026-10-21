# Experiment E1 (the typed-LR spike): PASS

2026-10-19. Plan: `../../PLAN.md` §3 (procedure), §1 D6 (the design under test), §2 rows E1/R1/R2.
Base: commit `3c35f59` (`/tmp/utt-snap6`-style snapshots; every line number below is HEAD's).
Run: one workflow, two independent Opus attempts for each half, each checked by an independent
adversarial verifier that rebuilt from clean, grepped for cheats, printed axioms, ran the tracer
and compared every statement with the original by `Expr` equality. All four verdicts: pass.

## 0. Outcome

**D6 holds.** Typed reductions can be added to the existing shape logical relation with the
`bot`, `conv`, `symm`, `trans`, `trans'`, `mono_*`, `join_ty`, `toType` and `left*` signatures
unchanged and `(⊥, ·)` still `True`:

- Part 1 (`TypedLR.lean`, a copy of `ShapeLogRel.lean:5272-6117`): all 19 `LogRel` fields of
  `LR0` and `LRS`, `LR.lift_succ_aux` in both directions, `LR.DefEq.lift`, `LR.TyDefEq.lift`,
  `LR.Subst1`, `LR.SubstWF`. No `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`.
  Both attempts closed every field the plan listed as the likely failure points (`whr` at
  `sort` and at `lam`, `whr_ty`, `conv` at `lam`, `mono_l` at `(m ≠ ⊥, sort)`, `trans'`,
  `sort_iff`, the lift ⇐ directions). The fallback design (artifact-style `bot` with a
  `TyDefEq A A a` hypothesis and an `isType` field) was not needed.
- Part 2 (`TypedAdequacy.lean`, a copy of `ShapeLogRelAdequacy.lean:8-515` over the typed
  relation): all 13 proven cases of `LR.adequacy` and the corollaries `forallE_whRed_l`,
  `forallE_inv`, `sort_inv`, `sort_forallE_inv` go through. The only `sorry` is the `const`
  case, at the same site as the original's line 196. Every typed reduction and every new
  ambient conjunct came from the case's own derivation, substituted; no `⊢ Γ` index beyond
  `W.wf₀` was needed, and `WHRedS.defeq` (subject reduction) was not used.

So R1 and R2 of the plan are a transcription of these two files.

## 1. The definitions as implemented

```lean
def TyRedS (Γ : List SExpr) (A A' : SExpr) : Prop := (∃ w, Γ ⊢ A ≡ A' : .sort w) ∧ Γ ⊢ A ⤳* A'
def TWHRedS (Γ : List SExpr) (M M' A : SExpr) : Prop := Γ ⊢ M ≡ M' : A ∧ Γ ⊢ M ⤳* M'
def AmbSort (Γ : List SExpr) (A : SExpr) : Prop := ∃ v w, Γ ⊢ A ≡ .sort v : .sort w
```

The four changed `LogRel` fields (the other fifteen are byte-for-byte the originals):

```lean
  sort_iff    : DefEq M N A (.sort r) (.sort r') ↔ AmbSort Γ A ∧ ∃ u, TyRedS Γ M (.sort u) ∧ TyRedS Γ N (.sort u)
  sort_iff_ty : TyDefEq M N (.sort r) ↔ ∃ u, TyRedS Γ M (.sort u) ∧ TyRedS Γ N (.sort u)
  whr         : TWHRedS Γ M M' A → TWHRedS Γ N N' A → (DefEq M N A m a ↔ DefEq M' N' A m a)
  whr_ty      : TyRedS Γ A A' → TyRedS Γ B B' → (TyDefEq A B m ↔ TyDefEq A' B' m)
```

Concrete relations: `LR0.TyDefEq` at `sort` and `LRS.TyDefEq` at `sort` use `TyRedS`;
`LR0.DefEq` and `LRS.DefEq` at a `sort` type shape are `True` for `m = ⊥` and
`AmbSort Γ A ∧ TyDefEq … m` otherwise (written as `match m.1 with | .bot => True | _ => …`);
`LRS.ValTyPi2` and the `.lam` row of `LRS.DefEq` use `TyRedS Γ A (.forallE A₁ A₂)` in place of
the untyped reduction. `ctor`/`indTy` rows are unchanged (`True`); D1/D2 are not part of E1.

Statements that had to change besides those (each forced by D6, each found by both attempts):

| declaration | original | now |
|---|---|---|
| `LR0.DefEq` | `(Γ) (M N : SExpr) (m a : WShape 0)` | gains the ambient argument `A`, because its `sort` row mentions `AmbSort Γ A`; the `LR0` instance field is `DefEq := LR0.DefEq Γ` |
| `LRS.DefEq.sort_a` (5637, `rfl`) | `DefEq IH M N A m (.sort r) = TyDefEq IH M N m` | false under D6; split into `bot_sort : DefEq IH M N A .bot (.sort r) = True := rfl` and `sort_a (hm : m ≠ .bot) : DefEq IH M N A m (.sort r) ↔ AmbSort Γ A ∧ TyDefEq IH M N m`; the two uses (5769 in `mono_r_1`, 5806 in `mono_l`) are re-proved with `by_cases m = ⊥` |
| `LRS.TyDefEq.sort_iff` (5444), `LRS.DefEq.lam_forallE` (5639) | untyped `⤳*` | `TyRedS`, exactly as D6 says; still `.rfl` / `simp only [Subtype.eta]` |
| `LRS.LamDefEq.whr` (5603) | untyped reductions | cannot be stated untyped once `IH.whr` is typed (nothing types `M a ≡ M' a`); replaced by `LRS.LamDefEq.whr_typed` from `TypedWhr.lean` (hypotheses `Γ ⊢ A ≡ .forallE A₁ A₂ : .sort w` and the two `TWHRedS`) |
| `whr` field implicit order | `{M M' N N' A m a}` | `{M M' A N N' m a}` (auto-bound from D6's text); all six callers pass hypotheses explicitly |

New helpers (all sorry-free): `TyRedS.sort`, `TyRedS.whnf_l`, `TyRedS.trans`, `TyRedS.ambSort`,
`TWHRedS.toTyRedS`, `LR0.TyDefEq.left/symm/trans/whr`, `LRS.TyDefEq.whr`, `LRS.DefEq.bot_sort`,
`LRS.LamDefEq.whr_typed`, `lift_ne_bot`. Everything else keeps its statement: the verifier's
`Expr`-equality script found 75 declarations identical to the originals (including the private
`lift_aux` lemmas and all of `LR.SubstWF`), 9 changed exactly as above, 16 new.

## 2. Why the proofs go through

- **Composing typed reductions** looked like it needed unique typing (`A ≡ A' : sort w₁`
  with `A ≡ sort u : sort w₂`). It does not: `IsDefEq.trans'` (`SExpr.lean:883`) is
  transitivity across different sorts. `TyRedS.whnf_l` and `TyRedS.trans` use it. This is the
  same observation that made `trans'` the route's extra rule in the first place.
- **`whr` at `sort`, `m ≠ ⊥`**: the row's own `AmbSort Γ A` retypes `M ≡ M' : A` to
  `M ≡ M' : sort v` (`defeqDF`), giving `TyRedS Γ M M'`; then the old `whr_ty` argument
  (`LRS.TyDefEq.whr`) applies. At `(⊥, sort)` it is `True ↔ True`.
- **`whr` at `(lam, forallE)`**: `LRS.LamDefEq.whr_typed`, with the row's
  `TyRedS Γ A (.forallE A₁ A₂)` supplying the typed Π equation.
- **`conv`**: at `sort` it gets `AmbSort Γ B` from `TyRedS Γ B (sort u)`; at `lam` it gets
  `TyRedS Γ A' (.forallE …)` from `ValTyPi2`. `inst_congr_beta` was not needed here, since
  `IH.conv`'s signature is unchanged.
- **`mono_l` at `(m ≠ ⊥, sort)`** copies `AmbSort`, since `m ≤ m'` and `m ≠ ⊥` give `m' ≠ ⊥`.
  `trans'` at a `forallE` type shape is still ruled out by `WHNF.sort.whRedS` on the `.2` part.
  `LR.lift_succ_aux` at `sort` uses `lift_ne_bot` and copies `AmbSort`.

## 3. The adequacy edit sites (R2)

| original line | change |
|---|---|
| 183 (`sort`) | `sort_iff.2 ⟨⟨_, _, .sort⟩, _, .sort, .sort⟩` |
| 274 (`appDF`) | `WHNF.forallE.whRedS red.2` |
| 285-292 (`lamDF`, the `suffices`) | four typing premises added to the proof-internal `suffices` (`Γ ⊢ A ≡ X : sort u`, `X::Γ ⊢ Y : B`, and primed), passed from the strong premises at its three uses; local helpers `bodyTy`, `tbeta` (a `TWHRedS` from `IsDefEq.beta` plus a codomain conversion), `hBsub` |
| 346, 353, 356 (`lamDF` beta steps) | typed via `tbeta` |
| 382, 395, 410 (`forallEDF`) | each tuple gets the `AmbSort` prefix `⟨_, _, .sort⟩`; the reflexive `TyRedS` proofs come from `IsDefEq.forallEDF HA.defeq HBody.defeq` substituted |
| 436 (`beta`) | typed by `Happ.defeq.subst` and `(IsDefEq.beta He.defeq Ha.defeq).subst` |
| 453 (`whr_t.determ`) | `whr_t.2.determ .forallE whr_N.2 .forallE` |
| 456 (`eta`) | `.appDF` of the substituted `IsDefEq.eta`, converted by the typed equation inside `whr_t` |
| 474 (`extra`) | typed directly by `IsDefEq.extra h1 h2` in `Γ₀` (`Δ = []`, today's `extra_patV`; no D5 open equation needed yet) |
| 488, 515 (`forallE_inv`, `sort_inv`) | `.2` projections; `forallE_whRed_l` keeps its untyped statement, so 495 and 498 needed no edit |

The statements of `LR.Adequate`, its lemmas, `LR.Adequate.mono_r`, `LR.adequacy` and the four
corollaries are `Expr`-equal to the originals (modulo the namespace).

## 4. Verification output (verbatim)

Part 1 (verifier a, tracer rooted at all 336 constants of the module):

```
axioms reached (3):
  Classical.choice
  Quot.sound
  propext
constants directly containing sorry (0):
```

Part 2:

```
== roots: [Lean4Lean.SExpr.T.LR.adequacy]
axioms reached (4):
  Classical.choice
  Quot.sound
  propext
  sorryAx
constants directly containing sorry (1):
  Lean4Lean.SExpr.T.LR.adequacy
== roots: [Lean4Lean.SExpr.T.forallE_inv, Lean4Lean.SExpr.T.sort_inv, Lean4Lean.SExpr.T.sort_forallE_inv]
axioms reached (4):
  Classical.choice
  Quot.sound
  propext
  sorryAx
constants directly containing sorry (1):
  Lean4Lean.SExpr.T.LR.adequacy
'Lean4Lean.SExpr.T.LR.Adequate.mono_r' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The verifiers also confirmed: the snapshot's `Lean4Lean/` outside `E1/` is byte-identical to
`3c35f59`; the only `variable` is `[Params]`; no `axiom`/`opaque`/`unsafe`/`implemented_by`/
`native_decide`/`set_option`; `TyRedS`/`TWHRedS`/`AmbSort` match D6 character for character; the
tower `T.LR` is built from `T.LR0`/`T.LRS`, not the repo's.

## 5. Deviations from PLAN D6

None in substance. The forced consequences are the five rows of the table in §1; the audit log
had predicted the `sort_a` split and the simp-lemma changes. No `SORRY(E1)` marker was needed.

## 6. What this means for R1+R2

R1 replaces `ShapeLogRel.lean:5272-6117` by `TypedLR.lean`'s body (drop its header and the
`T` namespace; the file uses no `T.`-qualified names). R2 replaces
`ShapeLogRelAdequacy.lean:8-515` by `TypedAdequacy.lean`'s body. Then: `lake build
Lean4Lean.Experimental` (all sixteen modules), the tracer's first block unchanged, and the
docs-pinning step (PLAN §2): experiments in `docs/const-case/` that redefine or depend on the
old untyped fields stop compiling and are marked historical.

## 7. How to rebuild

The two modules import each other as `Lean4Lean.Experimental.E1.TypedLR`, so they are not
checked by `../../check.sh`. To rebuild: copy both into `Lean4Lean/Experimental/E1/` of a
checkout at `3c35f59` (or `fb0edc2`), then

```sh
lake build Lean4Lean.Experimental.E1.TypedAdequacy
lake env lean docs/const-case/plan/E1/CheckLR.lean        # axioms + tracer, part 1
lake env lean docs/const-case/plan/E1/CheckAdequacy.lean  # tracer, part 2
```
