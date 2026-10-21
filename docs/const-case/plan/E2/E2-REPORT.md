# Experiment E2 (the stage-1a constructor clause): PASS

2026-10-19. Plan: `../../PLAN.md` §1 D1 ("Stage 1a") and D2, §2 rows E2 and R3.
Base: commit `dc61a99` (typed reductions landed; the `LogRel` block is `ShapeLogRel.lean:5280-6216`).
Run: two independent Opus attempts, each checked by an independent adversarial verifier
(clean rebuild, grep for cheats, axioms, tracer, statement comparison). Verdicts: both pass.

## 0. Outcome

**D1 and D2 wire in with no sorry.** `CtorLR.lean` is the typed `LogRel` block with the
stage-1a clause at `(ctor c l, indTy)` and the D2 formula at `indTy`:

- all 19 fields of the `LRS` instance are proved at the new cases (`trans` through
  `WHRedS.ctorSpine_determ` and the injectivity of the Π-telescope; `trans'` through
  `CtorDefEq.not_sort`; `conv` and `whr` through `CtorDefEq.conv`/`.whr`; `mono_l` through
  `WShape.ctor_le` and `CtorDefEq.mono_l`; `mono_r_*` through `indTy_le`/`le_indTy`);
- `LRS.TyDefEq.left/symm/trans/whr` get an `indTy` case (determinism via `WHNF.indTySpine`);
- `LR.lift_succ_aux` gets the `(ctor, indTy)` case from `CtorDefEq.lift_aux` (both directions);
- `LR.DefEq.lift`, `LR.TyDefEq.lift`, `Subst1`, `SubstWF` keep their statements.

`CtorAdequacy.lean` (the adequacy lemma and its corollaries over the new relation) is
**byte-identical** to `ShapeLogRelAdequacy.lean:8-562`: no case of `LR.adequacy` needed an edit.
The `(⊥, indTy) = trivial` site in `lamDF` still closes because the new row's `.bot => True` arm
reduces. The const case stays the only sorry.

The field plumbing D1 had marked `[A]` works as written: `l.pmap Subtype.mk (hm ▸ m.2).1`
turns the raw field list of a well-formed `ctor c l` shape into a list of `WShape n`, and
`LRS.DefEq.ctor_indTy` turns it back into the list that `WShape.casesOn'`/`HasTypeU.ctor`
produce. `WHRedS.defeq` (subject reduction) is not used.

## 1. The definitions as implemented (`CtorLR.lean:186-213`)

```lean
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

Wiring. `LRS.DefEq … .indTy` is `match hm : m.1 with | .bot => True | .ctor c l =>
LRS.CtorDefEq IH M N A c (l.pmap Subtype.mk (hm ▸ m.2).1) | _ => False`.
`LRS.TyDefEq … ⟨.indTy, _⟩` is `∃ I ls, Params.classify I = some (.indTy 0) ∧
TyRedS Γ M (.const I ls) ∧ TyRedS Γ N (.const I ls)`; `⟨.ctor _ _, _⟩` stays `True`.
The clause lemmas are those of `historical/CtorClause1a.lean` (synthesizer, proven over an
abstract `IH`), renamed `LRS.CtorDefEq.*`, `LRS.FieldRel.*`, `LRS.FieldsEq.*`, with the
section variables replaced by explicit `{IH : LogRel Γ n}` binders.

Statements that changed besides the two definitions (both attempts, independently):

| declaration | original | now |
|---|---|---|
| `LRS.TyDefEq.indTy_m` (`rfl`, `↔ True`) | `TyDefEq IH M N .indTy ↔ True` | `↔` the D2 formula (still `rfl`) |
| `LRS.DefEq.indTy_a` (`rfl`, `↔ True`) | `DefEq IH M N A m .indTy ↔ True` | split: `@[simp] bot_indTy : DefEq IH M N A .bot .indTy = True := rfl`; `@[simp] ctor_indTy : DefEq IH M N A (ctor' c l h) .indTy ↔ CtorDefEq IH M N A c l`; `indTy_a (h1 : m ≠ .bot) (h2 : ∀ c l h, m ≠ .ctor c l h) : … ↔ False`, no longer simp |
| the five uses of those simp lemmas (instance fields `mono_r_2`, `mono_r_2_ty`, `mono_r_1`, `mono_l`, and `lift_succ_aux`) | one-line `simp` | case split on the element shape (`⊥` / `ctor`) |

Everything else in the block keeps its statement. Attempt a's `Compare.lean` and attempt b's
check both confirm the four D6 fields and `bot`/`conv`/`mono_l` have the repo's signatures.

## 2. Verification output (verbatim, attempt a)

```
'Lean4Lean.SExpr.T.LRS' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lean4Lean.SExpr.T.LR' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lean4Lean.SExpr.T.LR.DefEq.lift' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lean4Lean.SExpr.T.LR.TyDefEq.lift' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lean4Lean.SExpr.T.LR.Adequate.mono_r' depends on axioms: [propext, Classical.choice, Quot.sound]
== roots: [Lean4Lean.SExpr.T.LR.DefEq.lift, Lean4Lean.SExpr.T.LR.TyDefEq.lift, Lean4Lean.SExpr.T.LR, Lean4Lean.SExpr.T.LR.SubstWF.id]
axioms reached (3):
  Classical.choice
  Quot.sound
  propext
constants directly containing sorry (0):
== roots: [Lean4Lean.SExpr.T.LR.adequacy]
axioms reached (4):
  Classical.choice
  Quot.sound
  propext
  sorryAx
constants directly containing sorry (1):
  Lean4Lean.SExpr.T.LR.adequacy
```

The verifier rebuilt both modules from clean, found the only `sorry` at the const case
(`CtorAdequacy.lean:196`, the copy of `ShapeLogRelAdequacy.lean:198`), no
axiom/opaque/unsafe/implemented_by/native_decide/set_option, `[Params]` the only `variable`,
the definitions character-for-character D1/D2, and the snapshot's `Lean4Lean/` outside `E2/`
byte-identical to `dc61a99`.

## 3. What this means for R3

R3 replaces `ShapeLogRel.lean:5280-6216` by `CtorLR.lean`'s body (drop the four header lines
and the `T` namespace; the file uses no `T.`-qualified names). `ShapeLogRelAdequacy.lean` is
unchanged. The docs experiments that used `indTy = True` (`Stuck.lean`, `Subst1.lean`'s
`LR.trivial_at_indTy`, `CtorClause.lean`'s own `LRS.CtorDefEq`, and others) stop compiling and
are marked historical.

## 4. How to rebuild

Copy `CtorLR.lean` and `CtorAdequacy.lean` into `Lean4Lean/Experimental/E2/` of a checkout at
`dc61a99`, then `lake build Lean4Lean.Experimental.E2.CtorAdequacy` and
`lake env lean docs/const-case/plan/E2/Check.lean`.
