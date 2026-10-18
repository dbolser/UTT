# Design: the `const` case of `LR.adequacy` (angle C — port of the paper artifact's ℕ / Y treatment)

Snapshot: `/tmp/utt-snap1` (read-only). Gap: `Lean4Lean/Experimental/ShapeLogRelAdequacy.lean:148-154`.
Artifact: `/tmp/utt-ref/paper-artifacts/domain-semantics-lean-BEE7/DomainSemantics/` (read-only).
Scratch (typechecks against the snapshot): `/tmp/utt-exp/design-artifact/CtorClause.lean`.

## 0. Thesis

1. The artifact closes the analogous gap for ℕ by making `LRS.TmEq` at type-shape `nat` *non-trivial*: at element-shape `zero`/`succ m'` both terms head-reduce to the constructor, the `succ` argument is related at level `n` (`TmEqNat`), and the *type* head-reduces to `nat` (`LogRel.lean:811-890`, `961-972`).
2. lean4lean's `LRS.DefEq` is `True` at type-shape `indTy` and `LRS.TyDefEq` is `True` at `ctor`/`indTy` (`ShapeLogRel.lean:5431, 5612-5634`), so a term related at `(ctor c l, indTy)` is not known to be a constructor spine; this is obstacle (i).
3. The port replaces the `indTy` clause by `CtorDefEq`: `A ⤳* I-spine`, both sides `⤳* const c ls'` applied to spines `Xs`/`Ys`, and the spines related *in the `SubstWF` form* (`CtorArgsEq`): per field, the type congruence across the two instantiations plus `IH.DefEq` at every type shape of the field's declared (closed telescope) type that is valid under the telescope valuation built from `l`. This is the lean4lean analogue of `TmEqNat`, dependent-telescope-aware; the artifact's "`Γ ⊢ M' ≡ N' : nat` witness that symm/trans need" becomes the stored `Γ ⊢ X ≡ Y : T.subst σ` + type-congruence components (lean4lean's `symm`/`trans` fields take no witnesses, so the witnesses must live in the clause).
4. The `const` case becomes a *spine-generalised* lemma (`adequacy_const_spine`) proved by induction on `LE_Interp.Const` with the spine arguments as **bound variables of the constant's type telescope** (not instantiated `LamDefEq` arguments), so argument relatedness and type-shape validity flow from `SubstWF`/`Adequate.cons` exactly as in the `lamDF` case; leaves: `bot`, `indTy` (→ `TyDefEq` at `indTy`), `ctor` (→ hand over the `SubstWF` as `CtorArgsEq`), `pat` (→ substitute, use `CtorDefEq` on the ctor-position arguments to reduce them to syntactic spines, fire `WHRed.extra`, relate the RHS).
5. Obstacle (ii) (the rule RHS is not a subderivation) is solved with the `adequacy_Y` measure: `LE_Interp.const` carries `a7 : ∀ m e, R m e → LE_Interp ρ m e` as a *nested* premise, so `induction hM` yields an IH for every fixed-constant leaf of the RHS (`LE_Interp.RHS.const`); these are structurally smaller self-witnesses, exactly like `ih_self` in `adequacy_Y` (`Adequacy.lean:351-440`). Typing of the RHS is *not* a problem: the env already carries it (`VDefEq.WF`, `IsDefEqStrong.extra` has both sides' typing).
6. Two pieces of infrastructure are missing from the snapshot and must be added: (a) `WHRed.major` (reduce the argument of a partial pattern application) — present in `Theory/Typing/HeadReduction.lean:60` but dropped from `SExpr.WHRed` (`SExpr.lean:1011`); without it `rec … (f x)` with `f x ⤳* succ k` is stuck, so the ctor clause could not be established for defeq-but-not-syntactic constructor applications (the artifact has `WHRedS.natCase`, `Term.lean:1899`); (b) the schematic rule's *typed open RHS* or, equivalently, subject reduction for `WHRed.extra` on open spines (`WHRedS.defeq`, `SExpr.lean:1072`, currently `sorry`).
7. The residual research risk is not the measure but **type-shape reconciliation for non-canonical fields**: a parametric/function-typed constructor field is related (producer side) at type shapes valid under the *constructor* telescope valuation, but consumed (recursor rule) at a type shape valid under the *recursor* telescope valuation; `indTy` forgets the parameters' shapes, so the two valuations are not syntactically comparable. Section 7 states the exact lemma needed and the fallback restriction.
8. Struct-eta (`etaCtor`) and K-like rules are already outside the shape semantics (no `Const` leaf accepts an `etaCtor` head; `Pattern.WF` forces `.ctor` heads in patterns; `SimplePattern` has no var-only major premise), so they are excluded explicitly, not handled.

## 1. What is being ported (artifact → lean4lean)

| artifact (DomainSemantics) | lean4lean target |
|---|---|
| `LRS.TmEq` nat clause, `LogRel.lean:881-890` (`A ⤳* nat ∧ match m: bot/zero/succ`) | `LRS.DefEq` indTy clause, `ShapeLogRel.lean:5612-5634` (currently `.indTy => True`) → `CtorDefEq` |
| `LRS.TyEq` nat clause `LogRel.lean:553` (`M ⤳* nat ∧ N ⤳* nat`) | `LRS.TyDefEq` indTy clause `ShapeLogRel.lean:5431-5434` (currently `True`) → `IndTyRed ∧ IndTyRed` |
| `LogRel.TmEqNat` + `.left/.mono_l/.join/.symm/.trans` `LogRel.lean:811-852` | `LRS.CtorArgsEq` + `.left/.symm/.trans` (`CtorClause.lean`, proved), `.mono_l` (§4) |
| nat field re-proofs in `LRS` `LogRel.lean:1096-1560` (bot, left, symm, trans, trans', conv, mono_r_2, mono_r_2_ty, mono_r_1, mono_l, join, whr) | `LRS` fields `ShapeLogRel.lean:5657-5894` (§4) |
| `LR.adequacy_Y` `Adequacy.lean:351-440` (induction on `LE_Interp` derivation, `ih_self`) | `LR.adequacy_const_spine` (§5) — induction on `LE_Interp.Const` + nested `a7` IHs |
| `natCase_zero/succ` adequacy cases `Adequacy.lean:2298-2470` (constructor clause → syntactic head reduction → iota → branch IH via `Adequate.cons`) | pat leaf of `adequacy_const_spine` (§5.4) |
| typed `Γ ⊢ M ⤳* N : A` = `⟨Γ ⊢ M ≡ N : A, M ⤳* N⟩` (`LamDefEq.whr`, `LogRel.lean:783`) | untyped `WHRedS` (`SExpr.lean:1063`); keep untyped, but add `WHRed.major` |
| `WHRedS.natCase` `Term.lean:1899` | new `WHRed.major` (copy of `Theory/Typing/HeadReduction.lean:60`) |

Artifact facts checked: `LogRel` there has `symm`/`trans`/`whr` with `IsDefEq` witnesses and a `join` field (`LogRel.lean:55-84`); lean4lean's has neither (`ShapeLogRel.lean:5271-5291`). Hence the witnesses are stored in the clause (§2).

## 2. New clauses (Lean, typechecked in `CtorClause.lean`)

```lean
def spine (h : SExpr) (Xs : List SExpr) : SExpr := Xs.foldl .app h

def LRS.IndTyRed (Γ : List SExpr) (A : SExpr) : Prop :=
  ∃ (I : Name) (ls : List SLevel) (As : List SExpr),
    Params.classify I = some (.indTy As.length) ∧ Γ ⊢ A ⤳* spine (.const I ls) As

inductive LRS.CtorArgsEq (IH : LogRel Γ n) :
    List SExpr → List SExpr → List SExpr → List (WShape n) → Valuation → Subst → Subst → Prop
  | nil : CtorArgsEq IH [] [] [] [] ρ σ σ'
  | cons {T Ts X Xs Y Ys} {p : WShape n} {l ρ σ σ'} :
    (∃ u, Γ ⊢ T.subst σ ≡ T.subst σ' : .sort u) →
    (∀ a : WShape n, LE_Interp ρ a.T T → a.HasType .type → IH.TyDefEq (T.subst σ) (T.subst σ') a) →
    Γ ⊢ X ≡ Y : T.subst σ →
    (∀ a : WShape n, LE_Interp ρ a.T T → p.HasType a → IH.DefEq X Y (T.subst σ) p a) →
    CtorArgsEq IH Ts Xs Ys l (ρ.push p.T) (σ.cons X) (σ'.cons Y) →
    CtorArgsEq IH (T :: Ts) (X :: Xs) (Y :: Ys) (p :: l) ρ σ σ'

def LRS.CtorDefEq (IH : LogRel Γ n) (M N A : SExpr) (c : Name) (l : List (WShape n)) : Prop :=
  LRS.IndTyRed Γ A ∧
  ∃ (ls : List SLevel) (Xs Ys Ts : List SExpr) (B : SExpr),
    Γ ⊢ .const c ls : Ts.foldr .forallE B ∧
    Γ ⊢ M ⤳* spine (.const c ls) Xs ∧ Γ ⊢ N ⤳* spine (.const c ls) Ys ∧
    LRS.CtorArgsEq IH Ts Xs Ys l .nil .id .id
```

Modified `LRS.DefEq` (`ShapeLogRel.lean:5612`):
```lean
  | .indTy =>
    match hm : m.1 with
    | .bot => True
    | .ctor c l => LRS.CtorDefEq IH M N A c (l.pmap Subtype.mk (hm ▸ m.2).1)   -- l : List (WShape n) via WShape.mk_ctor
    | _ => False
```
Modified `LRS.TyDefEq` (`ShapeLogRel.lean:5431`): `| ⟨.indTy, _⟩ => LRS.IndTyRed Γ M ∧ LRS.IndTyRed Γ N`; `⟨.ctor _ _, _⟩` stays `True` (a type never has a ctor element-shape; `trans'` is killed by `IndTyRed Γ (sort u)` being absurd via `WHNF.sort.whRedS`, exactly as the artifact kills it with `A ⤳* nat`).

Design decisions and why:
* `IndTyRed Γ A` is in the *element* clause (not only in `TyDefEq`) because lean4lean's `bot` field has no `TyDefEq A A a` hypothesis (artifact's does), so `(bot, indTy)` must stay `True`, and `trans'` at `s = indTy, a = ctor` needs the absurdity from the first hypothesis.
* Single `ls` for both spines: determinism (`WHNF.ctorSpine`) forces it in `trans`; the producer always has it.
* `CtorArgsEq` is `SubstWF`-shaped (type congruence + term congruence + `Subst1`-form universal over valid type shapes). Reasons: (1) dependent telescope — `trans` needs the type congruence `TyDefEq (T.subst σ) (T.subst σ') a` to convert the second relatedness to the first instantiation (checked: `CtorArgsEq.trans` typechecks using `IH.conv (IH.symm_ty …)`); (2) the producer (ctor leaf, §5.3) literally has a `SubstWF` and `Subst1` provides exactly these components (`ShapeLogRel.lean:6061-6066`); (3) the consumer (pat leaf, §5.4) must rebuild a `SubstWF` for the rule RHS and `Adequate.cons` needs `hv : DefEq x x' (A.subst σ) p a₁` at a type shape `a₁` with `LE_Interp ρ a₁.T A` — the universal form lets the consumer choose `a₁` and discharge validity itself.
* Validity is relative to the *closed* constructor telescope `Ts` under the valuation `.nil` pushed with `l` (`Valuation.ofRargs`); constructor types are closed so no ambient valuation is needed. The spine order of `l` matches `Const.ctor`'s `ctor' c rargs.reverse` and `Matches.app`'s `ctor' c' rargs'.reverse`.
* `TyDefEq` at `indTy` records only existence of an inductive head on each side (no same-`I`, no argument relatedness); only `conv` needs it (transport `IndTyRed Γ A` to `B`). Inductive-type injectivity is *not* claimed by the relation.

## 3. Lift stability

`LR.DefEq.lift`/`LR.TyDefEq.lift` (`ShapeLogRel.lean:6046-6058`) go through `LR.lift_succ_aux` by cases on the shape; the new cases need `CtorArgsEq IH … l ρ … ↔ CtorArgsEq (LRS-lifted) … (l.map (.lift n')) …`: uses `IH2 : DefEq … (m.lift) (a.lift) ↔ DefEq … m a` with `p : a` (hypothesis of the `Subst1`-form), `IH1` for `TyDefEq` with `a : type`, and `LE_Interp.lift`/`TShape.lift_eqv` for the validity hypothesis under the lifted valuation (`Valuation.ofRargs (rargs.map lift)` is pointwise `TShape`-equivalent by `TShape.lift_eqv`). Mirrors `LRS.PiDefEq.lift_aux`.

## 4. The 19 `LogRel` fields (`ShapeLogRel.lean:5271-5291`) — re-proof notes

Mirror of the artifact's nat alternatives (`LogRel.lean:1096-1560`). Shape-level facts used: `Shape.HasTypeU.ctor : ctor c l : indTy`, `indTy : type` (`ShapeLogRel.lean:2518-2519`), `WShape.le_indTy : s ≤ indTy ↔ s = bot ∨ s = indTy`, `WShape.ctor_le` (`1274, 2179`), `HasType.ctor_isType : ¬ ctor : sort` (`2910`).

| field | new work |
|---|---|
| `sort_iff`, `sort_iff_ty` | unchanged (`.rfl`). |
| `bot` | `(bot, indTy)` is `True`; `TyDefEq _ _ bot` unchanged. |
| `toType` | `id` (sort clause unchanged). |
| `left`, `left_ty` | `CtorDefEq.left` (proved); `TyDefEq.left` at indTy: `⟨h.1, h.1⟩`. |
| `symm`, `symm_ty` | `CtorDefEq.symm` (proved: `IH.symm`, `IH.conv` with the stored type congruence, `IsDefEq.defeqDF`); `TyDefEq.symm` at indTy: swap. |
| `trans`, `trans_ty` | `CtorDefEq.trans` (proved modulo telescope uniqueness `Ts = Ts'`: the two Π-telescopes read off `ci.type` must coincide, to be pinned via `ctor_syn`; `WHNF.ctorSpine` and the spine injectivity `WHRedS.ctorSpine_determ` are now in SExpr.lean); `CtorArgsEq.trans` proved. |
| `trans'` | at `s = indTy, a = ctor`: first hypothesis has `IndTyRed Γ (sort u)`; `WHNF.sort.whRedS` gives `sort u = spine …`, `cases`. At `a = bot`: `True`. |
| `conv` | `(ctor, indTy)`: `TyDefEq A B indTy = IndTyRed A ∧ IndTyRed B` replaces the `IndTyRed A` component; the `∃` part is untouched (it mentions `A` only through `IndTyRed`). |
| `mono_r_2` | `a ≤ a' = indTy` ⇒ `a ∈ {bot, indTy}` (`le_indTy`); `bot`: `True`; `indTy`: `id`. |
| `mono_r_2_ty` | `a ≤ a' = indTy` ⇒ `a = bot` (`True`) or `a = indTy` (`id`). |
| `mono_r_1` | `a' = indTy`, `a ≤ indTy`: `a = bot` ⇒ `m = bot` (`ha.bot_r`) ⇒ `(bot, indTy)` `True`; `a = indTy` ⇒ `id`. |
| `mono_l` | `a = indTy`, `m ≤ m'`, both `: indTy`: `m' = bot` ⇒ `m = bot`; `m' = ctor c l'`, `m = bot` ⇒ `True`; `m = ctor c l` with `l ≤ l'` pointwise (`WShape.ctor_le`) ⇒ `CtorArgsEq.mono_l`: same `Xs Ys Ts`, each field by `IH.mono_l (lᵢ ≤ l'ᵢ) hp hp'` where `hp' : l'ᵢ : a` is obtained from `hp : lᵢ : a` **only if typing is upward-closed along `≤` at fixed `a`** — it is not in general; instead use the validity hypothesis: the clause for `l'` quantifies over `a` with `l'ᵢ : a`, so we need `lᵢ : a → l'ᵢ : a`. **Fix**: state `CtorArgsEq` with `p.HasType a` replaced by `∃ p', p ≤ p' ∧ p'.HasType a`? No — simplest is to weaken the consumer: in the clause quantify `∀ a, LE_Interp ρ a.T T → ∀ q ≤ p, q.HasType a → IH.DefEq X Y (T.subst σ) q a` (relatedness at all typed points below the recorded shape). Then `mono_l` is `q ≤ l ≤ l'` transitivity, no typing transport needed, and the producer gets it from `IH.mono_l` once (it has `DefEq` at `(p, a)` with `p : a` from `Subst1`). The valuation also changes (`ρ.push p.T` vs `ρ.push p'.T`): validity is monotone in the valuation (`LE_Interp.mono_l`, larger valuation), so the `l'` clause's validity hypothesis `LE_Interp (push l'…) a.T T` must be *implied* by the `l` clause's — wrong direction. **Therefore the valuation in `CtorArgsEq` must be fixed independently of `l`**: use `ρ` as an explicit ∃-stored valuation in `CtorDefEq` (`∃ ρ, (∀ i, lᵢ.T ≤ ρ-entry i) ∧ CtorArgsEq … ρ`) — `mono_l` keeps `ρ`. This is the same move the artifact needs nowhere (ℕ has no telescope); it is cheap and I recommend it. (Not yet reflected in `CtorClause.lean`, which fixes `ρ := ofRargs l`.) |
| `join_ty` | at `m₁ = m₂ = indTy`: `indTy ⊔ indTy = indTy`, both `IndTyRed` pairs equal; `ctor`/`bot` cases `trivial`/`rwa`. |
| `whr` | `(ctor, indTy)`: `M ⤳* M'`: `hM.determ_l r (WHNF.ctorSpine …)` forward, `.trans` backward — exactly the `sort`/`forallE` pattern at `ShapeLogRel.lean:5860-5870`; `IndTyRed` untouched (it is about `A`). |
| `whr_ty` | indTy: same with `IndTyRed`'s reduction, needs `WHNF.indTySpine` (no rule has an `indTy` head: `pat_arity`). |

The artifact's extra fields `join`/`isType`/`bot_ty` do not exist in lean4lean and are not needed: `CtorDefEq` never requires joining two relatednesses (the Y/natCase consumer in the artifact uses `Adequate.mono_r`, whose lean4lean counterpart is the `toValTy`/`mono_r_*` dance already present in the `appDF` case).

## 5. The spine-generalised `const` lemma

Statement (typechecks, `CtorClause.lean:93-114`): for `Const c ls R rargs m` with `rargs` the shapes of the first `k = Ts.length` arguments (reversed), the open spine `const c ls (bvar (k-1)) … (bvar 0)` is `Adequate` in context `Ts.reverse ++ Γ₀` under valuation `Valuation.ofRargs rargs` at every `(m', a)` with `m ≤ m'.T`, `LE_Interp … a.T B`, `m' : a`; hypotheses: `hR : ∀ m e, R m e → LE_Interp … m e` and the **self-witness IH** `ihR : ∀ m e, R m e → … → Adequate Γ₀ Γ₀ .nil e e A m' a'` (every fixed-constant leaf of a rule RHS is adequate at its recorded shape). The `const` case of `LR.adequacy` instantiates it with `k = 0`, `Γ = Γ₀` (after the existing closedness rewrite), and `ihR` from `induction hM` (§6).

Induction on `hC : Const c ls R rargs m`, generalising `Ts B m' a n'` (and the context):

5.1 `bot`: `m = bot ⇒ m' = bot` (`TShape.le_bot`), `Adequate.bot hmem.isType`.

5.2 `lam (hf : ∀ (x,y) ∈ f, Const (x::rargs) y.T) (hle : m ≤ lam' f)`: `hmem` forces `a = forallE a₁ a₂` (other type shapes: `TShape.*_not_le_lam'` as in the existing `lamDF` case) and `B ⤳* …` is not needed because `B` is literally `forallE T B'` with `Ts = T :: Ts'`? No: unfold one binder: `hT : … ≡ (T::Ts').foldr forallE B'` so `B = forallE T B'`. Goal is `DefEq (openSpine k) (openSpine k) (forallE T B') (lam' f'') (forallE a₁ a₂)` (after `subst σ`). By `LRS.DefEq.lam_forallE` we must give `A₁ A₂ u v`, `forallE T B' ⤳* forallE A₁ A₂` (`.rfl`), `TyDefEq A₁ A₁ a₁` (from `hA.forallE_inv.1` + `toValTy` + adequacy of `T` — `T` is an environment type; see §6 for where its adequacy comes from), `PiDefEq` (as in `lamDF`, via `Adequate.cons` on `B'`), and `LamDefEq`: `∀ X Y p, p : a₁ → Γ₀ ⊢ X ≡ Y : A₁ → DefEq X Y A₁ p a₁ → DefEq ((spine k).app X) … (B'.inst X) (f''.app p) (a₂.app p)`. Use `WShape.HasDom.iff.1 (HasTypeLam …).2.1 p` to lower `p` to a **typed graph point** `x ≤ p`, `x : a₁`, `f''.app p ≤ f''.app x = y` (this is the step that makes the typed logrel follow the untyped shape semantics; it is exactly `ShapeLogRelAdequacy.lean:200-203`); `IH.mono_l` moves the goal to `(y, a₂.app x)`; then `Adequate.cons` extends the `SubstWF` with `(X, Y, x, a₁)` and the IH `hf x y` at `rargs' = x :: rargs`, `Ts'`, `B'`, valuation `ofRargs (x :: rargs) = (ofRargs rargs).push x.T` gives `Adequate` of `openSpine (k+1)` in `T :: …`; `openSpine (k+1) = (openSpine k).lift.app (bvar 0)` so `subst (σ.cons X)` yields `(spine k).subst σ .app X` up to `lift_subst_cons`. The three `Adequate` components are obtained as in `lamDF`'s three `all_goals` bullets.

5.3 `ctor (hcl : classify c = ctor rargs.length) (hle : m ≤ ctor' c rargs.reverse)`: `hmem` forces `a = indTy` (ctor shapes have only type `indTy`; `bot` handled by `TShape.le_bot`). Goal: `CtorDefEq (LR Γ₀) (spine.subst σ) (spine.subst σ') (B.subst σ) c rargs.reverse` for every `SubstWF Γ₀ σ σ' (Ts.reverse ++ Γ₀) ρ`. Components: `IndTyRed Γ₀ (B.subst σ)` — `B` is the constructor's result type `I args` (`Params.ctor_ty` / `CtorBundle.rhs`, `SExpr.lean:638,698`), so `.rfl` with `hclI`; `ls := ls`, `Xs := σ-images of the bvars`, `Ys := σ'-images`, `Ts := Ts`, `B`; reductions `.rfl`; `CtorArgsEq`: walk the `SubstWF` (`SubstWF.cons` gives, per entry, `Γ ⊢ A : sort u`, `LE_Interp ρ a A`, `x : a`, and `Subst1 Γ₀ σ.head σ'.head A.lift (A.subst σ.tail) (A.subst σ'.tail) (ρ.push x)` = `Γ₀ ⊢ x ≡ x' : A.subst σ.tail ∧ ∀ a, LE_Interp ρ a.T A.lift → (a : type → (∃u, A.subst σ ≡ A.subst σ' : sort u) ∧ TyDefEq …) ∧ ∀ m, LE_Interp ρ m.T (bvar 0) → m : a → DefEq x x' (A.subst σ.tail) m a`) — these are literally the four `cons` premises of `CtorArgsEq` (with `LE_Interp ρ m.T (bvar 0) ↔ m.T ≤ ρ 0 = p.T` by `LE_Interp.bvar_iff`, and the `q ≤ p` form of §4/`mono_l`). The `SubstWF` is over `Ts.reverse ++ Γ₀`; the `Γ₀` suffix is `SubstWF.id`-like only when the outer call is at `Γ = Γ₀` — in the `const` case it is (`Adequate` is used with `W : SubstWF Γ₀ σ σ' Γ ρ` and the closedness rewrite removes `σ` from the type; for the open spine the suffix substitution acts on `Γ₀`'s own variables and must be the identity-shaped part of `W`; take `Ts.reverse ++ Γ` with the ambient `W` as base).
   For `etaCtor` heads this leaf cannot occur (`Const.ctor` requires `.ctor`); such constants only have `bot` leaves, hence `lam' f = bot`, hence `m = bot` (§8).

5.4 `indTy (hcl) (hle : m ≤ indTy)`: `hmem` forces `a = sort true` (`indTy : type`); goal `DefEq … (sort u) indTy (sort r) = TyDefEq (spine.subst σ) (spine.subst σ') indTy = IndTyRed ∧ IndTyRed`: both `.rfl` with `hcl` (`rargs.length` matches by `hk`).

5.5 `pat (hP : Pat p r) (hM : Matches p c rargs mp) (hRHS : RHS ls mp R m r.1)`: by `pat_simple`, `p = .const c` (defn, `rargs = []`) or `p = .app (varN (const c) j) (varN (const c') i)` (iota: `rargs = [ctor' c' rargs', x_j, …, x_1]` with `Matches.app` giving the ctor-position argument the shape `ctor' c' rargs'.reverse` and `Matches.var` giving `mp (some^… none) = xᵢ.T`).
   Step 1 (substitute): fix `W : SubstWF Γ₀ σ σ' (Ts.reverse ++ Γ) ρ`; the goal is `DefEq ((spine k).subst σ) ((spine k).subst σ') (B.subst σ) m' a` (three variants, as always). `(spine k).subst σ = spine (const c ls) [σ(k-1), …, σ(0)]`.
   Step 2 (reduce the major to a syntactic constructor spine): for iota, the ctor-position variable `bvar 0`'s entry in `W` has shape `p_maj = ctor' c' rargs'.reverse`, declared type `I params` (shape `indTy`, valid: `LE_Interp ρ indTy.T (I params)` from `Const.indTy` of the type's own `LE_Interp`), so `Subst1` gives `DefEq (σ 0) (σ' 0) (I params…) p_maj indTy`, i.e. `CtorDefEq`: `σ 0 ⤳* spine (const c' ls') Zs`, `σ' 0 ⤳* spine (const c' ls') Zs'`, `CtorArgsEq … Zs Zs' rargs' …`. Then **`WHRed.major`** (new; `IsMajorPremise (spine (const c ls) [σ(k-1)…σ(1)])` holds because `varN (const c) j` matches that prefix) lifts `σ 0 ⤳* c' Zs` to `spine … σ0 ⤳* spine … (c' Zs)`; `(LR Γ₀).whr` moves the goal to the reduced spines.
   Step 3 (fire the rule): `MatchesS p (reduced spine) ls m2` is syntactic (`MatchesS.app (MatchesS.var^j .const) (MatchesS.var^i .const)`) with `m2 (inl path) = σ(…)`, `m2 (inr path) = Zs[…]`. `WHRed.extra hP hMatchesS (dfs := [])` needs `[].map = r.2.defeqsS ls m2`, i.e. `r.2 = .true` — **assumption `pat_check : Pat p r → r.2 = .true`** (§8). `(LR Γ₀).whr` again moves the goal to `r.1.applyS ls m2` vs `r.1.applyS ls m2'`.
   Step 4 (relate the RHS): `hRHS : RHS ls mp R m r.1` is a tree over `fixed`/`var`/`app`. Two routes:
   * **R2 (recommended, = artifact's natCase route)**: `Pattern.RHS` has no binders, so `r.1.applyS ls m2 = R̂.subst (σ_m2)` for the open term `R̂ := r.1` with each `var path` read as a bvar of a *pattern context* `Γ_p` (one entry per path, types = the rule's declared types; `fixed e` stays `e.instL ls`). Build `SubstWF Γ₀ σ_m2 σ_m2' Γ_p ρ_p` by `Adequate.cons`, feeding for each path the relatedness obtained in Step 2 (`CtorArgsEq` entries for `inr` paths, `Subst1` entries of `W` for `inl` paths) at a type shape valid for `Γ_p`'s declared type under `ρ_p` (§7). Then `Adequate Γ₀ Γ_p ρ_p R̂ R̂ T_p m a` is needed, i.e. the typed open RHS must be adequate — provided by (§6) the self-witness IH `ihR` for every `fixed` leaf plus congruence for `app` nodes (the `appDF` case of `LR.adequacy` is exactly `app` congruence; replaying it needs `IsDefEqStrong` of `R̂` in `Γ_p`, which is what the new `Params` field `pat_rhs_typed` must provide, §6).
   * R1 (fallback): induct on `hRHS` directly: `bot` → `(LR _).bot`; `const h` → `ihR _ _ h`; `var` → the stored relatedness (Step 2); `app hf ha hle` → `appDF`-style congruence using `LE_Interp.sound`/`InterpTyped` on the typing of the instance (`WHRedS.defeq` + `WHRedS.inferType`, `SExpr.lean:1072,1234`) to get typed shapes, then `HasDom.iff` lowering as in `appDF`. R1 needs no pattern context but redoes `appDF` by hand at each node.
   For defn (`p = const c`, `r.1 = fixed v`): Steps 2–3 are empty; Step 4 is `ihR m (v.instL ls) h` at `(m', a)` directly, then `whr` with `WHRed.extra hP .const`.

## 6. Where RHS typing/adequacy comes from; the measure

* Typing of a rule's two sides is in the env: `Ordered.defeq … df.WF env` with `VDefEq.WF = HasType [] lhs type ∧ HasType [] rhs type` (`Theory/Typing/Basic.lean:75`, `Lemmas.lean:253-258`); `IsDefEqStrong.extra` (`SExpr.lean:671-675`) carries both typings and the `extra` case of `LR.adequacy` already uses the RHS IH. For a *defn* rule the RHS `value` is typed in the env *before* `c` (`VDecl.WF.def`, `Env.lean:22-26`), for iota in Lean's real env the RHS mentions `rec` itself; `addInduct` is `sorry` (`Theory/Inductive.lean:7`) and rules reach the semantics only through the abstract `Params.Pat`/`extra_pat` (`SExpr.lean:614`), which exposes *closed instances* (`MatchesS (lhs.instL ls)`), not the schematic typed RHS. So a new `Params` field is needed for R2:
  `pat_rhs_typed : Pat p r → ∃ Γ_p T_p, (∀ ls m2, Γ ⊢ (lhs-instance) : (T_p.subst …) → IsDefEqStrong (Γ_p-instance) R̂ R̂ T_p) …` (its exact form is an implementation detail: it must give a typing derivation of the open RHS whose `const` leaves are the rule's fixed constants). Alternative with no new field: R1 + `WHRedS.defeq`/`inferType` (already sorried lemmas, presumably provable from `extra_pat` + substitution for closed instances only — *not* for open spines; hence R1 silently depends on the same missing schematic typing). **Recommendation: add the field; it is the honest statement of "rules are schematic".**
* **Measure.** Mirror `adequacy_Y`: in the `const` case do `induction hM` (the `LE_Interp ρ m.T (const c ls)` derivation) *before* anything else; the `const` constructor's premise `a7 : ∀ m e, R m e → LE_Interp ρ m e` is a nested inductive occurrence, so the IH is `∀ m e (h : R m e), motive (a7 m e h)` — one `Adequate` per fixed-constant leaf of every rule instance reachable through `Const.pat`/`RHS.const`. These derivations are structural sub-derivations of `hM`, so recursion is well-founded even for recursive (iota) rules where the RHS mentions `rec`: the recursive occurrence is a `fixed (const rec)` leaf whose witness is the sub-derivation `a7 _ _ h`, exactly `ih_self` in `adequacy_Y`. No env-ordered outer induction (`Ordered.strong`-style) is needed, because the measure is the *semantic* derivation, not the environment; env ordering would in any case fail for iota (self-reference) and is only sound for defn rules.
  The IH must be stated with `Adequate` over `Γ₀` (closed constants, valuation `.nil`): fixed leaves are closed terms (`RHS.Closed`, `SExpr.lean:523-532`), so their adequacy is context-independent; the `ihR` hypothesis of `adequacy_const_spine` has this shape.
  The outer `LR.adequacy` induction on `H` is unchanged: `adequacy_const_spine` is invoked at the `const` case with `ih3`/`ih5` only for the typing of the constant's own type (`TyDefEq A₁ A₁ a₁` in 5.2) — these ARE subderivations (`IsDefEqStrong.const` premises `Γ ⊢ type : sort u` and `∀ cl, type ≡ (F cl).rhs ls`), which is why `IsDefEqStrong.const` was given them. Open question: `T` (a binder type of the constant's type) needs `Adequate` for `TyDefEq A₁ A₁ a₁`; it is reachable from `ih3` by `forallE_inv`-style decomposition of `Adequate` at Π-types (the `lamDF` case does this through `ihA`), i.e. `Adequate` of `Π Ts, B` at `(forallE a₁ a₂, sort)` yields `TyDefEq` of `T` at `a₁` via `LRS.ValTyPi2`.

## 7. Type-shape reconciliation (the real residual risk)

Producer side (5.3) relates field `i` at all type shapes `a` with `LE_Interp ρ_c a.T Tsᵢ`, `ρ_c` the **constructor** telescope valuation (params ↦ shapes of the ctor spine's own parameter arguments `l_P'`, earlier fields ↦ their shapes). Consumer side (5.4/R2) must supply, for the minor premise `s : Π (a : α) …` of the recursor, a domain shape `a₁` with `LE_Interp ρ_k a₁.T α`, `ρ_k` the **recursor** telescope valuation (params ↦ the rec spine's graph-point shape `q`), i.e. `a₁.T ≤ q`; and it needs `DefEq (field) … p'' a₁` for the `HasDom`-lowered field shape `p'' ≤ p`, `p'' : a₁`. The clause gives it only when `a₁.T ≤ l_P'`. `q` and `l_P'` are two independent lower bounds of the shape of `P ≡ P'`; `indTy` has forgotten both, and the LogRel cannot prove `P ≡ P'` (that is inductive-family injectivity, downstream of this very theorem).
   * Canonical cases work: recursive fields (`p'' : indTy`, `a₁ = indTy` on both sides), sort-typed fields (`type`), Π-typed *type*-shaped fields (`DefEq` at `sort r` ignores `r`), and `p'' = bot` (then `DefEq … bot a₁` is `True` — note the `HasDom` lowering makes `p'' = bot` whenever `q` and `l_P'` are incompatible, so the mismatch only bites for *compatible but incomparable* shapes).
   * Lemma needed for the general case (not proved, stated as the key risk): **(TypedMeet)** for `p : a₀` and `p : a₁` with `a₀`, `a₁` type shapes of the same term under two valuations that are both below the term's semantic shape, there is `p'' ≤ p` and `a₂ ≤ a₀, a₂ ≤ a₁` with `p'' : a₂` and `f.app p ≤ f.app p''` for every `f` typed at `a₁`. Then `IH.mono_r_2` (down to `a₂`) + `IH.mono_r_1` (up to `a₁`, using `Subst1`'s `TyDefEq` at `a₁`) + `IH.mono_l` closes the gap. Shapes are a conditional semilattice with joins (`TShape.join`, `Compat`), so the meet-like `a₂` must come from `HasDom`-style lowering, not from a general meet.
   * Fallback (sound, smaller scope): restrict `Params` to inductives whose constructors have only canonically-shaped fields (recursive/indTy-typed, sort-typed) — covers ℕ, Bool, lists of ground data, `Eq` at indTy-typed carriers, excludes `List α` with function-shaped elements and `Acc`/W-types. This is a strict superset of what the artifact proves.
   * Alternative (invasive): make `Shape.indTy` carry the parameters' type shapes (as the artifact's `id A a b` carries `aA`). Rejected for cost (`Shape` is used in ~6000 lines).

## 8. Exclusions (explicit, justified)

* **Struct eta / `etaCtor`**: `Const.ctor` requires `classify c = some (.ctor _)` (`ShapeLogRel.lean:3327`), `Pattern.WF` requires `.ctor` heads for pattern arguments (`SExpr.lean:17-22`), so an `etaCtor` constant has only `bot` leaves, every `lam'` tower collapses (`Shape.lam'`, `ShapeLogRel.lean:812`), and `LE_Interp ρ m (const c ls)` forces `m = bot`; the `const` case returns `Adequate.bot`. `IsStruct`/`ctor'` collapse (`815-818, 977`) is therefore inert for adequacy. Projections/eta on structures are not rules of this `Params` (they would violate `pat_wf`).
* **K-like rules**: `SimplePattern` (`Pattern.lean:226`) has only `defn` and `iota` (constructor-headed major), so K-like rules (major is a var + `Check`) are excluded by `pat_simple`. The `Check` component is still unconstrained; Step 3 needs `r.2 = .true`. Add `pat_check : Pat p r → r.2 = .true` to `Params` (or derive it if `Pat` is later refined). Justification: shape relatedness cannot witness the syntactic defeqs a K-check demands.
* **Prop-valued inductives**: `indTy : sort r` only for `r = true` (`Shape.HasTypeU.indTy`), proofs are `bot` (`proofIrrel` case + `TShape.HasType.proofIrrel`), so `(ctor, indTy)` at a Prop-typed term never arises with `m ≠ bot`: nothing to do. Large elimination from Prop (subsingleton elimination) is a *rule* like any other and is covered by iota if present in `Pat`.
* **Universe levels**: single `ls` per clause; `SLevel` is semantically quotiented, so no level-defeq congruence is needed.

## 9. Required changes, in dependency order

1. `SExpr.WHRed`: add `major : IsMajorPremise f → Γ ⊢ a ⤳ a' → Γ ⊢ .app f a ⤳ .app f a'` (port `IsMajorPremise` from `Theory/Typing/HeadReduction.lean:43`), extend `WHRed.determ` (new `major/app` and `major/extra` cases use `WHNF` of partial pattern applications, `HeadReduction.lean:140`), `WHRedS.major`.
2. `WHNF.ctorSpine`, `WHNF.indTySpine`, `spine` injectivity.
3. `Params.pat_check`; `Params.pat_rhs_typed` (R2) — or accept R1 with `WHRedS.defeq`/`inferType` for open spines.
4. `LRS.IndTyRed`, `LRS.CtorArgsEq` (with explicit ∃-valuation, §4 `mono_l`), `LRS.CtorDefEq`; replace the two `True` clauses; re-prove the fields (§4); extend `LR.lift_succ_aux` (§3).
5. `LR.adequacy_const_spine` (§5); wire the `const` case: `induction hM` first (measure), then the lemma at `k = 0`.
6. (TypedMeet) lemma or the §7 fallback restriction.
