# Design "ctor-clause": constructor-value clauses for the const case

> **Status (2026-10-19).** Design A, the third analysis, written 2026-10-18 against an earlier
> snapshot (`/tmp/utt-snap1`) and kept verbatim. The five-lens review and the synthesizer
> (`PLAN.md` §0.6, §0.9, §0.14) found these corrections: (1) the code `k : Shape n` on
> `ctor c l k` is ill-typed as written; it must be the two level-(n+1) components
> `(a₁ : Shape n, f : ShapeFun n)`, the same data as `forallE` (`ClauseA.lean` does this).
> (2) The rank axioms of §6 (`rank_pat`) are inconsistent for mutual inductives, whose recursors
> occur in each other's rules; the plan uses `rank ≤` with one rank per block (`PLAN.md` D4).
> (3) The new `trans'` premise of §3 is unnecessary: a typed, level-free ambient conjunct in the
> clause makes `trans'` vacuous (`PLAN.md` D1, `not_sort`). (4) §7 calls quotients covered; they
> are excluded by `ctor_sort` (`Quot.mk.{0}` is Prop-valued). (5) `Exp2_Spine.lean` no longer
> typechecks at HEAD; `ClauseA.lean` supersedes it. What survives: codes as finite data on the
> constructor element (the plan's stage 1b), and the rank well-founded measure.


Scratch: `/tmp/utt-exp/design-ctor-clause/` (Exp1_Measure.lean, Exp2_Spine.lean both typecheck
against /tmp/utt-snap1; Exp2 is sorry-free).

## 0. Thesis (short)

Follow paper §3.4/3.5: terms related at `(m = ctor c l, a = indTy)` must head-reduce to `c`
applied to a spine whose fields are LR-related. The obstruction specific to this codebase is
that `ctor c l` records field *term*-shapes but no field *type*-shapes, and `indTy` is bare, so
the field relatedness `IH.DefEq xᵢ yᵢ Tᵢ lᵢ ?t` has no type-shape to live at. Quantifying `?t`
universally is not level-invariant (`LR.DefEq.lift` ⇐ fails), choosing it existentially breaks
`trans`/`mono_l`. The fix is the paper's own trick for Σ/Id: the **type code must carry the
field codes**. Cheapest placement here: the ctor *term*-shape carries a Π-code `k` of the
constructor's declared type, `ctor c l k`, and `hasType (ctor c l k) indTy` checks the fields
along `k`. The LR clause then relates fields point-wise along `k` (`SpineDefEq`, Exp2), which is
closed under conv/symm/trans/mono/lift because codes are finite data (same mechanism as
`LamDefEq`). The pat leaf becomes: shape-level `Matches` ⇒ major arg has ctor shape ⇒ clause
gives a syntactic ctor spine ⇒ new `WHRed.major` congruence + `WHRed.extra` fire ⇒ the RHS
instance is obtained by running adequacy on a **generic** typing of the rule RHS (Params-supplied,
with the recursive occurrence of `c` abstracted as a variable) under a `SubstWF` built from the
spine hypotheses, the ctor clause, and the structural IH on the shape derivation. Measure:
WF on the environment rank of the head constant (outer), structural on the `LE_Interp`
derivation of the constant through the `R`-closure (inner), structural on `Const` (innermost).

## 1. Why the naive clause fails (adversarial part)

Naive clause: `DefEq M N A (ctor c l) indTy := M ⤳* c x⃗ ∧ N ⤳* c y⃗ ∧ ∀ i, IH.DefEq xᵢ yᵢ (Tsᵢ[x⃗<i]) lᵢ tᵢ`.
What is `tᵢ`?

* `∀ tᵢ` with `LE_Interp (fieldsVal l⃗<i) tᵢ Tsᵢ ∧ lᵢ : tᵢ` (the `LR.Subst1` shape):
  `mono_l` is fine only if restated as `∀ m ≤ lᵢ`, but then `LR.lift_succ_aux` ⇐ fails: a
  level-`n+1` shape below `lift lᵢ` need not be a lift (contravariant step-function inputs), and
  a level-`n+1` type-shape `t` of `Tsᵢ` need not be below any lift (`plift.2` may be `none`,
  e.g. for `(α : Type) → α → α`). Retyping to a lift needs `TyDefEq` at the join, which is the
  thing being lifted. Dead.
* `∃ tᵢ`: `trans` needs a common `tᵢ` (join needs compat, which the LR cannot see without `ρ`);
  `mono_l` fails because `LogRel.mono_l` has no field-typing hypothesis: `ctor c [⊥, lam g] ≤
  ctor c [forallE.., lam g]` has the bigger side typed and the smaller side untypable
  (`Tsᵢ = bvar 0`). `Shape.hasType (ctor _ _) indTy = true` ignores fields.
* canonical `tᵢ` (top of the ideal): exists for fields whose type is not a Π whose codomain
  shape depends on a sort-typed binder; fails for `Monad`-like polymorphic fields.

Conclusion: the field type-shapes must be **part of the shape data**. Two placements:
(κ) `indTy K` with `K : Name → Shape` (per-ctor Π-codes) – touches every `indTy` site;
(λ) `ctor c l k` with `k : Shape n` a Π-code of `c`'s type – touches only `ctor` sites.
I design for (λ); (κ) is the same design with the code moved to the type side.

## 2. Shape algebra change (λ)

`ShapeS.ctor : Name → List Shape → Shape → ShapeS Shape` (third arg = code `k` of the ctor's
type, same level as the fields; its components are one level lower and are lifted where needed).

* `Shape.WF (.ctor c l k)` := fields WF ∧ `k.WF` ∧ (IsStruct c → ListNonZero l)  (IsStruct is dead
  under `Params.no_etaCtor`, §6).
* `LE`: `ctor c l k ≤ ctor c l' k'` iff `l ≤ l'` pointwise ∧ `k ≤ k'` (covariant code).
* `Compat/join/lift/plift/olift/trim`: pointwise on `(l, k)`.
* `hasType (.ctor c l k) .indTy := SpineTyped l k` where
  `SpineTyped [] _ = true`, `SpineTyped (x::l) (.forallE a f) = hasType x (lift a) && SpineTyped l (lift (f.app x))`,
  `SpineTyped (_::_) _ = false`  (a `⊥` code types only the empty spine; non-trivial fields force a Π-code).
  `hasType (.ctor ..) _ = false` otherwise (unchanged).
* `HasTypeU.ctor` gains the premise; `WShape.ctor'` keeps the IsStruct collapse syntactically.
* `LE_Interp.Const.ctor : classify c = some (.ctor rargs.length) → R k.T ((mk ci.type).instL ls) →
  m ≤ (ctor' c rargs.reverse k).T → Const rargs m`  (the code is R-linked, like `RHS.const`).
* `LE_Interp.Matches.app` carries the matched ctor's code: `… → Matches (.app f a) c (ctor' c' rargs'.reverse k :: rargs) …`
  (universally quantified `k`; `Matches.unique` becomes unique up to the given `k`).
* `build_spine`/`apps_realize`: construct `k` from the ctor const's own `a5`-shape (lifted).

## 3. LR changes (file:line anchors in /tmp/utt-snap1/Lean4Lean/Experimental/ShapeLogRel.lean)

### 3.1 `LRS.TyDefEq` (5431)
* `⟨.indTy, _⟩ => SynSpine Γ M N`  (was `True`):
  `∃ I ls a⃗ b⃗ ci, env.constants I = some ci ∧ classify I = some (.indTy |a⃗|) ∧ Γ ⊢ M ⤳* I ls a⃗ ∧ Γ ⊢ N ⤳* I ls b⃗ ∧ SynArgs a⃗ b⃗ ((mk ci.type).instL ls)`
  with `SynArgs [] [] _ = True`, `SynArgs (a::as) (b::bs) (forallE A₁ A₂) = Γ ⊢ a ≡ b : A₁ ∧ SynArgs as bs (A₂.inst a)`,
  else `False`. Purely syntactic; needs `Params.ind_type_tele` (the inductive's type is
  syntactically a Π-telescope, so instantiation keeps it a telescope and no whnf is needed on
  the `b`-side). Gives inductive-type injectivity as a by-product and discharges rule `Check`s.
* `⟨.ctor _ _ _, _⟩ => True` stays (see trans' below). `⟨.lam _, _⟩`, `⟨.bot, _⟩` unchanged.

### 3.2 `LRS.DefEq` (5612)
```
| .indTy => match hm : m.1 with
  | .bot => True
  | .ctor c l k => CtorDefEq IH M N A c ⟨l, _⟩ ⟨k, _⟩
  | _ => False                      -- was True for all m
```
```
CtorDefEq IH M N A c l k :=
  ∃ ls x⃗ y⃗ ci, env.constants c = some ci ∧ |x⃗| = |y⃗| = |l| ∧
    Γ ⊢ M ⤳* spine c ls x⃗ ∧ Γ ⊢ N ⤳* spine c ls y⃗ ∧
    SpineDefEq IH A x⃗ y⃗ ((mk ci.type).instL ls) l k
```
`SpineDefEq` is Exp2's definition with (i) `IH` abstract, (ii) the nil case
`SpineDefEq IH A [] [] T [] _ := IH.TyDefEq A T .indTy` (the "LR carries the type of a ctor
spine" conjunct, needed for `Check` discharge; `TyDefEq` at `indTy` is code-free so the level
of the final code is irrelevant). Cons case exactly as Exp2 (guarded by `k = forallE a₁ f`,
`p.HasType a₁`): whnf of the current type, `Γ ⊢ x ≡ y : A₁`, `IH.DefEq x y A₁ p a₁`,
`IH.TyDefEq (A₂[x]) (A₂[y]) (f.app p)`, `∃ w, Γ ⊢ A₂[x] ≡ A₂[y] : sort w`, recursion at
`((f.app p).lift _)`.  Add `IH.TyDefEq A₁ A₁ a₁` to the cons case (needed by `mono_l`'s
retyping through `mono_r_2`, and free from `ValTyPi2`).

### 3.3 LogRel fields (5271-5290), one by one, at the new cases
| field | status |
|---|---|
| sort_iff, sort_iff_ty, bot, toType, left_ty, symm_ty, trans_ty, mono_r_2_ty, whr_ty, join_ty | at `indTy` the new `SynSpine` is syntactic: left/symm via `IsDefEq.subst` on the telescope (same trick as Exp2's `∃w`), trans via determinism of whnf + defeqDF, whr via `WHRedS.determ_l` + ctor/indTy spines are WHNF (lemma `WHNF.ctorSpine`, needs `pat_wf` + no `major` on ctor heads), join_ty at `indTy ⊔ indTy = indTy` trivial. |
| left, symm, trans, conv | `SpineDefEq.left/symm/trans/conv` (Exp2, typechecked); head reductions agree by `WHRedS.determ`; nil conjunct by `left_ty/symm_ty/trans_ty` at `indTy` (symm needs `TyDefEq (T_end[x⃗]) (T_end[y⃗]) indTy` = `SynSpine`, derivable syntactically from `x⃗ ≡ y⃗` by `IsDefEq.subst` + `WHRedS.subst`). |
| trans' | **interface change**: add premise `a.HasType (.sort r)` (the term-shape of the types is a shape of a sort). Adequacy's trans' case already computes exactly this (`this.retype b4 b1`, Adequacy:155-166). Without it the field is false once `DefEq _ _ _ (ctor..) indTy` is non-trivial while `TyDefEq _ _ (ctor..)` is `True`. |
| mono_r_2, mono_r_1 | `a' = indTy ⇒ a ∈ {⊥, indTy}`; at `⊥`, `m : ⊥ ⇒ m = ⊥` ⇒ `True`. Unchanged proof shape. |
| mono_l | `ctor c l k ≤ ctor c l' k'`, both `: indTy` (= `SpineTyped`): `SpineDefEq.mono`: per step `a₁ ≤ a₁'`, `p ≤ p'`, `p : a₁`, `p' : a₁'` ⇒ `IH.mono_l` (p' → p at a₁', using `p : a₁'` by `HasType.mono_r`) then `IH.mono_r_2` (a₁' → a₁); `TyDefEq` at `f.app p ≤ f'.app p'` by `mono_r_2_ty`; recursion on lifted codes. The field-typing hypotheses come from the new `hasType`, which is why the code must be in the shape. |
| whr | `⤳*` composes; converse by `determ_l` since ctor spines are WHNF. |
| lift (`LR.lift_succ_aux` 6004) | `SpineDefEq.lift_aux`: `lift k = forallE (lift a₁) (lift f)` decomposes uniquely, so the only ∀ in the clause is over a determined pair; both directions reduce to `IH1/IH2` at `(p, a₁)` and `(f.app p)` via `WShapeFun.lift_app`. No non-lift shapes appear (contrast §1). `SynSpine` is level-free. |
| LR0 (5307) | no ctor/indTy at level 0: unchanged. |

`LE_Interp` (3333) is unchanged except `Const.ctor`/`Matches.app` (§2). `LR.SubstWF`/`Subst1`
(6061) unchanged.

## 4. IsDefEqStrong / Params changes (SExpr.lean)

* `IsDefEqStrong.const` (SExpr.lean:688) gains a **rank-bounded premise family**:
  `(∀ c' ci' ls', rank c' < rank c → env.constants c' = some ci' → ls'.length = ci'.uvars →
     Γ ⊢ (mk ci'.type).instL ls' : .sort (u c' ls'))` and the analogous ctor-bundle family for
  lower-rank constructors, and `(∀ p r, Pat p r → head p = c → GenericTyped p r)` (below).
  `IsDefEqStrong.defeq` ignores them; `IsDefEq.strong` (sorry) must build them by rank
  induction – that is where the environment induction lives, not in adequacy.
  Alternative kept in reserve: leave `IsDefEqStrong` alone and index adequacy by a rank bound.
* New `Params` fields (all true of Lean's kernel, all "environment facts"):
  `rank : Name → Nat` with `rank_type` (constants in `ci.type` have lower rank) and
  `rank_pat` (constants in fixed pieces of rules for `c` have rank ≤ rank c, and `= rank c` only for
  the bare `.fixed (const c _)` at an app head); `const_ty` (strong typing of `ci.type.instL ls`);
  `ctor_ty` (existing sorry, becomes a field); `no_etaCtor : classify c ≠ some (.etaCtor ..)`;
  `ind_type_tele`; `pat_typed` (§5.5); `check_form` (checks are `(rec-param, ctor-param)` pairs).
* `WHRed` (SExpr.lean:1073) gains
  `| major : Pat (.app q (.varN (.const c') n)) r → q.MatchesS f ls m → Γ ⊢ a ⤳ a' → Γ ⊢ .app f a ⤳ .app f a'`
  (reduce the major premise; paper §3.4 "congruence in the scrutinee"). Without it
  `Nat.rec z s (f x)` with `f x ⤳* succ y` is WHNF and the clause is unsound. `WHRed.determ`
  needs: ctor spines WHNF, rule arities uniform per head (`pat_uniq`-style), `major` vs `extra`
  exclusive because a matched major is already WHNF.

## 5. The const case under the design

Setting (Adequacy.lean:148-154): goal `(LR Γ₀).DefEq (const c ls) (const c ls) type m a`, with
`hM = .const a1 a2 a3 a4 a5 a6 a7`, `a6 : Const c ls R [] m'`, `a3 : m ≤ m'`, `a4 : m' : a_T`,
`a5 : LE_Interp ρ a_T type`, `ih3` (type adequacy), `ih5` (bundle adequacy), `ihP` (rank family).

Statement proved (ConstSpine), by induction on `a6` generalising the spine:
```
∀ rargs m' (hC : Const c ls R rargs m') (As Bs : List SExpr) T_cur a_cur m'',
  SpineHyp As Bs rargs (code descended from a_T) →      -- per layer j: Γ₀ ⊢ Aⱼ ≡ Bⱼ : A₁ⱼ, DefEq Aⱼ Bⱼ A₁ⱼ rargsⱼ a₁ⱼ, rargsⱼ : a₁ⱼ
  LE_Interp ρ a_cur T_cur → m'' ≤ m' → m'' : a_cur →
  (LR Γ₀).DefEq (spine c As) (spine c Bs) T_cur m'' a_cur
```
* **bot**: `m' = ⊥` ⇒ `m'' = ⊥` ⇒ `LR.bot`.
* **lam** (`m' ≤ lam' f`, `∀ (x,y) ∈ f, Const (x::rargs) y.T`): `a_cur = forallE a₁ a₂` (or ⊥).
  Unfold `LRS.DefEq.lam_forallE`: whnf `T_cur ⤳* forallE A₁ A₂`, `Γ ⊢ A₁ : sort`, `TyDefEq A₁ A₁ a₁`,
  `PiDefEq` all from `ih3` descended through the previous layers' `PiDefEq` (exactly as the
  existing appDF case extracts them). `LamDefEq`: given related `(x, x', p)`, pick the entry
  `(x₀, f.app p) ∈ f` with `x₀ ≤ p` (`WShapeFun.app_eq`), lower the arg by `mono_l`, recurse
  with `rargs := x₀ :: rargs`, `m' := f.app p`, `a_cur := a₂.app p` (typing from `HasTypeLam`).
* **ctor** (`m' ≤ ctor' c rargs.reverse k`, `R k type`): `a_cur = indTy`. Produce `CtorDefEq`:
  spines are already `c ls As` (WHNF, `⤳*` refl); `SpineDefEq` along `k`: the layer hypotheses are
  at the codes descended from `a_T`, the clause wants them at `k`'s codes; both `k` (via `a7`) and
  `a_T` are `LE_Interp ρ _ type` shapes, so `LE_Interp.compat` + `TShape.Join` + `ih3` at the join
  + `mono_r_1`/`mono_r_2` retype (lemma `LR.retype`, the same chain as `Adequate.cons`). Codomain
  `TyDefEq`s from `ih3`'s `PiDefEq`; `∃w` by `IsDefEq.subst`; nil conjunct `TyDefEq T_cur T_cur indTy`
  from `ih5` (bundle: `type ≡ Π Ts, I args`) descended to the end code, which is `a_cur = indTy`.
* **indTy** (`classify c = indTy |rargs|`, `a_cur = sort`): `TyDefEq (spine) (spine) indTy` =
  `SynSpine`: whnf refl, `SynArgs` from the layer hypotheses (syntactic part) using
  `ind_type_tele` so the `A₁ⱼ` are literally the telescope types.
* **pat** (`Pat p r`, `Matches p c rargs m'''`, `RHS ls m''' R m' r.1`): `p = iota rec j c' n`
  (`pat_simple`), so the major is the last layer, its shape in `rargs` is `ctor c' l' k'` (non-⊥
  by `no_etaCtor`) and its type-shape is forced to be `indTy`; its layer hypothesis is therefore
  `CtorDefEq`: `A_maj ⤳* c' ls' x⃗`, `B_maj ⤳* c' ls' y⃗`, `SpineDefEq x⃗ y⃗ type_c' l' k'`,
  `TyDefEq A₁_maj (T_end[x⃗]) indTy`.
  1. `spine c As ⤳* spine c As[maj := c' ls' x⃗]` by `WHRed.major` (+`WHRedS.app` for later layers – none, the pat leaf is at exact arity); same for Bs.
  2. `WHRed.extra` fires: `MatchesS` holds syntactically (arities from `Matches.arity`/`pat_arity`);
     checks (`dfs`) are `(rec-param, ctor-param)` pairs (`check_form`), discharged from the nil
     conjunct + `SynSpine` (`I ps ⤳* I ps`, `I ps' ⤳* I ps'`, `psⱼ ≡ ps'ⱼ`). Note the check's
     type is free in `dfs` (SExpr.lean:1076), so `∃ T` suffices.
  3. `(LR Γ₀).whr` reduces the goal to relatedness of the two RHS instances at `(m'', a_cur)`.
  4. RHS instances = `(r.1.toSExpr).subst σ_p` where `toSExpr` maps `.var path ↦ bvar`, the bare
     self-reference `.fixed (const c _) ↦ bvar self`, other `.fixed e ↦ e`, `.app ↦ app`.
     `Params.pat_typed` supplies `IsDefEqStrong Γ_p (r.1.toSExpr) _ T_p` with all constants of
     rank `< rank c` (self is a variable of type `type_c`); `adequacy_<` applies to it.
     Build `ρ_p` (outer args ↦ `rargs`, fields ↦ `l'`, self ↦ `m_e` from the `R` fact),
     `σ_p/σ_p'` (the matched terms), and `SubstWF Γ₀ σ_p σ_p' Γ_p ρ_p` by `Adequate.cons`-style
     upgrades: outer args from the layer points, fields from `SpineDefEq` points (type adequacy
     of `type_c'` from `ihP`/`adequacy_<`), self from `ihR _ _ hR` (Exp1) + `ih3`.
     `hM_rhs : LE_Interp ρ_p m' (r.1.toSExpr)` is assembled from `RHS ls m''' R m' r.1` (`.var ↦ .bvar`,
     `.fixed ↦ a7 _ _ h` or `.bvar self`, `.app ↦ .app`); `hA_rhs` from `LE_Interp.subst` on `T_cur`.
     Conclude with `(adequacy_< pat_typed hM_rhs hA_rhs hmem).2 W_p` and `subst` equations.

### 5.5 Why a *generic* RHS typing with a self-variable
Running adequacy on the *instance* needs an IH for a non-subderivation. Running it on a generic
RHS whose `const c` nodes are real const nodes regresses (their premise family contains the same
generic typing). Abstracting the recursive occurrence as a variable removes `c` from the
derivation; its `Subst1` is exactly what the structural IH `ihR` (Exp1) gives at the shape `m_e`
recorded in the model's `RHS.const` fact, upgraded to all `m ≤ m_e` and all type-shapes by
`mono_l` and the `Adequate.cons` chain (type adequacy of `type_c` = `ih3`).

## 6. Measure

Lexicographic, well-founded:
1. **rank of the head constant** (outer WF induction, in `ConstAdequate`): type adequacy of `c`'s
   type and bundles, adequacy of the generic RHS typing, and `ConstAdequate` of lower-rank fixed
   constants all mention only constants of rank `< rank c` (`rank_type`, `rank_pat`, `pat_typed`).
2. **structural on `hM : LE_Interp ρ m (const c ls)`** (Exp1): the only same-rank recursion is the
   bare self-reference `.fixed (const c ls)` in `RHS`, reached through `a7`, which is a proper
   sub-derivation; `ihR` gives its relatedness at `m_e`.
3. **structural on `Const c ls R rargs m'`**: the lam layers (`Const.lam`'s entries).
Adequacy itself stays a structural induction on `IsDefEqStrong` (`adequacy_rel`, parametrised by
`CA : ∀ c, rank c < k → ConstAdequate c`); the const case calls `CA`, the other 13 cases are
untouched. trans/symm/trans' cases obtain fresh witnesses only via `LE_Interp.sound` on
*sub*-derivations (as now); they never re-enter the const recursion, so they do not interact with
the measure. The shape-side recursion never consults the typing derivation, which is what makes
"the RHS is not a subderivation" harmless.

## 7. K, Props, struct eta, quotients

* **Prop-valued inductives**: interpret to `⊥` (indTy : sort false is false; ctors cannot be
  typed, so `Const.ctor` yields `⊥`). Their constructors need nothing. Their **recursors' iota
  rules are outside the model** (a `⊥` major fires no `Const.pat`; `CtorBundle.hu0` already
  forbids Prop ctors). Pre-existing; the paper's conclusion flags it. For Lean this excludes
  `Acc.rec`, `Eq.rec`, `And.rec`, … as *reduction rules*; acceptable for the unique-typing
  theorem only if the environment is restricted accordingly (same restriction as today).
* **K-like reduction**: not a rule of the typed theory (derivable from `proofIrrel` + iota on the
  ctor); but iota on a Prop ctor is excluded as above, so K is excluded with it. Nothing new.
* **struct eta**: not in `IsDefEq`/`WHRed`/`Pattern` (SimplePattern only; VEnv has no eta entries).
  The shape model's `IsStruct`/`ctor'` collapse is only sound *with* an eta rule, and the
  head-reduction clause is only sound *without* one; `Params.no_etaCtor` picks the current
  syntax. Adding eta later means a projection-based clause for etaCtor heads (paper §3.1) and
  `toCtorWhenStructure` in `WHRed`; `SExpr` has no `proj`, so projections would be rec-encoded.
* **quotients**: `Quot.lift f h (Quot.mk r a) ⤳ f a` is an iota `SimplePattern` with `Quot.mk`
  classified `ctor`, `Quot` classified `indTy`; covered. `Quot.ind` lands in Prop: `⊥`.
* **nested/reflexive inductives**: their rec RHSs contain lambdas over path vars, inexpressible in
  `Pattern.RHS`; excluded already.

## 8. Reproof cost (estimates for one expert)

| item | effort |
|---|---|
| Shape algebra: `ctor` gets a code (LE/Compat/join/lift/plift/olift/WF/hasType/unfold, `ctor'_le`, `ctor'_join`, `ctor.inj`, `TShape.*_not_le_ctor'`, `HasType.ctor*`) | 3-4 days, mechanical |
| Model: `Const.ctor` R-link, `Matches.app` code, `Const.mono/mono_l/lift/compat_join/compat_mismatch`, `Matches.*`, `of_matchesS`, `build_spine`, `apps_realize`, `strongSound` const/extra | 4-6 days |
| `WHRed.major` + WHNF of ctor spines + determ cases | 1-2 days (existing extra sorries stay) |
| LR: `SynSpine`, `CtorDefEq`/`SpineDefEq` (+`TyDefEq A₁ A₁ a₁`), fields: left/symm/trans/conv done in Exp2 pattern; mono_l, lift_aux, whr, trans' premise | 4-6 days |
| `IsDefEqStrong.const` premise family, `Params` fields, `RHS.toSExpr`, `pat_typed` statement | 2-3 days |
| Adequacy restructure (`adequacy_rel`, `ConstAdequate`, spine lemma, `LR.retype`, pat-leaf plumbing: `ρ_p/σ_p/W_p/hM_rhs`) | 2-3 weeks |
| `IsDefEq.strong` grows (rank induction) – stays a sorry as today | – |

## 9. Risks / where I am guessing

1. `Const.ctor`'s code `k` vs the enclosing `a5` shape: retyping through compat/join/`ih3`; I did not
   typecheck `LR.retype`. Medium risk.
2. `pat_typed` with a self-variable assumes self-references are bare `const c` at app heads (true
   for Lean recursors; definitions are non-recursive). Also assumes the generic RHS typing uses
   only constants of lower rank (ctors precede recursors).
3. `check_form` and the discharge via the nil conjunct + `SynSpine` assume Lean's shape of iota
   rules (rec major domain `I params`, ctor body `I params'`). The `Check` machinery is otherwise
   unspecified in the file.
4. Pre-existing mismatch: `VEnv` rules are λ-closed schemas (`vdefeq(... => ...)`) while
   `Params.extra_pat`/`WHRed.extra` match open app spines; the design assumes the latter.
5. `trans'` premise change ripples into `UniqueTyping.lean` only through adequacy (checked: the
   case already has the fact).
6. Level bookkeeping of `k` inside `ctor` (components one level down, lifted in `SpineTyped`) may
   force `TShape`-level statements in more places than estimated.
7. `SynSpine` soundness in the fundamental lemma relies on variables being `⊥` (neutrals never
   need to reduce); with `SubstWF` this is the standard argument but I have not re-run the
   appDF/lamDF cases for the new `indTy` clause.
8. (κ) vs (λ): if `Matches` turns out to need the code from the *type* (e.g. `compat_join` across
   different ctors of one inductive), switch to `indTy K`; the LR side is identical.
