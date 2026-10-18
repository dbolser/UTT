# Design "fuel-measure": the const case of `LR.adequacy` (Angle B)

Designer: fuel-measure. Snapshot: /tmp/utt-snap1. Scratch: /tmp/utt-exp/design-fuel-measure/
(Stuck.lean, Subst1.lean, Fuel.lean — all typecheck; the only `sorry` is the deliberately
stated spine lemma in Fuel.lean).

## 0. One-paragraph verdict

Angle B *as posed* ("keep the LR's shape clauses, change only the induction") cannot close
the const case: with `DefEq _ _ _ m indTy = True`, the theorem `LR.adequacy` is false, not
merely unproven (Section 2). The syntactic constructor spine is genuinely needed at exactly
one place — the `Const.pat` leaf when the observed shape pair `(m, a)` is non-degenerate
(`a = sort` with `m ∈ {sort, forallE}`, or `a = forallE` with `m = lam` and a non-degenerate
codomain observation), i.e. for large elimination — and nothing in the current LR or in the
current `WHRed` can supply it. So the ctor clause (Angle A) and a `major` rule in `WHRed` are
prerequisites. What Angle B *does* contribute, and what any ctor-clause design still needs, is
the answer to obstacle (ii) (no IH for rule RHSs). The measure is: outer structural induction
on `H : IsDefEqStrong` as today; inside the const case only, a *local* structural induction on
the model derivation `hM : LE_Interp ρ m (const c ls)` (this is the fuel: every pattern
unfolding in the model nests a strictly smaller `LE_Interp` derivation of each closed RHS leaf
through `a7`); the closed RHS leaves that are not same-block constants get their typing
derivations as new premises of `IsDefEqStrong.const`, hence outer IHs. The local induction
never crosses an `H`-node, so the fresh witnesses produced by `LE_Interp.sound` in the
symm/trans/trans' cases never feed it. Sections 3-5 give the details, Section 6 the costs,
Section 7 what is excluded (K, Prop-valued iota, struct-eta on variables) and why that is
partly inherited from the existing development.

## 1. The goal at the sorry, by `Const` sub-case

At ShapeLogRelAdequacy.lean:148-154 (after `cases hM`, `suffices`, `clear σ`):

    a3 : m.T ≤ m'         a4 : m'.HasType a'        a5 : LE_Interp ρ a' ci.type[ls]
    a6 : LE_Interp.Const c ls R [] m'               a7 : ∀ m e, R m e → LE_Interp ρ m e
    hA : LE_Interp ρ a.T ci.type[ls]                hmem : m.HasType a
    ⊢ (LR Γ₀).DefEq (const c ls) (const c ls) ci.type[ls] m a

`LRS.DefEq` (ShapeLogRel.lean:5612) is `True` at `a = bot`, `a = indTy`, and at `m = bot`;
it is `TyDefEq _ _ m` at `a = sort`, and the `lam_forallE` Pi/Lam clause at `a = forallE`,
`m = lam`. Hence, leaf by leaf of `a6`:

| `a6`      | constraint on `m`                | nontrivial goals                                         |
|-----------|----------------------------------|----------------------------------------------------------|
| `bot`     | `m = bot`                        | none (`(LR _).bot`)                                      |
| `indTy`   | `m ≤ indTy`, so `a = sort`       | none (`TyDefEq _ _ indTy = True`)                        |
| `ctor`    | `m ≤ ctor' c []`, so `a = indTy` | none today; with a ctor clause: `const c ls ⤳* const c ls` (rfl) |
| `lam`     | `m ≤ lam' f`, `a = forallE a₁ a₂`| `ci.type[ls] ⤳* Π A₁ A₂` + `PiDefEq` (from `ih3`), and `LamDefEq`: for every related `y y'` at `p : a₁`, `DefEq (c y) (c y') (A₂[y]) (g.app p) (a₂.app p)` — recursion on the spine |
| `pat`     | `m ≤ m'`, `RHS ls m'' R m' r.1`  | depends on `(m,a)`: `a=sort, m=sort/forallE`: `const c ls ⤳* sort/Π`; `a=forallE, m=lam`: as the lam row, but the Const derivation ends here, so the unfolding must happen; `a ∈ {bot, indTy}`: none |

The `lam` row needs the statement generalised over a spine (Fuel.lean `const_spine`), and
the `pat` row is reachable at every spine length (through `Const.lam`). So "the pat leaf" is
really: *after* `k` lam layers, with `xs, xs'` related at typed shapes `ps ≥ rargs`,
`Matches p c rargs m''` at shape level, `RHS ls m'' R m' r.1`, and a non-degenerate `(m, a)`.
Its proof must (a) head-reduce `apps c xs` to `r.1.applyS ls m2` and (b) prove adequacy of
the RHS instance at `(m, a)`.

## 2. With the LR unchanged, the pat leaf is unprovable — the theorem is false

Two independent facts, both checked in Lean against the snapshot:

* **Stuck.lean** (`WHNF.rec_bvar`): `extra` needs a *syntactic* `MatchesS`, so using only
  `pat_simple` and `pat_wf`, if `classify rec = symb (n+1)` then `rec a₁ … aₙ (bvar i)` is
  in WHNF. When this note was written the SExpr `WHRed` had only `app`, `beta`, `extra`, and
  `rec a₁ … aₙ (g T X)` (any `g` classified `symb`, e.g. `id`) was stuck as well
  (`WHNF.rec_symb_major`, since deleted). The `major` rule of the VExpr-level `WHRed`
  (Theory/Typing/HeadReduction.lean:59-64) has since been added to the SExpr one (b2516c4),
  which unsticks that case; `bvar i` stays stuck.
* **Subst1.lean** (`LR.SubstWF.push_any_at_ctor`): with the current LR, `LR.Subst1`
  (ShapeLogRel.lean:6061) accepts *any* `x : N` (`N` classified `indTy 0`) at *any* shape
  `xs : indTy`, in particular `x := bvar j` at `xs := ctor' succ [ctor' zero []]`. Reason:
  every shape interpreting `const N ls` is `bot` or `indTy` (`Const.indTy_inv`), and
  `TyDefEq`/`DefEq` are `True` there.

Put together: take `Γ = N :: Γ₀`, `Γ₀ = [N]`, `σ = cons id (bvar 0)`, `ρ = push nil xs.T`,
`M = N.rec (fun _ => Type) Nat (fun _ _ => Nat → Nat) (bvar 0) : Type`. The model gives
`hM : LE_Interp ρ (forallE bot bot).T M` (Const.lam layers of `N.rec`, then `Const.pat` with
the shape-level `Matches` firing on `ρ 0 = ctor' succ […]`, RHS shape `Π`). `Adequate` at
`σ` demands `(LR Γ₀).TyDefEq (M.subst σ) (M.subst σ) (forallE bot bot)`, i.e.
`[N] ⊢ N.rec … (bvar 0) ⤳* forallE _ _`, contradicting `WHNF.rec_bvar`. The model-side
derivation is argued on paper (Experiment 2 formalises the LR side, Experiment 1 the syntax
side). So: *no* change to the induction, the premises of `IsDefEqStrong.const`, or the
measure can rescue the const case while `DefEq` is `True` at `indTy`; and the corollary
`forallE_whRed_l` is false for the current `WHRed` whenever the environment has a
large-eliminating recursor. Where exactly the spine is needed: at the `pat` leaf, for (a).
The LR must say "related at `ctor c l` ⇒ both head-reduce to `c`-applications with arguments
related at `l`" (the paper's `0`/`S u` clauses), and `WHRed` must reduce in major-premise
position. Those two are assumed from here on (Angle A supplies the clause; I state what I
need from it in 3.0).

## 3. The design (given a ctor clause and `major`)

### 3.0 Assumptions on the other pieces
* `LRS.DefEq M N A (ctor c l hl) indTy ↔ ∃ args args', Γ ⊢ M ⤳* apps c args ∧
  Γ ⊢ N ⤳* apps c args' ∧ Forall₃ (IH.DefEq) args args' l` (+ types from the ctor telescope
  via `CtorBundle`/`h5`). `TyDefEq` stays `True` at `indTy` (inductive-type injectivity is
  not needed for unique typing). `ctor' c l = bot` for structures with all-bot args is left
  as is (struct eta: a variable of structure type is at `bot`).
* `WHRed.major : IsMajorPremise f → Γ ⊢ a ⤳ a' → Γ ⊢ app f a ⤳ app f a'`, with
  `IsMajorPremise` ported from HeadReduction.lean:45. `WHRed.determ` ported likewise
  (ctor applications and `symb` under-applications remain WHNF, Stuck.lean `WHNF.apps_symb`).
* Checks are trivial: Params field `pat_check : Pat p r → r.2 = .true` (K is not a
  `SimplePattern` anyway; Section 7).

### 3.1 Strengthened `IsDefEqStrong.const` (SExpr.lean:641-645)
Add to `Params`: `Block : Name → Name → Prop` (same recursive block; reflexive, symmetric),
`rank : Name → Nat`, and the fields
* `pat_leaf_ty : Pat p r → e ∈ r.1.fixedLeaves → ∃ T, ∀ ls, [] ⊢ (mk e).instL ls : T.instL ls`
  (closed RHS leaves are well-typed closed terms; replaces inversion on `df.WF`),
* `pat_leaf_rank : Pat p r → e ∈ r.1.fixedLeaves → ¬SameBlock Block p.head e →
  ∀ c' ∈ consts e, rank c' < rank p.head` and `block_rank : Block c c' → rank c = rank c'`
  (env.Ordered alone does not give this: `Foo := Foo` is `Ordered`),
* `pat_rhs_wt`: the RHS of a rule is typable syntax-directedly from leaf types and the
  telescope types of the matched variables, every `.app` node having a function whose type is
  *syntactically* a Pi with the argument's type as domain (true for delta = single leaf,
  iota = minor applied to fields and recursive calls, quot = `f a`).

New premises of `const` (checked as a legal inductive in Fuel.lean, `IsDefEqStrong'`):
```
(Ts : ∀ p r, Pat p r → p.head = c → VExpr → SExpr) →
(∀ p r (hP : Pat p r) (hc : p.head = c), ∀ e ∈ r.1.fixedLeaves,
   ¬SameBlock Block c e → Γ ⊢ (mk e).instL ls : Ts p r hP hc e) →
(∀ c' ls', Block c c' → env.constants c' = some ci' → ls'.length = ci'.uvars →
   Γ ⊢ (mk ci'.type).instL ls' : sort (u' c' ls'))
```
(the last gives type-validity for same-block constants reached by the local induction; it
must also be bundled with their `CtorBundle`s if a block could contain ctors — it cannot:
blocks are sets of recursors). Note `∨` must be written as `¬_ → _` (Lean rejected the
nested `Or`). `IsDefEqStrong.defeq` ignores the new premises; `LE_Interp.strongSound` too.
`IsDefEq.strong` builds them by strong induction on `rank c` (outer) and on the derivation
(inner); the same-block exclusion is what makes the premise trees finite for recursors
(`rec` occurs in its own iota RHS; mutual recursors occur in each other's).

### 3.2 The const case of `LR.adequacy`
Outer: `induction H` as now; in `const` we have `ih3`, `ih5` (ctor telescope), `ihU` (leaf
typings), `ihB` (block types). Then:

**Step A (local fuel).** Generalise to the motive
`P hM := ∀ c' ls' (he : e = const c' ls') (hb : Block c c') a (hA) (hmem), DefEq e e T' m a`
and run `induction hM` (Fuel.lean (b): the IH `ih7 : ∀ m e (h : R m e), P (a7 m e h)` is
available). In the `const` constructor, go to Step B with `a6`.

**Step B (spine).** By induction on `a6 : Const c' ls' R rargs m'` prove `const_spine`
(Fuel.lean (c)): for typed `ps ≥ rargs`, spines `xs xs'` related at `ps` with telescope
types, `m ≤ m'` typed by `a`, and type-validity `TyDefEq T T a` of the telescope type:
`DefEq (apps c' xs) (apps c' xs') T m a`.
* `bot`: `(LR _).bot`.
* `indTy`: `a = sort`, `m ∈ {bot, indTy}`, `TyDefEq` is `True`.
* `ctor`: `m = bot` or `m = ctor c' l` with `l ≤ rargs.reverse`; the ctor clause holds with
  `⤳* = rfl` and `hrel` + `mono_l`.
* `lam`: `m = lam g`, `g ≤ f`, `a = forallE a₁ a₂`. `T ⤳* Π A₁ A₂` and `PiDefEq` come from
  `hT` (ValTyPi2). For `LamDefEq`: given `y ≡ y' : A₁` related at `p : a₁`, pick
  `(x, y_sh) ∈ f` with `x ≤ p` and `f.app p = y_sh` (`WShapeFun.app_eq`); the IH for
  `Const (x :: rargs) y_sh.T` at `ps' = p :: ps`, `m := g.app p ≤ y_sh`, `a := a₂.app p`,
  with the next telescope type's validity from `PiDefEq` at `p` (exactly the `valPi` moves of
  the existing `lamDF`/`appDF` cases).
* `pat` (Step C).

**Step C (unfold).** `Matches p c' rargs m''` (shape level), `RHS ls m'' R m' r.1`, `(m, a)`
non-degenerate (otherwise `True`).
1. Syntactic match: each ctor position of `p` corresponds to an `x_i` related at
   `p_i ≥ ctor' c_i l_i`; the ctor clause gives `x_i ⤳* apps c_i args_i` (and primed);
   `WHRedS` under `major` (the prefix `apps c' (xs before i)` is `IsMajorPremise`) gives
   `apps c' xs ⤳* apps c' xs[i ↦ apps c_i args_i] =: L`, and `MatchesS p L ls m2` holds
   syntactically with `m2` the arguments/fields; `pat_check` makes `dfs := []` work.
   So `Γ₀ ⊢ apps c' xs ⤳* r.1.applyS ls m2` (and primed), and `(LR _).whr` reduces the goal
   to `DefEq (r.1.applyS ls m2) (r.1.applyS ls m2') T m a`.
2. Mini-adequacy of the RHS, by induction on the `RHS` derivation (`RHS ls m'' R m' r.1`),
   with `pat_rhs_wt` supplying the syntactic types:
   * `.bot`: `(LR _).bot`.
   * `.var path`: `m ≤ m2-shape(path)`; the matched argument (or ctor field) is related at
     that shape by `hrel` (or by the ctor clause's field relatedness); `mono_l`.
   * `.app F A`: `m ≤ (f.app x).T`; IHs give `DefEq F[..] F[..] (Π) f (forallE ..)` and
     `DefEq A[..] A[..] A₀ x a₀`; the `LamDefEq` component of the former at `x` gives the
     goal (with `mono_l`, `mono_r_*`), the type being the syntactic `B.inst A` (the `appDF`
     case of the current proof is the template).
   * `.const e` (closed leaf, `R m_e e`, so `he := a7 m_e e hR : LE_Interp ρ m_e e`, a
     strict sub-derivation of `hM`): if `e = const c'' us` with `Block c c''`: the local IH
     `ih7` at `he` (Step A's motive, with `ihB` for its type validity). Otherwise `ihU` for
     the leaf's typing premise: `(LE_Interp.sound H_e W).2 he |>.out` gives the typed shape
     `m_e' ≥ m_e`, `ihU he' hT_e hmem_e` gives `Adequate`, hence `DefEq e e T_e m_e' a_e`,
     then `mono_l`.

### 3.3 Levels and contexts
`const c ls` is closed, so `σ` disappears (`subst_eq .zero`) and `ρ` only matters through
`LE_Interp.closed_iff`; the leaf derivations are in `[]` and are weakened to `Γ₀` by
`IsDefEq.weak'`. The spine lemma is stated at the level `k` of the typed shapes `ps`; `rargs`
at level `n` is lifted with `TShape.LE`.

## 4. The measure and why it is well-founded
Lexicographic: (1) structural on `H : IsDefEqStrong` (outer, as today); (2) structural on
`hM : LE_Interp` — *only inside the const case*, motive restricted to same-block constants,
the `H`-node's premises fixed; (3) structural on `a6 : Const`; (4) structural on the `RHS`
derivation. Recursive calls:
* symm/trans/trans'/appDF/lamDF/defeqDF/beta/eta/extra/proofIrrel obtain fresh `hM'` from
  `LE_Interp.sound`/`InterpTyped.out`; they are all level-(1) calls, which place no
  constraint on `hM'`. They never enter another node's local induction.
* inside the local induction, calls go to: (a) `ih7` at `a7 m e hR`, a strict
  sub-derivation (level 2 decreases; `H`-node unchanged); (b) `ihU`/`ih3`/`ihB`/`ih5`, outer
  IHs that accept any model derivation (level 1 decreased earlier); (c) the `Const`/`RHS`
  IHs (levels 3-4). Fresh witnesses created inside (via `SoundTy`) are only ever passed to
  (b). So no call feeds a non-smaller `hM` to the local induction.
Why the alternatives fail: a numeric fuel on `hM` (pat-depth) is not bounded across
`trans` (`LE_Interp.sound` along `H1` can add `#extra(H1)` unfoldings, and `symm` reuses the
same derivation for conversion and recursion, so `depth + size(H)` does not decrease); a
rank-of-head measure fails on self-referential rules (`Foo := Foo` is `Ordered`; `rec` in its
own RHS); an env-ordered family of `Params` instances would require monotonicity of the whole
6100-line development. The local induction sidesteps all of this because the term inside the
const case is fixed (`const c' ls'`) and the `H`-node is fixed.

## 5. Where syntactic constructor information is genuinely needed
Only in Step C.1, and only when `(m, a)` is non-degenerate. With the LR unchanged that is
precisely where the proof dies (Section 2); with the ctor clause it is exactly what the clause
provides. Everywhere else (bot/indTy/ctor leaves, lam layers, RHS `.var`/`.app`/`.const`)
no syntactic spine is needed. The task's hope "the const case might be provable WITHOUT any
syntactic constructor information because at `indTy` the goal is True and at `forallE` the
`whr` field plus RHS adequacy suffice" is correct for small elimination into inductive types
(codomain shape `indTy`) and false for large elimination, which is what `forallE_inv` is
ultimately about.

## 6. Re-proof cost
* SExpr.lean: `IsDefEqStrong.const` (+3 premises): `IsDefEqStrong.defeq` trivial;
  `IsDefEq.strong` (currently sorry) now needs rank induction + the new Params fields:
  medium (new, ~150 lines once `pat_leaf_ty` is a field). `WHRed` + `major`:
  `WHRed.subst/weak'/weakU_inv` small; `WHRed.determ` port from HeadReduction.lean:170-210
  (~80 lines, also closes the existing `extra` sorries there); `IsMajorPremise` + lemmas.
* ShapeLogRel.lean: `strongSound` const case: ignore new premises (trivial). The ctor clause
  itself (Angle A): all 19 `LogRel` fields at the new `(ctor, indTy)` case, `lift` lemmas,
  `Subst1` unchanged in form: large (~400-600 lines) but not this design's.
* ShapeLogRelAdequacy.lean: const case ≈ 400-800 lines (local induction, `const_spine`, RHS
  mini-adequacy, Step C.1 reduction construction). Other cases: `appDF`/`lamDF` unchanged;
  `bvar` uses `Subst1` unchanged; `extra` unchanged (goes through the const case).
* `Params`: 4-5 new fields; `ctor_ty` and `extra_pat` stay as they are.

## 7. K, Prop-valued inductives, struct eta, quotients
* K-like reduction: excluded. It is not a `SimplePattern` (major premise is a variable), and
  a shape model cannot see the check `a ≡ b`; the paper excludes it too. `pat_check` records
  the exclusion. For full Lean this is a real gap (Eq.rec on `h : a = a`).
* Prop-valued inductives interpret to `bot` via `a4 : m'.HasType a` with `a : sort false`.
  Consequently iota rules whose major premise is a proof (`Eq.rec`, `Acc.rec`, `And.rec`,
  subsingleton elimination) can never fire in the model, while their RHS can be non-bot
  (large elimination): soundness of the model would fail. The current development already
  excludes them silently: `CtorBundle.hu0 : u ≠ .zero` and `pat_wf` (nested pattern heads
  must be classified `ctor`) mean Prop-constructors cannot be classified `ctor`, so such rules
  cannot be in `Pat`, hence (by `extra_pat`) not in `env.defeqs`. This design does not change
  that; it is the same obstacle the paper's conclusion names ("proof irrelevance with K").
  Not acceptable for full Lean (cast/▸ are `Eq.rec`), but orthogonal to the const case.
* Struct eta: the model fires iota on structure recursors for *any* major (`ctor'` collapses
  to `bot` for `etaCtor` with bot fields), but no `WHRed` rule eta-expands a variable of
  structure type (that step is type-directed in Lean's kernel, `toCtorWhenStructure`). For
  large-eliminating structure recursors applied to a variable this breaks adequacy exactly
  like Section 2, with the ctor clause unable to help (shape is `bot`). Needs either a typed
  eta-expansion step in `WHRed` or restricting `etaCtor` to small elimination. Pre-existing;
  flagged.
* Quotients: `Quot.lift f h (Quot.mk r a) ⤳ f a` fits `SimplePattern.iota` with `Quot.mk`
  a ctor of the `indTy` `Quot`; RHS has no closed leaves; handled by Steps B/C unchanged.

## 8. Risks / where I am guessing
* The ctor clause's `trans`/`join`/`mono` fields are someone else's; I assume they go
  through (determinism of `⤳*` on ctor applications is fine, Stuck.lean).
* `pat_rhs_wt` is an assumption about Lean4Lean's rule set that I have not verified against
  a concrete `Params` instance (none exists in the repo); if a delta RHS is split into
  `.app` of several leaves, the mini-adequacy needs Pi-injectivity for the leaf types —
  circular. Normalising delta RHSs to a single leaf removes the issue.
* The local induction's motive quantifies over block constants and arbitrary level lists;
  Experiment 3(b) only checks that the IH has the right shape, not that the generalisation
  elaborates with the real `Const`/`RHS` nesting.
* The model-side half of the Section 2 counterexample (deriving `hM` at a Pi shape for
  `N.rec … (bvar 0)`) is on paper, not in Lean; it needs a concrete `Pat` for `N.rec`.
* Prop-valued iota and struct eta on variables are outside what this (or any shape-model)
  design handles; if the goal is "Lean", they must be solved separately.
