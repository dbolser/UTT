# Experiment E3 (the rank measure and `Pattern.gen`): PASS

2026-10-20. Plan: `../../PLAN.md` §1 D4 (and D3's two fields), §2 row E3. Base: commit
`3bccfa8` (typed reductions, stage-1a clause and the environment-indexed `IsDefEqStrong E` all
landed, so the module uses the repo's `VEnv.below`, `exists_below`, `mkSE`, `CtorProviderE.synE`,
`weak0`/`weak_append`, `telescope`, `soundSE` and redefines none of them). Run: two independent
Opus attempts on fresh snapshots, each checked by an independent adversarial verifier (clean
rebuild, grep for cheats and for private redefinitions, tracer rooted at every constant of the
module, statement comparison against D4/D3 and `historical/PatLeafStmt2.lean`, concrete evaluation
of `Pattern.gen`). Verdicts: both pass, first round, no issues.

## 0. Outcome

**D4 holds as written.** `Measure7.lean` (attempt a, 871 lines; `Measure7-b.lean` is attempt b,
1075 lines) has:

- `Pattern.gen` as a total **function** `VEnv → (Name → Nat) → (Name → Option Classification) →
  (p : Pattern) → p.RHS → Option PatGen`, with per-occurrence self variables, `none` when the
  head's type has fewer syntactic Π-binders than the pattern arity, and the delta case
  `ctx = [], lhs = const c params, type = ci.type`;
- the spec lemmas **(a) `gen_head`, (b) `gen_lhs`, (c) `RHS.toVExpr_subst` (per occurrence),
  (d) `gen_type`, (e) `gen_arity` (any pattern, delta too), (f) `gen_rhs`, (g) `gen_self`**, all
  sorry-free, stated for the general iota pattern `app (varN (const rec) m) (varN (const c') n)`;
- `RankParams`, the D4/D3 field package (`rank`, `rank_ordered`, `type_below`, `pat_rank`,
  `pat_gen`, `pat_typed`, `pat_defeq`, `pat_check`, `indTy_closed`, `ctor_fields_closed`) with
  D4/D3's statements text for text; this is R5's field list and E4's `ParamsR`;
- `EnvStrongR` and `EnvStrongR.of_params`: rank-bounded strong typings of every constant's type
  (at `below (rank c)`, context `[]`), of every entry of a rule's generated context, and of
  `rhsAbs` in `self ++ ctx` (at `below (rank head)`), from `type_below`/`pat_typed` via
  `rank_ordered`, `VEnv.IsDefEq.strong`, `instL` and the repo's `mkSE`; sorry-free;
- `LR.WFIH`, `LR.ConstGoal` (the ∃-typed-upper-bound form), `LR.LocalIH` (same-rank bare-constant
  leaves, no `Block`), the statements of `LR.const_spine` (R9) and `LR.pat_leaf_1a` (E6/R10) with
  marked sorries, and **`LR.const_local` proved** by induction on `hM` through the R-closure, its
  only recursive calls the local IH and the WF IH at `rank c ≤ rank c₀ < k`, calling
  `const_spine` at the leaves (`rargs = []`, `ρ = .nil`, `W = SubstWF.id`);
- as a bonus, R8's wiring `LR.const_case` (the `const` case of the rank-indexed adequacy through
  `const_local` at `c₀ := c`; tracer: exactly `const_spine`); attempt b also has the outer WF
  induction `LR.adequacy_rank_wf` (`Nat.strongRecOn`, sorry-free), the pattern-leaf reduction
  chain `pat_leaf_reduce` (`major`, then `extra`), and `gen_lhs_matches` (the instantiated LHS
  matches `p` with `m2 = σ ∘ genIdx`, so `MatchesS.determ` supplies (c)/(f)'s index hypothesis).

Tracer: `[LR.const_local]` reaches exactly one sorry constant, `LR.const_spine`;
`[LR.pat_leaf_1a]` exactly itself; `[Pattern.gen, EnvStrongR.of_params]` none; the repo's
`LR.adequacy` block is unchanged. Rooted at all 298 (a) / 357 (b) constants of the module, the
only sorries are the two stubs.

**`Pattern.gen` is not degenerate.** `Toy.lean` (a) evaluates it by `rfl`/`decide` on a toy ℕ
environment for the `Nat.rec` succ rule: `ctx` of length 4, one self entry, `lhs = Nat.rec m z s
(succ n)`, `rhs = s n (Nat.rec m z s n)`, `rhsAbs = bvar 2 (bvar 1) (bvar 0 (bvar 4) (bvar 3)
(bvar 2) (bvar 1))`, `type = bvar 3 (succ (bvar 0))`, which is D4's `[self, n, s, z, motive] ⊢ s n
(self motive z s n) : motive (succ n)`. `GenNat.lean` (b) does the same on `docs/params/NatParams.lean`'s
actual environment, patterns and right-hand sides (ranks ℕ 0, zero/succ 1, rec 2), for both iota
rules, and checks that the output is the open body of `iotaSuccLam` (4 binders stripped) and
`iotaZeroLam` (3); a negative control with `self := []` fails. `Toy2.lean` (a's verifier) runs a
`Tree` environment whose node rule has two recursive calls and checks that they get separate self
variables, keyed by position.

## 1. The definitions and statements (attempt a; full text in `STATEMENTS-a.txt`)

```lean
structure PatGen where
  ctx : List VExpr      -- innermost first: ctor field types, then the head's first m binder types
  self : List VExpr     -- one closed type per same-rank bare-leaf occurrence (bvar 0 = first)
  lhs rhs rhsAbs type : VExpr

def VExpr.piTelescope : Nat → VExpr → Option (List VExpr × VExpr)   -- strip k syntactic Π-binders
def Pattern.gen (env : VEnv) (rank : Name → Nat) (classify : Name → Option Classification)
    (p : Pattern) (r : p.RHS) : Option PatGen :=
  match Pattern.selfTypes env (r.selfLeaves (Pattern.sameRank rank p.head)), p.genCore env classify with
  | some self, some (ctx, lhs, type) =>
    some { ctx, self, lhs, type
           rhs := r.toVExpr (fun _ => false) 0 0
           rhsAbs := r.toVExpr (Pattern.sameRank rank p.head) self.length 0 }
  | _, _ => none
-- genCore: delta `.const c` ↦ ([], const c params, ci.type); iota ↦ genIota, which needs
-- classify c' = some (.ctor n), piTelescope m ci.type = some (Hs, forallE (const I us) Bmaj) and
-- piTelescope n (ci'.type.instL us) = some (Fs, _), giving ctx = Fs.reverse ++ Hs.reverse,
-- lhs = (rec params) (bvar spine m, offset n) ((c' us) (bvar spine n)), type = Bmaj[c' us (bvar spine n)].

structure RankParams where       -- D4/D3 text for text; = R5's Params fields, E4's ParamsR
  rank : Name → Nat
  rank_ordered : ∀ k, (Params.env.below rank k).Ordered
  type_below : … → (Params.env.below rank (rank c)).IsType ci.uvars [] ci.type
  pat_rank : Params.Pat p r → .const c' us ∈ r.1.fixedLeaves → rank c' ≤ rank p.head
  pat_gen : Params.Pat p r → (Pattern.gen Params.env rank Params.classify p r.1).isSome
  pat_typed : Params.Pat p r → Pattern.gen … p r.1 = some g → Params.env.constants p.head = some ci →
    OnCtx (g.self ++ g.ctx) (fun Γ A => (Params.env.below rank (rank p.head)).IsType ci.uvars Γ A) ∧
    (Params.env.below rank (rank p.head)).HasType ci.uvars (g.self ++ g.ctx) g.rhsAbs (g.type.liftN g.self.length)
  pat_defeq : … → Params.env.IsDefEq ci.uvars g.ctx g.lhs g.rhs g.type
  pat_check : Params.Pat p r → r.2 = .true
  indTy_closed, ctor_fields_closed : as D3

def LR.WFIH (rank) (Γ₀) (k) : Prop := ∀ k' < k, ∀ {Γ M N A}, IsDefEqStrong (Params.env.below rank k') Γ M N A →
    ∀ {ρ n} {m a : WShape n}, LE_Interp ρ m.T M → LE_Interp ρ a.T A → m.HasType a → LR.Adequate Γ₀ Γ ρ M N A m a
def LR.ConstGoal (Γ₀) (ρ) (mT : TShape) (c) (ls) (ci) : Prop :=
  (∃ n, mT = (WShape.bot (n := n)).T) ∨
  ∃ (n : Nat) (m' a' : WShape n), mT ≤ m'.T ∧ m'.HasType a' ∧ LE_Interp ρ a'.T (mkInst ls ci.type) ∧
    ∀ {n'} (m a : WShape n'), m.T ≤ m'.T → LE_Interp ρ a.T (mkInst ls ci.type) → m.HasType a →
      (LR Γ₀).DefEq (.const c ls) (.const c ls) (mkInst ls ci.type) m a
def LR.LocalIH (rank) (Γ₀) (ρ₀) (c) (R : TShape → SExpr → Prop) : Prop :=
  ∀ m e, R m e → ∀ c' ls' ci', e = .const c' ls' → rank c' = rank c →
    Params.env.constants c' = some ci' → ls'.length = ci'.uvars → LR.ConstGoal Γ₀ ρ₀ m c' ls' ci'

theorem LR.const_local (RP : RankParams) {Γ₀} {k} {c₀} (WFIH : LR.WFIH RP.rank Γ₀ k) (hΓ₀ : ⊢ Γ₀)
    (hc₀ : RP.rank c₀ < k) : ∀ {ρ mT M} (_hM : LE_Interp ρ mT M) {c ls ci}, M = .const c ls →
      RP.rank c ≤ RP.rank c₀ → Params.env.constants c = some ci → ls.length = ci.uvars →
      LR.ConstGoal Γ₀ ρ mT c ls ci          -- proved; Fidelity.lean closes D4's literal spelling with it

theorem LR.const_spine (RP : RankParams) … (WFIH) (hc : RP.rank c < k) (h1) (h2) (LIH : LR.LocalIH RP.rank Γ₀ ρ₀ c R)
    (hC : LE_Interp.Const c ls R rargs mC) (hT : mkInst ls ci.type = Ts.foldr .forallE B) (hk : rargs.length = Ts.length)
    (hρ : (Valuation.ofRargs rargs).LE ρ) (W : LR.SubstWF Γ₀ σ σ' (Ts.reverse ++ Γ₀) ρ)
    (le : m.T ≤ mC) (hA : LE_Interp ρ a.T B) (hmem : m.HasType a) (tyV : …) :
    (LR Γ₀).DefEq ((openSpine c ls Ts.length).subst σ) ((openSpine c ls Ts.length).subst σ') (B.subst σ) m a
  -- sorry -- SORRY(E3): spine lemma (R9); pat_leaf_1a adds hP hMt hRHS hchk g hg hty hdef (PatLeafStmt2 + RP)
```

## 2. Decisions where D4 left a choice, and findings (both attempts agree unless said)

- **`RankParams` is an explicit argument** `(RP : RankParams)` of every lemma that needs the
  fields, so D4's `Params.rank` reads `RP.rank`; `WFIH`/`LocalIH` take `rank` explicitly as in
  `PatLeafStmt2.lean`. `const_spine`/`pat_leaf_1a` take `RP` in addition to `PatLeafStmt2`'s
  hypotheses (D4: the fields "enter E6 as section hypotheses"); `hty`/`hdef`/`hchk` are kept for
  fidelity though `RP` supplies them.
- **`const_local`'s WF induction is outside it**, as in D4's statement: the WF IH is a hypothesis
  (`LR.WFIH`), closed by `adequacy_rank` (R7) together with the other 13 cases (b's
  `adequacy_rank_wf` shows the shape). The WF-IH call inside is at `k' = rank c ≤ rank c₀ < k`,
  because `EnvStrongR.const` types `c`'s type in `below (rank c)`.
- **`rhs` is D4's primary definition** (paths ↦ `bvar (idx path)`, every fixed leaf kept, no self
  abstraction); (f) is then the `sel = fun _ => false` instance of (c) (a) or proved directly (b).
- **(c) with pointwise hypotheses on `σ`** instead of `selfσ ++ σ_p`: `σ j = mkInst ls e` for the
  j-th self leaf and `σ (g.self.length + idx path) = m2 path`; equivalent and more general. The
  self order is `fixedLeaves.filter sameRank`, left to right, `bvar 0` the first occurrence; D4's
  `idx` is the concrete `Pattern.pathIdx` (a) / `Pattern.genIdx` (b).
- **(a) is `Params`-free**; the link to `ctor_syn` (`Fs = Ts.map (·.instL us)`) is the separate
  `gen_head_ctor`. (b) and (d) take (a)'s data `(Hs, I, us, Bmaj)` as hypotheses (unique by
  Π-telescope injectivity). (b) comes in VExpr, substituted and `openSpine` forms; (e) from `hg`,
  in `mkInst` form, and from `Pat` via `pat_gen` (`RankParams.pat_arity`); (g) also in `SExpr`
  form via `mkInst_instL` (re-proved from `SelfType.lean`).
- **`Pattern.gen` also uses `classify`**: `genIota` requires `classify c' = some (.ctor n)` (D4
  passes `classify` but gives it no use); `pat_wf` guarantees it for every rule.
- **Stage 1a shows in `gen`**: the recursor's major domain must be syntactically `.const I us`
  and the constructor fields are `piTelescope n (ci'.type.instL us)` with no parameter
  instantiation. Right under `indTy_closed`/`ctor_fields_closed`; stage 2 needs a spine domain and
  parameter-instantiated fields.
- **Self abstraction is bare leaves only** (D4's wording, `pat_rank` likewise): a compound fixed
  leaf containing a same-rank constant is not abstracted, so `pat_typed` cannot hold for such a
  rule (`below (rank head)` excludes rank-head constants). Lean's recursor rules have bare
  recursive calls, so this is fine for E4; R5 should keep it in mind.
- **`EnvStrongR`** has no `Block`; `leaf` became `rhs` (D4 step 3), a `ctx` field types each
  context entry in its tail (for E6's `ihA`), `const` drops `ls.length`. Contexts stay closed and
  `weak_append` moves them to `… ++ Γ₀` at the use site (D4 step 3 as planned).
- **Added because the repo lacks them**: `openSpine`, `Valuation.ofRargs` (R8 items),
  `Pattern.RHS.fixedLeaves`, `piTelescope` lemmas, `foldr_forallE_inj`, `spine_subst`,
  `mkInst_foldl_app`, `SLevel.instV_params`, `Arity.varN_const`, the abbrev `Pattern.iota`
  (= `SimplePattern.toPattern`, `rfl`). Nothing the repo defines is redefined (verifier grep).
  `Lean4Lean.Verify`'s `OnCtx.of_append`/`VExpr.appN` are not importable from Experimental, so
  spines are `List.foldl VExpr.app` and the suffix step is an inline induction.

## 3. Verification output (verbatim, `Check.lean`, attempt a; `Check.out`)

```
'Lean4Lean.Pattern.gen_head' depends on axioms: [propext, Quot.sound]
'Lean4Lean.Pattern.gen_head_ctor' depends on axioms: [propext, Quot.sound]
'Lean4Lean.Pattern.gen_lhs' depends on axioms: [propext, Quot.sound]
'Lean4Lean.Pattern.gen_lhs_subst' depends on axioms: [propext, Quot.sound]
'Lean4Lean.Pattern.gen_lhs_openSpine' depends on axioms: [propext, Quot.sound]
'Lean4Lean.Pattern.RHS.toVExpr_subst' depends on axioms: [propext, Quot.sound]
'Lean4Lean.Pattern.gen_rhsAbs' depends on axioms: [propext, Quot.sound]
'Lean4Lean.Pattern.gen_type' depends on axioms: [propext, Quot.sound]
'Lean4Lean.Pattern.gen_arity' depends on axioms: [propext, Quot.sound]
'Lean4Lean.Pattern.gen_arity_mkInst' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.RankParams.pat_arity' depends on axioms: [propext, Quot.sound]
'Lean4Lean.Pattern.gen_rhs' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lean4Lean.Pattern.gen_self' depends on axioms: [propext, Quot.sound]
'Lean4Lean.Pattern.gen_self_mkInst' depends on axioms: [propext, Quot.sound]
'Lean4Lean.Pattern.gen_delta' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.EnvStrongR.of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lean4Lean.SExpr.IsDefEqStrong.forallE_inv'' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.IsDefEqStrong.telescope' depends on axioms: [propext, Quot.sound]
== roots: [Lean4Lean.SExpr.LR.const_local]
axioms reached (4):
  Classical.choice
  Quot.sound
  propext
  sorryAx
constants directly containing sorry (1):
  Lean4Lean.SExpr.LR.const_spine
== roots: [Lean4Lean.SExpr.LR.pat_leaf_1a]
axioms reached (4):
  Classical.choice
  Quot.sound
  propext
  sorryAx
constants directly containing sorry (1):
  Lean4Lean.SExpr.LR.pat_leaf_1a
== roots: [Lean4Lean.SExpr.LR.const_case]
axioms reached (4):
  Classical.choice
  Quot.sound
  propext
  sorryAx
constants directly containing sorry (1):
  Lean4Lean.SExpr.LR.const_spine
== roots: [Lean4Lean.Pattern.gen, Lean4Lean.SExpr.EnvStrongR.of_params]
axioms reached (3):
  Classical.choice
  Quot.sound
  propext
constants directly containing sorry (0):
```

## 4. Where it lands

- **R5** (`SExpr.lean` before `class Params`, 98 at `3bccfa8`): `piTelescope`, `PatGen`,
  `pathIdx`/`genIdx`, `RHS.fixedLeaves`/`selfLeaves`/`toVExpr`, `sameRank`, `constType`,
  `selfTypes`, `bvarSpine`, `genIota`, `genCore`, `Pattern.gen`; after it the spec lemmas and the
  ten `Params` fields exactly as `RankParams`. E4 pins the field list first.
- **R7**: the WF induction on `k` (`adequacy_rank_wf`'s shape) around the 14 cases.
- **R8**: `EnvStrongR`, `openSpine`, `Valuation.ofRargs`, `WFIH`/`ConstGoal`/`LocalIH`,
  `const_local`, `const_spine` stated, `const_case` wiring.
- **R9/R10/E6**: the `const_spine` and `pat_leaf_1a` statements as here (with `RP`).

## 5. Rebuilding

The module is `Lean4Lean/Experimental/E3/Measure7.lean` in a built copy of `3bccfa8`
(`lake build Lean4Lean.Experimental.E3.Measure7`, ~3 s after the tree is built), then
`lake env lean Check.lean`, `Toy.lean`, `Fidelity.lean`, `Toy2.lean` (a) or `GenNat.lean` (b,
against `Measure7-b.lean`) from the copy's root. The run used `/tmp/utt-snap13a` and
`/tmp/utt-snap13b` (scratch `/tmp/utt-exp/e3/{a,b}`).
