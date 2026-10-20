# Experiment E5 (λ-wrapped rules): PASS

2026-10-20. Plan: `../../PLAN.md` §1 D5 ("`extra_patV`, restated for λ-wrapped rules") and
§2 row E5. Base: commit `3bccfa8` (typed reductions, stage-1a clause and the environment-indexed
strong judgment all landed). Run: two independent Opus attempts on fresh snapshots, each checked
by an independent adversarial verifier (clean rebuild, grep for cheats, axioms, tracer rooted at
every top-level declaration, statement diffs against the plan files and the repo). Verdicts:
both pass, first round.

## 0. Outcome

**D5's λ-`extra_patV` is sufficient as stated; no amendment is needed.** With it as an explicit
hypothesis `hlam : ExtraPatVLam` (verbatim from `../ExtraLamStmt.lean`, which is verbatim D5):

- `T.strongSoundS_extra_lam`, the `extra` case of `LE_Interp.strongSoundS` for a λ-rule, is
  proved with the statement of `ExtraLamStmt.lean:25-29` byte for byte (`Check.lean` closes the
  plan's statement with it). Axioms `[propext, Classical.choice, Quot.sound]`.
- `T.LR.adequacy`, a copy of `ShapeLogRelAdequacy.lean:9-562` whose `extra` case is re-proved
  for λ-rules without `Params.extra_pat` or `Params.extra_patV`, has the repo's statement plus the
  one hypothesis `hlam`. Its tracer block is the repo's: the `const` case is the only sorry.
- `T.extra_pat_lam`, the `SExpr` translation of the λ-field (the lemma R6 lands in place of
  `Params.extra_pat`), is sorry-free, and at `Δ = []` its pattern conjunct is exactly
  `Params.extra_pat`'s conclusion (an `example` in `Check.lean`).
- Every conjunct of the field is used: the λ-shape equalities (both theorems); `OnCtx Δ.reverse
  IsType` (level well-formedness for `IsDefEq.mkS`, and `⊢ Δ.reverse ++ Γ₀`, which types the
  binders for the λ-congruences and `Ctx.SubstEq.cons`); the open equation (types every beta
  layer and the base step); `r.2.OK` at `Δ.reverse ++ Γ`, used at `Γ := Γ₀` (`WHRed.extra` on the
  open instance); `Pat`, `Matches`, `R = r.1.apply` (both theorems).

Both attempts reached the same structure independently; they differ only in the spelling of
`extra_pat_lam`'s context conjunct and in the name of the adequacy engine (§1).

## 1. The statements (`LamRules.lean`, `LamAdequacy.lean`; attempt a)

```lean
def ExtraPatVLam : Prop :=            -- verbatim ExtraLamStmt.lean / PLAN D5
  ∀ {df : VDefEq} {ls : List VLevel} {Γ : List VExpr},
    Params.env.defeqs df → (∀ l ∈ ls, l.WF Params.univs) → ls.length = df.uvars →
    ∃ (Δ : List VExpr) (L R T : VExpr),
      df.lhs.instL ls = Δ.foldr .lam L ∧ df.rhs.instL ls = Δ.foldr .lam R ∧
      df.type.instL ls = Δ.foldr .forallE T ∧
      OnCtx Δ.reverse (Params.env.IsType Params.univs) ∧
      Params.env.IsDefEq Params.univs Δ.reverse L R T ∧
      ∃ p r m1 m2, Params.Pat p r ∧ p.Matches L m1 m2 ∧
        r.2.OK (Params.env.IsDefEqU Params.univs (Δ.reverse ++ Γ)) m1 m2 ∧ R = r.1.apply m1 m2

theorem T.extra_pat_lam (hlam : ExtraPatVLam) (Γ : List SExpr) {df : VDefEq} {ls : List SLevel}
    (h1 : Params.env.defeqs df) (h2 : ls.length = df.uvars) :
    ∃ (Δ : List SExpr) (L R T : SExpr),
      .mkInst ls df.lhs = Δ.foldr .lam L ∧ .mkInst ls df.rhs = Δ.foldr .lam R ∧
      .mkInst ls df.type = Δ.foldr .forallE T ∧
      (⊢ Γ → ⊢ Δ.reverse ++ Γ) ∧                       -- attempt b: per-binder typings, below
      Δ.reverse ++ Γ ⊢ L ≡ R : T ∧
      ∃ p r m1 m2 dfs, Params.Pat p r ∧ p.MatchesS L m1 m2 ∧
        (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 ∧
        (∀ a b A, (A, a, b) ∈ dfs → Δ.reverse ++ Γ ⊢ a ≡ b : A) ∧
        R = r.1.applyS m1 m2

theorem T.strongSoundS_extra_lam (hlam : ExtraPatVLam) {df : VDefEq} {ls : List SLevel}
    {Γ : List SExpr} (h1 : Params.env.defeqs df) (h2 : ls.length = df.uvars)
    (ih1 : StrongSoundEq Γ (.mkInst ls df.lhs) (.mkInst ls df.lhs) (.mkInst ls df.type))
    (ih2 : StrongSoundEq Γ (.mkInst ls df.rhs) (.mkInst ls df.rhs) (.mkInst ls df.type)) :
    StrongSoundEq Γ (.mkInst ls df.lhs) (.mkInst ls df.rhs) (.mkInst ls df.type)

theorem T.LR.adequacy (hlam : ExtraPatVLam) (hΓ : ⊢ Γ) (H : Γ ⊢ M ≡ N : A)
    (hM : LE_Interp ρ m.T M) (hA : LE_Interp ρ a.T A) (hmem : m.HasType a) :
    Adequate (n := n) Γ₀ Γ ρ M N A m a

-- the extra-case engine (attempt b calls it LR.lamTel_defEq, with σ for τ and the per-binder form)
theorem T.LR.lamRule {Γ₀ : List SExpr} (hΓ₀ : ⊢ Γ₀) {T : SExpr} :
    ∀ (Δ : List SExpr) {Ξ : List SExpr} {τ : Subst} {L R : SExpr},
    ⊢ Δ.reverse ++ Ξ → Δ.reverse ++ Ξ ⊢ L ≡ R : T → Δ.reverse ++ Ξ ⊢ L ⤳ R →
    Ctx.SubstEq Γ₀ τ τ Ξ → ∀ {n} {m a : WShape n},
    (LR Γ₀).DefEq ((Δ.foldr .lam L).subst τ) ((Δ.foldr .lam L).subst τ) ((Δ.foldr .forallE T).subst τ) m a →
    (LR Γ₀).DefEq ((Δ.foldr .lam R).subst τ) ((Δ.foldr .lam R).subst τ) ((Δ.foldr .forallE T).subst τ) m a →
    (LR Γ₀).DefEq ((Δ.foldr .lam L).subst τ) ((Δ.foldr .lam R).subst τ) ((Δ.foldr .forallE T).subst τ) m a
```

Attempt b's `extra_pat_lam` (`LamRules-b.lean:81`) states the context conjunct as the binder
typings `∀ Δ₁ A Δ₂, Δ = Δ₁ ++ A :: Δ₂ → ∃ u, Δ₁.reverse ++ Γ ⊢ A : .sort u` (the `SExpr` form of
`OnCtx Δ.reverse IsType`), vacuous at `Δ = []`. Either form serves R6; b's is what the
λ-congruence consumes directly, a's is shorter.

## 2. What the proofs do (both attempts; departures from D5's sketch)

- **`typed_beta_rule` is not used.** The `whr` field needs each side's own reduct, `(λA.F)x ≡
  F[x]` and `(λA.G)x ≡ G[x]`; both come from `typed_beta_rhs` applied to the two reflexive halves
  of the (closed-up, substituted) open equation. `typed_beta_rule`'s cross step `(λA.L)a ≡ R[a]`
  is what no `LogRel` field takes. With more than one binder the reduct of a layer is again a λ,
  so each layer is a typed beta step only; the `extra` step happens once, at the open body.
- **Beta layers are typed from the λ-closure of the open equation** over the binders still to
  come (`lamDF_foldr` / `lamTel_typed`, which need the telescope's well-formedness), with the
  arguments so far substituted in by `IsDefEq.subst` along a `Ctx.SubstEq` built with `.cons`
  from each argument's typing `Γ₀ ⊢ x : A[τ]`, which `LamDefEq` supplies. The case's own `σ`
  enters through `W.toSubstEq`, so the old closedness rewrites (`mkInstS.subst_eq`) are gone.
- **`WHRed.extra` on the open instance** is taken in `Δ.reverse ++ Γ₀` with the side conditions
  from `extra_pat_lam` at `Γ := Γ₀`, then moved into `Γ₀` by `WHRed.subst` with the substituted
  open equation as its typed base step. `IsDefEq.extra` is not used.
- **`strongSoundS_extra_lam` needs neither the open equation nor the side conditions**: only the
  λ-shape equalities, `Pat`, `MatchesS`, `R = applyS` and the two IHs. It inverts the
  `StrongSoundCore.lam` layers, keeps body types tied to the declared codomain with
  `SoundEq.forallE_inv`, runs the old argument (`ShapeLogRel.lean:5233-5260`, factored out as
  `soundEq_pat`) on the open body, and closes back up with a `SoundEq.lam` congruence, the one
  place `LE_Interp.lam` is used.
- **The λ-rule `extra` case feeds `hM` to the rhs through `T.strongSoundS_extra_lam`** (with IHs
  from the repo's `LE_Interp.strongSoundS Hl`/`Hr`) instead of `LE_Interp.soundS (.extra …)`.
- **Reach.** `T.LR.adequacy` still reaches `Params.extra_patV`, through exactly one path:
  the repo's `LE_Interp.strongSoundS` (its `extra` case), which every case uses via `soundS`
  (`Reach.lean`, output in §3). `T.LR.lamRule`, `T.strongSoundS_extra_lam` and `T.extra_pat_lam`
  do not reach it. **R6 must swap `strongSoundS`'s `extra` case for `strongSoundS_extra_lam`**;
  then the old field is off the adequacy route entirely.
- `hlam` is also threaded into `forallE_whRed_l`, `forallE_inv`, `sort_forallE_inv`, `sort_inv`
  (they call `LR.adequacy`). The copy needs `open Lean4Lean.SExpr.LR` for `SubstWF`,
  `DefEq.lift`, `TyDefEq.lift` to resolve inside `T.LR.*`. Otherwise the diff against
  `ShapeLogRelAdequacy.lean:9-562` is the new λ lemmas and the replaced `extra` case.

## 3. Verification output (verbatim, `Check.lean` and `Reach.lean`, attempt a)

```
'Lean4Lean.SExpr.T.extra_pat_lam' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.T.strongSoundS_extra_lam' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lean4Lean.SExpr.typed_beta_rule' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.typed_beta_rhs' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.T.LR.lamRule' depends on axioms: [propext, Classical.choice, Quot.sound]
== roots: [Lean4Lean.SExpr.T.LR.adequacy]
axioms reached (4):
  Classical.choice
  Quot.sound
  propext
  sorryAx
constants directly containing sorry (1):
  Lean4Lean.SExpr.T.LR.adequacy
== roots: [Lean4Lean.SExpr.T.strongSoundS_extra_lam]
axioms reached (3):
  Classical.choice
  Quot.sound
  propext
constants directly containing sorry (0):
Lean4Lean.SExpr.T.LR.adequacy reaches Lean4Lean.Params.extra_patV: [Lean4Lean.Params.extra_patV, Lean4Lean.SExpr.Params.extra_pat, Lean4Lean.SExpr.LE_Interp.strongSoundS, Lean4Lean.SExpr.T.LR.adequacy]
Lean4Lean.SExpr.T.LR.lamRule does NOT reach Lean4Lean.Params.extra_patV
Lean4Lean.SExpr.T.strongSoundS_extra_lam does NOT reach Lean4Lean.Params.extra_patV
Lean4Lean.SExpr.T.extra_pat_lam does NOT reach Lean4Lean.Params.extra_patV
```

Attempt b's verifier additionally enumerated all constants of both modules (22 and 83) from the
module data and found the `const`-case sorry to be the only one, and proved
`type_of% @plan_strongSoundS_extra_lam = type_of% @T.strongSoundS_extra_lam := rfl`.
The only sorry warning in either module is `LamAdequacy.lean:294:8` (`T.LR.adequacy`, the
`const` case at line 343, copied verbatim from `ShapeLogRelAdequacy.lean:198`).

## 4. What R6 lands (new lemmas, none in the repo)

From `LamRules.lean` (namespace `SExpr.T`): `mk_foldr_lam`, `mk_foldr_forallE`,
`onCtx_append_levelWF`, `ctxWF_append_mk`, `extra_pat_lam`, `SoundEq.lam` (λ-congruence for
`SoundEq`), `soundEq_pat` (`ShapeLogRel.lean:5233-5260` as a lemma), `SoundEq.lam_foldr`,
`strongSoundS_extra_lam`. From `LamAdequacy.lean`: `typed_beta_rule`, `typed_beta_rhs` (verbatim
`../LamRuleTyped.lean`), `ctxWF_of_append`, `lamDF_foldr`, `tyDefEq_lam_l`, `lr0_lam_of`,
`lrs_lam_of`, `LR.lamRule`, and the new `extra` case. Attempt b's equivalents: `onCtx_levelWF`,
`onCtx_mid`, `isDefEq_append_mkS`, `soundEq_lam`, `soundEq_foldr_lam`, `binders_cons`,
`lamTel_typed`, `LR.lamTel_defEq`. R6 also replaces `Params.extra_patV` by the λ-field (then
`ExtraPatVLam` is the field and `hlam` disappears), re-derives `Params.extra_pat` as
`extra_pat_lam` at `Δ = []`, swaps `strongSoundS`'s `extra` case (§2, reach), and retires
`docs/params/Schema.lean`'s `no_lam_rule` (false by design).

## 5. Rebuilding

The modules are `Lean4Lean/Experimental/E5/{LamRules,LamAdequacy}.lean` in a built copy of
`3bccfa8`; `lake build Lean4Lean.Experimental.E5.LamRules Lean4Lean.Experimental.E5.LamAdequacy`,
then `lake env lean Check.lean` and `lake env lean Reach.lean` from the copy's root. The run
used `/tmp/utt-snap14a` (attempt a) and `/tmp/utt-snap14b` (attempt b; scratch in
`/tmp/utt-exp/e5/{a,b}`). In a snapshot without `.git`, the first `lake env lean` re-clones
`batteries` at the same revision (harmless, ~17 s).
