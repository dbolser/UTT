import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! E3 (docs/const-case/PLAN.md §2 row E3, §1 D4): `Pattern.gen` as a function with its spec
lemmas (a)-(g), the D4/D3 `Params`-field package `RankParams`, `EnvStrongR` and its
`of_params`, the measure's `LR.WFIH`/`LR.ConstGoal`/`LR.LocalIH`, the statements of
`LR.const_spine` (R9) and `LR.pat_leaf_1a` (E6/R10), and `LR.const_local` (proved, up to the
`const_spine` stub). Built over the repo's `IsDefEqStrong E`, `VEnv.below`, `mkSE`,
`CtorProviderE.synE`, `weak0`, `soundSE` (HEAD `3bccfa8`).

Deliberate sorries (2): the bodies of `LR.const_spine` (`-- SORRY(E3): spine lemma (R9)`) and
`LR.pat_leaf_1a` (`-- SORRY(E3): pat leaf (E6/R10)`).

Layout: Part 1 (`namespace Lean4Lean`, no `Params`): `VExpr.piTelescope`, `PatGen`,
`Pattern.gen` and the `Params`-free spec lemmas (a) `gen_head`, (b) `gen_lhs`, (d) `gen_type`,
(e) `gen_arity`, (g) `gen_self`. Part 2 (`namespace Lean4Lean.SExpr`, `variable [Params]`): the
`SExpr` forms (b) `gen_lhs_subst`, (c) `RHS.toVExpr_subst`/`gen_rhsAbs`, (f) `gen_rhs`,
(g) `gen_self_mkInst`, (e) `gen_arity_mkInst`, (a) with `ctor_syn` `gen_head_ctor`; then
`RankParams`, `EnvStrongR`, and the measure. -/
namespace Lean4Lean

/-! # Part 1: `Pattern.gen` (VExpr level, before `class Params` in R5)

## Syntactic Π-telescopes -/

/-- Strip `k` syntactic Π-binders: `piTelescope k e = some (Hs, B)` iff `e = Hs.foldr .forallE B`
with `Hs.length = k` (outermost binder first). -/
def VExpr.piTelescope : Nat → VExpr → Option (List VExpr × VExpr)
  | 0, e => some ([], e)
  | k+1, .forallE A B => (B.piTelescope k).map fun r => (A :: r.1, r.2)
  | _+1, _ => none

theorem VExpr.piTelescope_eq_some : ∀ {k : Nat} {e : VExpr} {Hs : List VExpr} {B : VExpr},
    VExpr.piTelescope k e = some (Hs, B) → Hs.length = k ∧ e = Hs.foldr .forallE B
  | 0, e, Hs, B, h => by
    simp only [piTelescope, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | k+1, .forallE A B', Hs, B, h => by
    simp only [piTelescope, Option.map_eq_some_iff] at h
    obtain ⟨⟨Hs', B''⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨h3, rfl⟩ := piTelescope_eq_some h1
    exact ⟨by simp [h3], rfl⟩
  | _+1, .bvar _, _, _, h | _+1, .sort _, _, _, h | _+1, .const .., _, _, h
  | _+1, .app .., _, _, h | _+1, .lam .., _, _, h => nomatch h

theorem VExpr.piTelescope_foldr : ∀ (Hs : List VExpr) (B : VExpr),
    VExpr.piTelescope Hs.length (Hs.foldr .forallE B) = some (Hs, B)
  | [], _ => rfl
  | A :: Hs, B => by simp [piTelescope, piTelescope_foldr Hs B]

theorem VExpr.foldr_forallE_inj : ∀ {Hs Hs' : List VExpr} {B B' : VExpr}, Hs.length = Hs'.length →
    Hs.foldr .forallE B = Hs'.foldr .forallE B' → Hs = Hs' ∧ B = B'
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | A :: Hs, A' :: Hs', _, _, hl, h => by
    simp only [List.foldr_cons, VExpr.forallE.injEq] at h
    obtain ⟨h1, h2⟩ := foldr_forallE_inj (by simpa using hl) h.2
    exact ⟨by rw [h.1, h1], h2⟩

theorem VExpr.instL_foldr_forallE (us : List VLevel) : ∀ (Hs : List VExpr) (B : VExpr),
    (Hs.foldr .forallE B).instL us = (Hs.map (·.instL us)).foldr .forallE (B.instL us)
  | [], _ => rfl
  | A :: Hs, B => by simp [VExpr.instL, instL_foldr_forallE us Hs B]

/-! ## Pattern shapes, path indices, RHS translation -/

/-- Recognise `varN (const c) k` (`asVarN_varN`, `eq_varN_of_asVarN`). -/
def Pattern.asVarN : Pattern → Option (Name × Nat)
  | .const c => some (c, 0)
  | .var f => f.asVarN.map fun r => (r.1, r.2 + 1)
  | .app .. => none

theorem Pattern.asVarN_varN (c : Name) : ∀ n, (Pattern.varN (.const c) n).asVarN = some (c, n)
  | 0 => rfl
  | n+1 => by simp [Pattern.varN, asVarN, asVarN_varN c n]

theorem Pattern.eq_varN_of_asVarN : ∀ {p : Pattern} {c : Name} {n : Nat},
    p.asVarN = some (c, n) → p = .varN (.const c) n
  | .const c', c, n, h => by
    simp only [asVarN, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | .var f, c, n, h => by
    simp only [asVarN, Option.map_eq_some_iff] at h
    obtain ⟨⟨c', k⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2
    rw [eq_varN_of_asVarN h1]; rfl
  | .app .., _, _, h => nomatch h

theorem Pattern.head_varN (c : Name) : ∀ n, (Pattern.varN (.const c) n).head = c
  | 0 => rfl
  | n+1 => head_varN c n

/-- The number of pattern variables (paths). -/
def Pattern.nvars : Pattern → Nat
  | .const _ => 0
  | .app f a => f.nvars + a.nvars
  | .var f => f.nvars + 1

theorem Pattern.nvars_varN (p : Pattern) : ∀ n, (p.varN n).nvars = p.nvars + n
  | 0 => rfl
  | n+1 => by simp [Pattern.varN, nvars, nvars_varN p n]; omega

/-- `Pattern.gen`'s path ↦ context-index map (`idx` of D4): the paths numbered innermost first,
the last argument being `0`. For `app (varN (const rec) m) (varN (const c') n)` it sends
`inl (some^i none) ↦ n + i` and `inr (some^i none) ↦ i` (`nvars_varN`). -/
def Pattern.pathIdx : (p : Pattern) → p.Path → Nat
  | .const _, x => Empty.elim x
  | .app f a, x => Sum.elim (fun y => f.pathIdx y + a.nvars) (fun y => a.pathIdx y) x
  | .var f, x => Option.elim x 0 (fun y => f.pathIdx y + 1)

@[simp] theorem Pattern.pathIdx_inl {f a : Pattern} (x : f.Path) :
    (Pattern.app f a).pathIdx (.inl x) = f.pathIdx x + a.nvars := rfl
@[simp] theorem Pattern.pathIdx_inr {f a : Pattern} (x : a.Path) :
    (Pattern.app f a).pathIdx (.inr x) = a.pathIdx x := rfl
@[simp] theorem Pattern.pathIdx_none {f : Pattern} : (Pattern.var f).pathIdx none = 0 := rfl
@[simp] theorem Pattern.pathIdx_some {f : Pattern} (x : f.Path) :
    (Pattern.var f).pathIdx (some x) = f.pathIdx x + 1 := rfl

/-- The closed leaves of an RHS, left to right (Measure6.lean:69). -/
def Pattern.RHS.fixedLeaves {p : Pattern} : p.RHS → List VExpr
  | .fixed e _ => [e]
  | .var _ => []
  | .app f a => f.fixedLeaves ++ a.fixedLeaves

/-- The leaf occurrences selected by `sel`, in `fixedLeaves` order. -/
def Pattern.RHS.selfLeaves {p : Pattern} (sel : VExpr → Bool) (r : p.RHS) : List VExpr :=
  r.fixedLeaves.filter sel

/-- The RHS as an open term, per occurrence: the `i`-th selected leaf occurrence (counted from
`j`) becomes `bvar (j + i)`, `var path` becomes `bvar (k + pathIdx path)`, other leaves stay.
Keyed by RHS position, not by `VExpr` (the patleaf refuter's `node l r` fix). -/
def Pattern.RHS.toVExpr {p : Pattern} (sel : VExpr → Bool) (k : Nat) : p.RHS → Nat → VExpr
  | .fixed e _, j => if sel e then .bvar j else e
  | .var path, _ => .bvar (k + p.pathIdx path)
  | .app f a, j => .app (f.toVExpr sel k j) (a.toVExpr sel k (j + (f.selfLeaves sel).length))

/-- A bare-constant leaf of the same rank as the head `h` (abstracted as a self variable). -/
def Pattern.sameRank (rank : Name → Nat) (h : Name) : VExpr → Bool
  | .const c' _ => rank c' == rank h
  | _ => false

theorem Pattern.sameRank_eq_true {rank : Name → Nat} {h : Name} {e : VExpr} :
    Pattern.sameRank rank h e = true ↔ ∃ c' us, e = .const c' us ∧ rank c' = rank h := by
  cases e <;> simp [sameRank]

/-- The type of a bare constant at its levels. -/
def VExpr.constType (env : VEnv) : VExpr → Option VExpr
  | .const c us => (env.constants c).map fun ci => ci.type.instL us
  | _ => none

/-- The self types of a list of bare-constant occurrences (`none` if one is not a constant of `env`). -/
def Pattern.selfTypes (env : VEnv) : List VExpr → Option (List VExpr)
  | [] => some []
  | e :: es =>
    match e.constType env, selfTypes env es with
    | some T, some Ts => some (T :: Ts)
    | _, _ => none

theorem Pattern.selfTypes_eq_some {env : VEnv} : ∀ {es Ts : List VExpr},
    Pattern.selfTypes env es = some Ts → Ts.length = es.length ∧
      ∀ (j : Nat) (e : VExpr), es[j]? = some e → ∃ (c' : Name) (us : List VLevel) (ci' : VConstant),
        e = .const c' us ∧ env.constants c' = some ci' ∧ Ts[j]? = some (ci'.type.instL us)
  | [], Ts, h => by
    simp only [selfTypes, Option.some.injEq] at h; subst h
    exact ⟨rfl, fun _ _ h => by simp at h⟩
  | e :: es, Ts, h => by
    simp only [selfTypes] at h
    split at h
    · next T Ts' h1 h2 =>
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨ih1, ih2⟩ := selfTypes_eq_some h2
      refine ⟨by simp [ih1], fun j e' he => ?_⟩
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at he; subst he
        cases e with
        | const c' us =>
          simp only [VExpr.constType, Option.map_eq_some_iff] at h1
          obtain ⟨ci', h3, rfl⟩ := h1
          exact ⟨c', us, ci', rfl, h3, rfl⟩
        | _ => simp [VExpr.constType] at h1
      | succ j => simpa using ih2 j e' (by simpa using he)
    · cases h

/-- `h (bvar (off+k-1)) … (bvar off)`. -/
def VExpr.bvarSpine (h : VExpr) (k off : Nat) : VExpr :=
  ((List.range k).reverse.map fun i => VExpr.bvar (off + i)).foldl .app h

/-! ## `PatGen` and `Pattern.gen` -/

/-- A rule's generated pattern context and open equation (PLAN D4). -/
structure PatGen where
  /-- innermost first: the ctor field types, then the head's first `m` binder types -/
  ctx : List VExpr
  /-- one closed type per same-rank bare-leaf occurrence of the RHS (innermost = first occurrence) -/
  self : List VExpr
  /-- the generic LHS, in `ctx` -/
  lhs : VExpr
  /-- the RHS, paths ↦ `bvar (pathIdx path)`, every fixed leaf kept; in `ctx` -/
  rhs : VExpr
  /-- the RHS with the same-rank bare leaves abstracted; in `self ++ ctx` -/
  rhsAbs : VExpr
  /-- the type of `lhs`, in `ctx` -/
  type : VExpr

/-- The iota part: `rec`'s type has `m` syntactic binders then a major `Π (_ : const I us)`,
`c'` is a constructor of arity `n` whose type (at `us`) has `n` syntactic binders. -/
def Pattern.genIota (env : VEnv) (classify : Name → Option Classification)
    (rec : Name) (m : Nat) (c' : Name) (n : Nat) : Option (List VExpr × VExpr × VExpr) :=
  match env.constants rec, env.constants c', classify c' with
  | some ci, some ci', some (.ctor n') =>
    match ci.type.piTelescope m with
    | some (Hs, .forallE (.const _ us) Bmaj) =>
      match (ci'.type.instL us).piTelescope n with
      | some (Fs, _) =>
        if n' = n then
          some (Fs.reverse ++ Hs.reverse,
            .app (VExpr.bvarSpine (.const rec (VLevel.params ci.uvars)) m n)
              (VExpr.bvarSpine (.const c' us) n 0),
            (Bmaj.liftN n 1).inst (VExpr.bvarSpine (.const c' us) n 0))
        else none
      | none => none
    | _ => none
  | _, _, _ => none

/-- `(ctx, lhs, type)` for the two `SimplePattern` shapes; `none` for every other pattern. -/
def Pattern.genCore (env : VEnv) (classify : Name → Option Classification) :
    Pattern → Option (List VExpr × VExpr × VExpr)
  | .const c => (env.constants c).map fun ci => ([], .const c (VLevel.params ci.uvars), ci.type)
  | .app f a =>
    match f.asVarN, a.asVarN with
    | some (rec, m), some (c', n) => Pattern.genIota env classify rec m c' n
    | _, _ => none
  | .var _ => none

/-- `Pattern.gen` (item R5): a function, so it leaves no junk witnesses
(`PatTypedDegenerate.lean`, `JunkGen.lean`). -/
def Pattern.gen (env : VEnv) (rank : Name → Nat) (classify : Name → Option Classification)
    (p : Pattern) (r : p.RHS) : Option PatGen :=
  match Pattern.selfTypes env (r.selfLeaves (Pattern.sameRank rank p.head)),
    p.genCore env classify with
  | some self, some (ctx, lhs, type) =>
    some { ctx, self, lhs, type
           rhs := r.toVExpr (fun _ => false) 0 0
           rhsAbs := r.toVExpr (Pattern.sameRank rank p.head) self.length 0 }
  | _, _ => none

theorem Pattern.gen_eq_some {env : VEnv} {rank : Name → Nat} {classify : Name → Option Classification}
    {p : Pattern} {r : p.RHS} {g : PatGen} (hg : Pattern.gen env rank classify p r = some g) :
    Pattern.selfTypes env (r.selfLeaves (Pattern.sameRank rank p.head)) = some g.self ∧
    p.genCore env classify = some (g.ctx, g.lhs, g.type) ∧
    g.rhs = r.toVExpr (fun _ => false) 0 0 ∧
    g.rhsAbs = r.toVExpr (Pattern.sameRank rank p.head) g.self.length 0 := by
  unfold Pattern.gen at hg
  split at hg
  · next h1 h2 => cases hg; exact ⟨h1, h2, rfl, rfl⟩
  · cases hg

theorem Pattern.genIota_eq_some {env : VEnv} {classify : Name → Option Classification}
    {rec c' : Name} {m n : Nat} {ctx : List VExpr} {lhs type : VExpr}
    (h : Pattern.genIota env classify rec m c' n = some (ctx, lhs, type)) :
    ∃ (ci ci' : VConstant) (Hs : List VExpr) (I : Name) (us : List VLevel) (Bmaj : VExpr)
      (Fs : List VExpr) (R' : VExpr),
      env.constants rec = some ci ∧ env.constants c' = some ci' ∧
      classify c' = some (.ctor n) ∧
      ci.type.piTelescope m = some (Hs, .forallE (.const I us) Bmaj) ∧
      (ci'.type.instL us).piTelescope n = some (Fs, R') ∧
      ctx = Fs.reverse ++ Hs.reverse ∧
      lhs = .app (VExpr.bvarSpine (.const rec (VLevel.params ci.uvars)) m n)
        (VExpr.bvarSpine (.const c' us) n 0) ∧
      type = (Bmaj.liftN n 1).inst (VExpr.bvarSpine (.const c' us) n 0) := by
  unfold Pattern.genIota at h
  split at h
  · next ci ci' n' h1 h2 h3 =>
    split at h
    · next Hs I us Bmaj h4 =>
      split at h
      · next Fs R' h5 =>
        split at h
        · next hn =>
          subst hn
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨ci, ci', Hs, I, us, Bmaj, Fs, R', h1, h2, h3, h4, h5, rfl, rfl, rfl⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-! ## Spec lemmas (a), (b), (d), (e), (g) -/

/-- The iota pattern `rec x₁ … xₘ (c' z₁ … zₙ)` (`SimplePattern.iota`, Pattern.lean:240). -/
abbrev Pattern.iota (rec : Name) (m : Nat) (c' : Name) (n : Nat) : Pattern :=
  .app (.varN (.const rec) m) (.varN (.const c') n)

theorem Pattern.iota_eq_toPattern (rec : Name) (m : Nat) (c' : Name) (n : Nat) :
    Pattern.iota rec m c' n = (SimplePattern.iota rec m c' n).toPattern := rfl

theorem Pattern.genCore_iota {env : VEnv} {classify : Name → Option Classification}
    {rec c' : Name} {m n : Nat} {x : List VExpr × VExpr × VExpr}
    (h : (Pattern.iota rec m c' n).genCore env classify = some x) :
    Pattern.genIota env classify rec m c' n = some x := by
  simpa [genCore, asVarN_varN] using h

/-- Common unpacking of `hg` for the iota shape. -/
theorem Pattern.gen_iota {env : VEnv} {rank : Name → Nat} {classify : Name → Option Classification}
    {rec c' : Name} {m n : Nat} {r : (Pattern.iota rec m c' n).RHS} {g : PatGen}
    (hg : Pattern.gen env rank classify (.iota rec m c' n) r = some g) :
    ∃ (ci ci' : VConstant) (Hs : List VExpr) (I : Name) (us : List VLevel) (Bmaj : VExpr)
      (Fs : List VExpr) (R' : VExpr),
      env.constants rec = some ci ∧ env.constants c' = some ci' ∧
      classify c' = some (.ctor n) ∧
      Hs.length = m ∧ ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj) ∧
      Fs.length = n ∧ ci'.type.instL us = Fs.foldr .forallE R' ∧
      g.ctx = Fs.reverse ++ Hs.reverse ∧
      g.lhs = .app (VExpr.bvarSpine (.const rec (VLevel.params ci.uvars)) m n)
        (VExpr.bvarSpine (.const c' us) n 0) ∧
      g.type = (Bmaj.liftN n 1).inst (VExpr.bvarSpine (.const c' us) n 0) := by
  obtain ⟨-, h2, -⟩ := Pattern.gen_eq_some hg
  obtain ⟨ci, ci', Hs, I, us, Bmaj, Fs, R', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    Pattern.genIota_eq_some (Pattern.genCore_iota h2)
  obtain ⟨l4, e4⟩ := VExpr.piTelescope_eq_some h4
  obtain ⟨l5, e5⟩ := VExpr.piTelescope_eq_some h5
  exact ⟨ci, ci', Hs, I, us, Bmaj, Fs, R', h1, h2, h3, l4, e4, l5, e5, h6, h7, h8⟩

/-- Uniqueness of the recursor-type data `(Hs, I, us, Bmaj)` at a fixed length. -/
theorem VExpr.foldr_forallE_major_inj {Hs Hs' : List VExpr} {I I' : Name} {us us' : List VLevel}
    {B B' : VExpr} (hl : Hs.length = Hs'.length)
    (h : Hs.foldr VExpr.forallE (.forallE (.const I us) B) =
      Hs'.foldr VExpr.forallE (.forallE (.const I' us') B')) :
    Hs = Hs' ∧ I = I' ∧ us = us' ∧ B = B' := by
  obtain ⟨h1, h2⟩ := VExpr.foldr_forallE_inj hl h
  simp only [VExpr.forallE.injEq, VExpr.const.injEq] at h2
  exact ⟨h1, h2.1.1, h2.1.2, h2.2⟩

/-- Spec lemma (a), `gen_head`. -/
theorem Pattern.gen_head {env : VEnv} {rank : Name → Nat} {classify : Name → Option Classification}
    {rec c' : Name} {m n : Nat} {r : (Pattern.iota rec m c' n).RHS} {g : PatGen} {ci : VConstant}
    (hg : Pattern.gen env rank classify (.iota rec m c' n) r = some g)
    (hci : env.constants rec = some ci) :
    ∃ (Hs : List VExpr) (I : Name) (us : List VLevel) (Bmaj : VExpr),
      Hs.length = m ∧ ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj) ∧
      ∃ (ci' : VConstant) (Fs : List VExpr) (R' : VExpr),
        classify c' = some (.ctor n) ∧ env.constants c' = some ci' ∧
        Fs.length = n ∧ ci'.type.instL us = Fs.foldr .forallE R' ∧
        g.ctx = Fs.reverse ++ Hs.reverse := by
  obtain ⟨ci₀, ci', Hs, I, us, Bmaj, Fs, R', h1, h2, h3, l4, e4, l5, e5, h6, -, -⟩ := gen_iota hg
  cases hci.symm.trans h1
  exact ⟨Hs, I, us, Bmaj, l4, e4, ci', Fs, R', h3, h2, l5, e5, h6⟩

/-- Spec lemma (b), VExpr form: the generic LHS `rec (bvar (n+m-1)) … (bvar n) (c' (bvar (n-1)) … (bvar 0))`,
at the recursor's own level parameters and the major's levels `us`. -/
theorem Pattern.gen_lhs {env : VEnv} {rank : Name → Nat} {classify : Name → Option Classification}
    {rec c' : Name} {m n : Nat} {r : (Pattern.iota rec m c' n).RHS} {g : PatGen} {ci : VConstant}
    {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr}
    (hg : Pattern.gen env rank classify (.iota rec m c' n) r = some g)
    (hci : env.constants rec = some ci) (hHs : Hs.length = m)
    (hT : ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj)) :
    g.lhs = .app (VExpr.bvarSpine (.const rec (VLevel.params ci.uvars)) m n)
      (VExpr.bvarSpine (.const c' us) n 0) := by
  obtain ⟨ci₀, -, Hs₀, I₀, us₀, Bmaj₀, -, -, h1, -, -, l4, e4, -, -, -, h7, -⟩ := gen_iota hg
  cases hci.symm.trans h1
  obtain ⟨-, -, rfl, -⟩ := VExpr.foldr_forallE_major_inj (hHs.trans l4.symm) (hT.symm.trans e4)
  exact h7

/-- Spec lemma (d), `gen_type`: the recursor's body with the major instantiated by the generic
ctor spine (the body lifted past the `n` field variables). -/
theorem Pattern.gen_type {env : VEnv} {rank : Name → Nat} {classify : Name → Option Classification}
    {rec c' : Name} {m n : Nat} {r : (Pattern.iota rec m c' n).RHS} {g : PatGen} {ci : VConstant}
    {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr}
    (hg : Pattern.gen env rank classify (.iota rec m c' n) r = some g)
    (hci : env.constants rec = some ci) (hHs : Hs.length = m)
    (hT : ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj)) :
    g.type = (Bmaj.liftN n 1).inst (VExpr.bvarSpine (.const c' us) n 0) := by
  obtain ⟨ci₀, -, Hs₀, I₀, us₀, Bmaj₀, -, -, h1, -, -, l4, e4, -, -, -, -, h8⟩ := gen_iota hg
  cases hci.symm.trans h1
  obtain ⟨-, -, rfl, rfl⟩ := VExpr.foldr_forallE_major_inj (hHs.trans l4.symm) (hT.symm.trans e4)
  exact h8

/-- The delta shape `.const c`: `ctx = []`, `lhs = const c params`, `type = ci.type`. -/
theorem Pattern.gen_delta {env : VEnv} {rank : Name → Nat} {classify : Name → Option Classification}
    {c : Name} {r : (Pattern.const c).RHS} {g : PatGen}
    (hg : Pattern.gen env rank classify (.const c) r = some g) :
    ∃ ci, env.constants c = some ci ∧ g.ctx = [] ∧ g.lhs = .const c (VLevel.params ci.uvars) ∧
      g.type = ci.type := by
  obtain ⟨-, h2, -⟩ := Pattern.gen_eq_some hg
  simp only [genCore, Option.map_eq_some_iff, Prod.mk.injEq] at h2
  obtain ⟨ci, h1, h2, h3, h4⟩ := h2
  exact ⟨ci, h1, h2.symm, h3.symm, h4.symm⟩

theorem Arity.varN_const {h c : Name} : ∀ {m k : Nat}, Arity (.const h) k (.varN (.const c) m) → k = m
  | 0, _, H => by cases H; rfl
  | m+1, _, H => by
    cases H with
    | var H => rw [Arity.varN_const H]

/-- Spec lemma (e), `gen_arity` (iota and delta): the head's type has at least the pattern
arity of syntactic Π-binders. -/
theorem Pattern.gen_arity {env : VEnv} {rank : Name → Nat} {classify : Name → Option Classification}
    {p : Pattern} {r : p.RHS} {g : PatGen} {ci : VConstant} {k : Nat}
    (hg : Pattern.gen env rank classify p r = some g) (hci : env.constants p.head = some ci)
    (hk : Arity (.const p.head) k p) :
    ∃ (Hs : List VExpr) (B : VExpr), Hs.length = k ∧ ci.type = Hs.foldr .forallE B := by
  obtain ⟨-, h2, -⟩ := Pattern.gen_eq_some hg
  match p, h2, hci, hk with
  | .const c, _, _, hk => cases hk; exact ⟨[], ci.type, rfl, rfl⟩
  | .app f a, h2, hci, hk =>
    simp only [genCore] at h2
    split at h2
    · next rec m c' n hf ha =>
      cases eq_varN_of_asVarN hf; cases eq_varN_of_asVarN ha
      obtain ⟨ci₀, -, Hs, I, us, Bmaj, -, -, h1, -, -, t4, -⟩ := Pattern.genIota_eq_some h2
      obtain ⟨l4, e4⟩ := VExpr.piTelescope_eq_some t4
      have hhead : (Pattern.iota rec m c' n).head = rec := head_varN rec m
      rw [hhead] at hci hk
      cases hci.symm.trans h1
      cases hk with
      | app hk =>
        cases Arity.varN_const hk
        exact ⟨Hs ++ [.const I us], Bmaj, by simp [l4], by simp [e4]⟩
    · cases h2
  | .var _, h2, _, _ => cases h2

theorem Pattern.RHS.mem_selfLeaves {p : Pattern} {sel : VExpr → Bool} {r : p.RHS} {e : VExpr} :
    e ∈ r.selfLeaves sel ↔ e ∈ r.fixedLeaves ∧ sel e = true := List.mem_filter

/-- Spec lemma (g), `gen_self`: one `self` entry per same-rank bare-constant leaf occurrence of
the RHS (in `fixedLeaves` order), typed by the constant's type at the occurrence's levels. -/
theorem Pattern.gen_self {env : VEnv} {rank : Name → Nat} {classify : Name → Option Classification}
    {p : Pattern} {r : p.RHS} {g : PatGen} (hg : Pattern.gen env rank classify p r = some g) :
    g.self.length = (r.selfLeaves (Pattern.sameRank rank p.head)).length ∧
    ∀ (j : Nat) (e : VExpr), (r.selfLeaves (Pattern.sameRank rank p.head))[j]? = some e →
      ∃ (c' : Name) (us : List VLevel) (ci' : VConstant), e = .const c' us ∧
        env.constants c' = some ci' ∧ rank c' = rank p.head ∧
        g.self[j]? = some (ci'.type.instL us) := by
  obtain ⟨h1, -⟩ := Pattern.gen_eq_some hg
  obtain ⟨l1, h1⟩ := Pattern.selfTypes_eq_some h1
  refine ⟨l1, fun j e he => ?_⟩
  obtain ⟨c', us, ci', rfl, h2, h3⟩ := h1 j e he
  have hsel := (Pattern.RHS.mem_selfLeaves.1 (List.mem_of_getElem? he)).2
  obtain ⟨c'', us', he', hr⟩ := Pattern.sameRank_eq_true.1 hsel
  cases he'
  exact ⟨c', us, ci', rfl, h2, hr, h3⟩

theorem Pattern.RHS.selfLeaves_app {p : Pattern} (sel : VExpr → Bool)
    (f a : p.RHS) : (Pattern.RHS.app f a).selfLeaves sel = f.selfLeaves sel ++ a.selfLeaves sel := by
  simp [Pattern.RHS.selfLeaves, Pattern.RHS.fixedLeaves, List.filter_append]

/-! # Part 2: `SExpr` forms, the `Params`-field package, the measure -/

namespace SExpr
variable [Params]

/-- `SelfType.lean` (docs/const-case/plan, not in the repo). -/
theorem _root_.Lean4Lean.SLevel.instV_inst {ls : List SLevel} {us : List VLevel} {l : VLevel} :
    SLevel.instV ls (l.inst us) = SLevel.instV (us.map (SLevel.instV ls)) l := by
  apply Subtype.ext; funext v
  simp only [SLevel.instV, VLevel.eval_inst, List.map_map, Function.comp_def]

/-- `SelfType.lean: mkInst_instL`. -/
theorem mkInst_instL {ls : List SLevel} {us : List VLevel} :
    ∀ {e : VExpr}, mkInst ls (e.instL us) = mkInst (us.map (SLevel.instV ls)) e
  | .bvar _ => rfl
  | .sort u => by simp only [VExpr.instL, mkInst, SLevel.instV_inst]
  | .const c vs => by
    simp only [VExpr.instL, mkInst, List.map_map, Function.comp_def, SLevel.instV_inst]
  | .app f a | .lam f a | .forallE f a => by
    simp only [VExpr.instL, mkInst, mkInst_instL (e := f), mkInst_instL (e := a)]

theorem _root_.Lean4Lean.SLevel.instV_params {ls : List SLevel} {n : Nat} (h : ls.length = n) :
    (VLevel.params n).map (SLevel.instV ls) = ls := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [VLevel.params, List.map_map, List.getElem_map, List.getElem_range, Function.comp]
  apply Subtype.ext; funext v
  simp [SLevel.instV, VLevel.eval, List.getD_eq_getElem?_getD, h2]

theorem mkInst_foldl_app (ls : List SLevel) : ∀ (Xs : List VExpr) (h : VExpr),
    mkInst ls (Xs.foldl .app h) = spine (mkInst ls h) (Xs.map (mkInst ls))
  | [], _ => rfl
  | X :: Xs, h => mkInst_foldl_app ls Xs (.app h X)

theorem spine_subst (σ : Subst) : ∀ (Xs : List SExpr) (h : SExpr),
    (spine h Xs).subst σ = spine (h.subst σ) (Xs.map (·.subst σ))
  | [], _ => rfl
  | X :: Xs, h => spine_subst σ Xs (.app h X)

theorem mkInst_foldr_forallE (ls : List SLevel) : ∀ (Hs : List VExpr) (B : VExpr),
    mkInst ls (Hs.foldr .forallE B) = (Hs.map (mkInst ls)).foldr .forallE (mkInst ls B)
  | [], _ => rfl
  | A :: Hs, B => by simp [mkInst, mkInst_foldr_forallE ls Hs B]

theorem mkInst_bvarSpine (ls : List SLevel) (h : VExpr) (k off : Nat) :
    mkInst ls (VExpr.bvarSpine h k off) =
      spine (mkInst ls h) ((List.range k).reverse.map fun i => .bvar (off + i)) := by
  unfold VExpr.bvarSpine; rw [mkInst_foldl_app]; simp [List.map_map, Function.comp_def, mkInst]

/-- `const c ls (bvar (k-1)) … (bvar 0)` (docs/const-case/CtorClause.lean:102). -/
def openSpine (c : Name) (ls : List SLevel) (k : Nat) : SExpr :=
  spine (.const c ls) ((List.range k).reverse.map .bvar)

theorem openSpine_subst (c : Name) (ls : List SLevel) (k : Nat) (σ : Subst) :
    (openSpine c ls k).subst σ = spine (.const c ls) ((List.range k).reverse.map σ) := by
  simp [openSpine, spine_subst, List.map_map, Function.comp_def, SExpr.subst]

/-- Spec lemma (b), `gen_lhs`, under a substitution: the `openSpine rec ls (m+1)` instance
with the major replaced by the ctor spine. -/
theorem _root_.Lean4Lean.Pattern.gen_lhs_subst {env : VEnv} {rank : Name → Nat}
    {classify : Name → Option Classification}
    {rec c' : Name} {m n : Nat} {r : (Pattern.iota rec m c' n).RHS} {g : PatGen} {ci : VConstant}
    {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr}
    (hg : Pattern.gen env rank classify (.iota rec m c' n) r = some g)
    (hci : env.constants rec = some ci) (hHs : Hs.length = m)
    (hT : ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj))
    {ls : List SLevel} (hls : ls.length = ci.uvars) (σ : Subst) :
    (mkInst ls g.lhs).subst σ =
      .app (spine (.const rec ls) ((List.range m).reverse.map fun i => σ (n + i)))
        (spine (.const c' (us.map (SLevel.instV ls))) ((List.range n).reverse.map σ)) := by
  rw [Pattern.gen_lhs hg hci hHs hT]
  simp only [mkInst, mkInst_bvarSpine, SExpr.subst, spine_subst, List.map_map, Function.comp_def,
    SLevel.instV_params hls, Nat.zero_add]

theorem _root_.Lean4Lean.Pattern.gen_lhs_openSpine {env : VEnv} {rank : Name → Nat}
    {classify : Name → Option Classification}
    {rec c' : Name} {m n : Nat} {r : (Pattern.iota rec m c' n).RHS} {g : PatGen} {ci : VConstant}
    {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr}
    (hg : Pattern.gen env rank classify (.iota rec m c' n) r = some g)
    (hci : env.constants rec = some ci) (hHs : Hs.length = m)
    (hT : ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj))
    {ls : List SLevel} (hls : ls.length = ci.uvars) (σ : Subst) :
    (mkInst ls g.lhs).subst σ =
      .app ((openSpine rec ls m).subst fun i => σ (n + i))
        ((openSpine c' (us.map (SLevel.instV ls)) n).subst σ) := by
  rw [Pattern.gen_lhs_subst hg hci hHs hT hls, openSpine_subst, openSpine_subst]

/-- The per-occurrence RHS instance as a substitution instance (generic form of (c)). -/
theorem _root_.Lean4Lean.Pattern.RHS.toVExpr_subst {p : Pattern} (sel : VExpr → Bool) (k : Nat)
    (ls : List SLevel) (m2 : p.Path → SExpr) (σ : Subst)
    (hidx : ∀ path, σ (k + p.pathIdx path) = m2 path) :
    ∀ (r : p.RHS) (j : Nat),
      (∀ (i : Nat) (e : VExpr), (r.selfLeaves sel)[i]? = some e → σ (j + i) = mkInst ls e) →
      (mkInst ls (r.toVExpr sel k j)).subst σ = r.applyS ls m2
  | .fixed e cl, j, hs => by
    simp only [Pattern.RHS.toVExpr, Pattern.RHS.applyS]
    split
    · next h =>
      have := hs 0 e (by simp [Pattern.RHS.selfLeaves, Pattern.RHS.fixedLeaves, h])
      simpa [mkInst, SExpr.subst] using this
    · exact cl.mkInstS.subst_eq .zero
  | .var path, _, _ => by
    simp only [Pattern.RHS.toVExpr, Pattern.RHS.applyS, mkInst, SExpr.subst, hidx]
  | .app f a, j, hs => by
    rw [Pattern.RHS.selfLeaves_app] at hs
    have hf := toVExpr_subst sel k ls m2 σ hidx f j fun i e he =>
      hs i e (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 he).1]; exact he)
    have ha := toVExpr_subst sel k ls m2 σ hidx a (j + (f.selfLeaves sel).length) fun i e he => by
      rw [Nat.add_assoc]
      exact hs _ e (by rw [List.getElem?_append_right (by omega)]; simpa using he)
    simp only [Pattern.RHS.toVExpr, Pattern.RHS.applyS, mkInst, SExpr.subst, hf, ha]

/-- Spec lemma (c), the per-occurrence `RHS.toVExpr_subst` at `Pattern.gen`'s `rhsAbs`:
`σ` sends the `j`-th same-rank bare leaf occurrence's self variable `bvar j` to that occurrence
(instantiated), and the pattern variable of `path` (`bvar (g.self.length + pathIdx path)`) to
`m2 path`. -/
theorem _root_.Lean4Lean.Pattern.gen_rhsAbs {env : VEnv} {rank : Name → Nat}
    {classify : Name → Option Classification} {p : Pattern} {r : p.RHS} {g : PatGen}
    (hg : Pattern.gen env rank classify p r = some g)
    (ls : List SLevel) (m2 : p.Path → SExpr) (σ : Subst)
    (hself : ∀ (j : Nat) (e : VExpr), (r.selfLeaves (Pattern.sameRank rank p.head))[j]? = some e →
      σ j = mkInst ls e)
    (hidx : ∀ path, σ (g.self.length + p.pathIdx path) = m2 path) :
    (mkInst ls g.rhsAbs).subst σ = r.applyS ls m2 := by
  rw [(Pattern.gen_eq_some hg).2.2.2]
  exact Pattern.RHS.toVExpr_subst _ _ ls m2 σ hidx r 0 fun i e he => by
    rw [Nat.zero_add]; exact hself i e he

/-- Spec lemma (f), `gen_rhs`: the unabstracted RHS under the pattern substitution. -/
theorem _root_.Lean4Lean.Pattern.gen_rhs {env : VEnv} {rank : Name → Nat}
    {classify : Name → Option Classification} {p : Pattern} {r : p.RHS} {g : PatGen}
    (hg : Pattern.gen env rank classify p r = some g)
    (ls : List SLevel) (m2 : p.Path → SExpr) (σ : Subst)
    (hidx : ∀ path, σ (p.pathIdx path) = m2 path) :
    (mkInst ls g.rhs).subst σ = r.applyS ls m2 := by
  rw [(Pattern.gen_eq_some hg).2.2.1]
  refine Pattern.RHS.toVExpr_subst _ 0 ls m2 σ (fun path => by rw [Nat.zero_add]; exact hidx path)
    r 0 fun i e he => ?_
  have : r.selfLeaves (fun _ => false) = [] := by
    rw [Pattern.RHS.selfLeaves, List.filter_eq_nil_iff]; simp
  simp [this] at he

/-- Spec lemma (g) at the `SExpr` level (`SelfType.lean: mkInst_instL`): the `j`-th self entry,
instantiated, is `ConstGoal`'s type at the occurrence `mkInst ls (.const c' us)`. -/
theorem _root_.Lean4Lean.Pattern.gen_self_mkInst {env : VEnv} {rank : Name → Nat}
    {classify : Name → Option Classification} {p : Pattern} {r : p.RHS} {g : PatGen}
    (hg : Pattern.gen env rank classify p r = some g) {j : Nat} {e : VExpr}
    (he : (r.selfLeaves (Pattern.sameRank rank p.head))[j]? = some e) (ls : List SLevel) :
    ∃ (c' : Name) (us : List VLevel) (ci' : VConstant) (T : VExpr), e = .const c' us ∧
      env.constants c' = some ci' ∧ rank c' = rank p.head ∧ g.self[j]? = some T ∧
      mkInst ls e = .const c' (us.map (SLevel.instV ls)) ∧
      mkInst ls T = mkInst (us.map (SLevel.instV ls)) ci'.type := by
  obtain ⟨c', us, ci', rfl, h1, h2, h3⟩ := (Pattern.gen_self hg).2 j e he
  exact ⟨c', us, ci', _, rfl, h1, h2, h3, rfl, mkInst_instL⟩

/-- Spec lemma (e) for the instantiated type. -/
theorem _root_.Lean4Lean.Pattern.gen_arity_mkInst {env : VEnv} {rank : Name → Nat}
    {classify : Name → Option Classification}
    {p : Pattern} {r : p.RHS} {g : PatGen} {ci : VConstant} {k : Nat}
    (hg : Pattern.gen env rank classify p r = some g) (hci : env.constants p.head = some ci)
    (hk : Arity (.const p.head) k p) (ls : List SLevel) :
    ∃ (Hs : List SExpr) (B : SExpr), Hs.length = k ∧ mkInst ls ci.type = Hs.foldr .forallE B := by
  obtain ⟨Hs, B, h1, h2⟩ := Pattern.gen_arity hg hci hk
  exact ⟨Hs.map (mkInst ls), mkInst ls B, by simp [h1], by rw [h2, mkInst_foldr_forallE]⟩

/-- Spec lemma (a) with `ctor_syn`: the field telescope `Fs` of `gen_head` is the constructor's
`ctor_syn` telescope at the major's levels `us`. -/
theorem _root_.Lean4Lean.Pattern.gen_head_ctor {rank : Name → Nat}
    {rec c' : Name} {m n : Nat} {r : (Pattern.iota rec m c' n).RHS} {g : PatGen} {ci : VConstant}
    (hg : Pattern.gen Params.env rank Params.classify (.iota rec m c' n) r = some g)
    (hci : Params.env.constants rec = some ci) :
    ∃ (Hs : List VExpr) (I : Name) (us : List VLevel) (Bmaj : VExpr),
      Hs.length = m ∧ ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj) ∧
      ∃ (ci' : VConstant) (I' : Name) (Ts args : List VExpr),
        Params.env.constants c' = some ci' ∧ Params.classify c' = some (.ctor n) ∧
        Ts.length = n ∧ Params.classify I' = some (.indTy args.length) ∧
        ci'.type = Ts.foldr .forallE
          (args.foldr (fun A acc => acc.app A) (.const I' (VLevel.params ci'.uvars))) ∧
        g.ctx = (Ts.map (·.instL us)).reverse ++ Hs.reverse := by
  obtain ⟨Hs, I, us, Bmaj, l1, e1, ci', Fs, R', hcl, hci', l2, e2, hctx⟩ := Pattern.gen_head hg hci
  obtain ⟨I', Ts, args, hTs, hI', e3⟩ := Params.ctor_syn (cl := .ctor n) rfl hcl hci'
  rw [e3, VExpr.instL_foldr_forallE] at e2
  obtain ⟨rfl, -⟩ := VExpr.foldr_forallE_inj (by simp [l2]; exact hTs) e2
  exact ⟨Hs, I, us, Bmaj, l1, e1, ci', I', Ts, args, hci', hcl, hTs, hI', e3, hctx⟩

/-! ## The Params-field package (scratch structure; R5 lands these as `Params` fields) -/

/-- D4/D3's new `Params` fields, over the current `Params` (stated as a structure, as
`Measure.lean` did). `indTy_closed` and `ctor_fields_closed` are the stage-1a restriction (D3). -/
structure RankParams where
  rank : Name → Nat
  rank_ordered : ∀ k, (Params.env.below rank k).Ordered
  type_below : ∀ {c : Name} {ci : VConstant}, Params.env.constants c = some ci →
    (Params.env.below rank (rank c)).IsType ci.uvars [] ci.type
  pat_rank : ∀ {p : Pattern} {r : p.RHS × p.Check} {c' : Name} {us : List VLevel},
    Params.Pat p r → .const c' us ∈ r.1.fixedLeaves → rank c' ≤ rank p.head
  pat_gen : ∀ {p : Pattern} {r : p.RHS × p.Check}, Params.Pat p r →
    (Pattern.gen Params.env rank Params.classify p r.1).isSome
  pat_typed : ∀ {p : Pattern} {r : p.RHS × p.Check} {g : PatGen} {ci : VConstant},
    Params.Pat p r → Pattern.gen Params.env rank Params.classify p r.1 = some g →
    Params.env.constants p.head = some ci →
    OnCtx (g.self ++ g.ctx) (fun Γ A => (Params.env.below rank (rank p.head)).IsType ci.uvars Γ A) ∧
    (Params.env.below rank (rank p.head)).HasType ci.uvars (g.self ++ g.ctx) g.rhsAbs
      (g.type.liftN g.self.length)
  pat_defeq : ∀ {p : Pattern} {r : p.RHS × p.Check} {g : PatGen} {ci : VConstant},
    Params.Pat p r → Pattern.gen Params.env rank Params.classify p r.1 = some g →
    Params.env.constants p.head = some ci →
    Params.env.IsDefEq ci.uvars g.ctx g.lhs g.rhs g.type
  pat_check : ∀ {p : Pattern} {r : p.RHS × p.Check}, Params.Pat p r → r.2 = .true
  indTy_closed : ∀ {I : Name} {k : Nat} {ci : VConstant}, Params.classify I = some (.indTy k) →
    Params.env.constants I = some ci → k = 0 ∧ ∃ u, ci.type = .sort u
  ctor_fields_closed : ∀ {c : Name} {cl : Classification} {ci : VConstant},
    (cl matches .ctor .. | .etaCtor ..) → Params.classify c = some cl →
    Params.env.constants c = some ci →
    ∃ (I : Name) (Ts : List VExpr), ci.type = Ts.foldr .forallE (.const I (VLevel.params ci.uvars)) ∧
      ∀ T ∈ Ts, ∃ (I' : Name) (us : List VLevel), T = .const I' us ∧
        Params.classify I' = some (.indTy 0)

/-- Spec lemma (e) through `pat_gen`, for any `Pat` (iota or delta). -/
theorem RankParams.pat_arity (RP : RankParams) {p : Pattern} {r : p.RHS × p.Check}
    {ci : VConstant} {k : Nat} (hP : Params.Pat p r) (hci : Params.env.constants p.head = some ci)
    (hk : Arity (.const p.head) k p) :
    ∃ (Hs : List VExpr) (B : VExpr), Hs.length = k ∧ ci.type = Hs.foldr .forallE B := by
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 (RP.pat_gen hP)
  exact Pattern.gen_arity hg hci hk

/-! ## `EnvStrongR`: rank-bounded strong typings, from `type_below` / `pat_typed` -/

/-- Rank-bounded strong typings of constant types and of each rule's generated RHS (and of its
generated context, entry by entry), all in the prefix `env.below rank (rank head)`. -/
structure EnvStrongR (RP : RankParams) : Prop where
  const : ∀ {c : Name} {ci : VConstant} (ls : List SLevel), Params.env.constants c = some ci →
    ∃ u, IsDefEqStrong (Params.env.below RP.rank (RP.rank c)) []
      (mkInst ls ci.type) (mkInst ls ci.type) (.sort u)
  ctx : ∀ {p : Pattern} {r : p.RHS × p.Check} {g : PatGen} {ci : VConstant} (ls : List SLevel),
    Params.Pat p r → Pattern.gen Params.env RP.rank Params.classify p r.1 = some g →
    Params.env.constants p.head = some ci →
    ∀ (i : Nat) (A : VExpr), (g.self ++ g.ctx)[i]? = some A →
    ∃ u, IsDefEqStrong (Params.env.below RP.rank (RP.rank p.head))
      (((g.self ++ g.ctx).drop (i + 1)).map (mkInst ls)) (mkInst ls A) (mkInst ls A) (.sort u)
  rhs : ∀ {p : Pattern} {r : p.RHS × p.Check} {g : PatGen} {ci : VConstant} (ls : List SLevel),
    Params.Pat p r → Pattern.gen Params.env RP.rank Params.classify p r.1 = some g →
    Params.env.constants p.head = some ci →
    IsDefEqStrong (Params.env.below RP.rank (RP.rank p.head)) ((g.self ++ g.ctx).map (mkInst ls))
      (mkInst ls g.rhsAbs) (mkInst ls g.rhsAbs) (mkInst ls (g.type.liftN g.self.length))

omit [Params] in
theorem onCtx_map_instL_levelWF {U : Nat} {vs : List VLevel} (hvs : ∀ l ∈ vs, l.WF U) :
    ∀ Γ : List VExpr, OnCtx (Γ.map (VExpr.instL vs)) (fun _ A => A.LevelWF U)
  | [] => trivial
  | _ :: Γ => ⟨onCtx_map_instL_levelWF hvs Γ, VExpr.LevelWF.instL hvs⟩

omit [Params] in
theorem OnCtx.getElem? {P : List VExpr → VExpr → Prop} :
    ∀ {Γ : List VExpr} {i : Nat} {A : VExpr}, OnCtx Γ P → Γ[i]? = some A →
      OnCtx (Γ.drop (i + 1)) P ∧ P (Γ.drop (i + 1)) A
  | _ :: _, 0, _, ⟨h1, h2⟩, he => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he; subst he; exact ⟨h1, h2⟩
  | _ :: Γ, i + 1, _, ⟨h1, _⟩, he => OnCtx.getElem? (Γ := Γ) (i := i) h1 (by simpa using he)

/-- The `type_below`/`pat_typed` → strong chain in one prefix: `VEnv.IsDefEq.strong`
(`rank_ordered`), `instL`, then the repo's `mkSE` at `E = env.below rank k`. -/
theorem RankParams.strong_below (RP : RankParams) {k U : Nat} {Γ : List VExpr} {e A : VExpr}
    (hΓ : OnCtx Γ (fun Γ A => (Params.env.below RP.rank k).IsType U Γ A))
    (H : (Params.env.below RP.rank k).HasType U Γ e A) (ls : List SLevel) :
    IsDefEqStrong (Params.env.below RP.rank k) (Γ.map (mkInst ls))
      (mkInst ls e) (mkInst ls e) (mkInst ls A) := by
  obtain ⟨vs, hvs, rfl⟩ := SLevel.exists_map_mk ls
  have hS := (VEnv.IsDefEq.strong (RP.rank_ordered k) hΓ H).instL hvs
  have := hS.mkSE (CtorProviderE.synE (Params.env.below_le ..)) (onCtx_map_instL_levelWF hvs Γ)
  have hctx : Γ.map (mkInst (vs.map SLevel.mk)) = (Γ.map (VExpr.instL vs)).map SExpr.mk := by
    rw [List.map_map]; congr 1; funext B; exact mkInst_map_mk hvs
  rw [hctx, mkInst_map_mk hvs, mkInst_map_mk hvs]
  exact this

/-- `EnvStrongR.of_params` (Measure6.lean:298), with the repo's `mkSE` (no `hE`). -/
theorem EnvStrongR.of_params (RP : RankParams) : EnvStrongR RP where
  const := fun ls h1 => by
    obtain ⟨u, hu⟩ := RP.type_below h1
    exact ⟨_, RP.strong_below (Γ := []) trivial hu ls⟩
  ctx := fun ls hP hg h1 i A hA => by
    obtain ⟨h2, ⟨u, hu⟩⟩ := OnCtx.getElem? (RP.pat_typed hP hg h1).1 hA
    exact ⟨_, RP.strong_below h2 hu ls⟩
  rhs := fun ls hP hg h1 =>
    RP.strong_below (RP.pat_typed hP hg h1).1 (RP.pat_typed hP hg h1).2 ls

/-! ## The measure: WF IH, `ConstGoal`, local IH -/

/-- Telescope valuation (docs/const-case/CtorClause.lean:106). -/
def Valuation.ofRargs {n} (rargs : List (WShape n)) : Valuation :=
  rargs.foldr (fun x ρ => ρ.push x.T) .nil

/-- The WF IH of `LR.adequacy_rank` at bound `k`. -/
def LR.WFIH (rank : Name → Nat) (Γ₀ : List SExpr) (k : Nat) : Prop :=
  ∀ k' < k, ∀ {Γ M N A}, IsDefEqStrong (Params.env.below rank k') Γ M N A →
    ∀ {ρ n} {m a : WShape n}, LE_Interp ρ m.T M → LE_Interp ρ a.T A → m.HasType a →
      LR.Adequate Γ₀ Γ ρ M N A m a

/-- `LR.const_local`'s conclusion (PLAN D4) for `hM : LE_Interp ρ mT (.const c ls)`:
`⊥`, or the ∃-typed-upper-bound form. -/
def LR.ConstGoal (Γ₀ : List SExpr) (ρ : Valuation) (mT : TShape) (c : Name) (ls : List SLevel)
    (ci : VConstant) : Prop :=
  (∃ n, mT = (WShape.bot (n := n)).T) ∨
  ∃ (n : Nat) (m' a' : WShape n), mT ≤ m'.T ∧ m'.HasType a' ∧ LE_Interp ρ a'.T (mkInst ls ci.type) ∧
    ∀ {n'} (m a : WShape n'), m.T ≤ m'.T → LE_Interp ρ a.T (mkInst ls ci.type) → m.HasType a →
      (LR Γ₀).DefEq (.const c ls) (.const c ls) (mkInst ls ci.type) m a

/-- The local IH for the `R`-premise of `LE_Interp.const`: same-rank bare-constant leaves. -/
def LR.LocalIH (rank : Name → Nat) (Γ₀ : List SExpr) (ρ₀ : Valuation) (c : Name)
    (R : TShape → SExpr → Prop) : Prop :=
  ∀ m e, R m e → ∀ c' ls' ci', e = .const c' ls' → rank c' = rank c →
    Params.env.constants c' = some ci' → ls'.length = ci'.uvars → LR.ConstGoal Γ₀ ρ₀ m c' ls' ci'

/-- The spine lemma (R9; PLAN D4, `PatLeafStmt2.lean`): induction on `Const`, at every valuation
above the telescope valuation that a `SubstWF` covers, goal at every typed shape below. -/
theorem LR.const_spine (RP : RankParams) {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
    (WFIH : LR.WFIH RP.rank Γ₀ k) {c : Name} {ci : VConstant} {ls : List SLevel}
    (hc : RP.rank c < k) (h1 : Params.env.constants c = some ci) (h2 : ls.length = ci.uvars)
    {R : TShape → SExpr → Prop} (LIH : LR.LocalIH RP.rank Γ₀ ρ₀ c R)
    {n : Nat} {rargs : List (WShape n)} {mC : TShape} (hC : LE_Interp.Const c ls R rargs mC)
    {Ts : List SExpr} {B : SExpr} (hT : mkInst ls ci.type = Ts.foldr .forallE B)
    (hk : rargs.length = Ts.length)
    {ρ : Valuation} {σ σ' : Subst} (hρ : (Valuation.ofRargs rargs).LE ρ)
    (W : LR.SubstWF Γ₀ σ σ' (Ts.reverse ++ Γ₀) ρ)
    {n'} {m a : WShape n'} (le : m.T ≤ mC) (hA : LE_Interp ρ a.T B) (hmem : m.HasType a)
    (tyV : ∀ {τ τ'}, LR.SubstWF Γ₀ τ τ' (Ts.reverse ++ Γ₀) ρ →
      (LR Γ₀).TyDefEq (B.subst τ) (B.subst τ') a) :
    (LR Γ₀).DefEq ((openSpine c ls Ts.length).subst σ) ((openSpine c ls Ts.length).subst σ')
      (B.subst σ) m a := by
  sorry -- SORRY(E3): spine lemma (R9)

/-- The E6 interface (R10 proves exactly this; R9 calls it at `Const.pat`), `PatLeafStmt2.lean:168`
with the real `Pattern.gen` and the repo's `IsDefEqStrong E`. -/
theorem LR.pat_leaf_1a (RP : RankParams) {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
    (WFIH : LR.WFIH RP.rank Γ₀ k) {c : Name} {ci : VConstant} {ls : List SLevel}
    (hc : RP.rank c < k) (h1 : Params.env.constants c = some ci) (h2 : ls.length = ci.uvars)
    {R : TShape → SExpr → Prop} (LIH : LR.LocalIH RP.rank Γ₀ ρ₀ c R)
    {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} {mC : TShape}
    (hP : Params.Pat p r) (hMt : LE_Interp.Matches p c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1) (hchk : r.2 = .true)
    (g : PatGen) (hg : Pattern.gen Params.env RP.rank Params.classify p r.1 = some g)
    (hty : OnCtx (g.self ++ g.ctx)
        (fun Γ A => (Params.env.below RP.rank (RP.rank c)).IsType ci.uvars Γ A) ∧
      (Params.env.below RP.rank (RP.rank c)).HasType ci.uvars (g.self ++ g.ctx) g.rhsAbs
        (g.type.liftN g.self.length))
    (hdef : Params.env.IsDefEq ci.uvars g.ctx g.lhs g.rhs g.type)
    {Ts : List SExpr} {B : SExpr} (hT : mkInst ls ci.type = Ts.foldr .forallE B)
    (hk : rargs.length = Ts.length)
    {ρ : Valuation} {σ σ' : Subst} (hρ : (Valuation.ofRargs rargs).LE ρ)
    (W : LR.SubstWF Γ₀ σ σ' (Ts.reverse ++ Γ₀) ρ)
    {n'} {m a : WShape n'} (le : m.T ≤ mC) (hA : LE_Interp ρ a.T B) (hmem : m.HasType a)
    (tyV : ∀ {τ τ'}, LR.SubstWF Γ₀ τ τ' (Ts.reverse ++ Γ₀) ρ →
      (LR Γ₀).TyDefEq (B.subst τ) (B.subst τ') a) :
    (LR Γ₀).DefEq ((openSpine c ls Ts.length).subst σ) ((openSpine c ls Ts.length).subst σ')
      (B.subst σ) m a := by
  sorry -- SORRY(E3): pat leaf (E6/R10)

/-- `LR.const_local` (PLAN D4): induction on `hM` through the `R`-closure. Its only recursive
calls are the local IH on the `Const` premise's sub-derivations (`ih7`) and the WF IH at
`rank c ≤ rank c₀ < k` (type validity, `tyV`); the rest is `LR.const_spine` at `rargs = []`. -/
theorem LR.const_local (RP : RankParams) {Γ₀ : List SExpr} {k : Nat} {c₀ : Name}
    (WFIH : LR.WFIH RP.rank Γ₀ k) (hΓ₀ : ⊢ Γ₀) (hc₀ : RP.rank c₀ < k) :
    ∀ {ρ mT M} (_hM : LE_Interp ρ mT M) {c ls ci}, M = .const c ls → RP.rank c ≤ RP.rank c₀ →
      Params.env.constants c = some ci → ls.length = ci.uvars → LR.ConstGoal Γ₀ ρ mT c ls ci := by
  intro ρ mT M hM
  induction hM with
  | bot => intro _ _ _ _ _ _ _; exact .inl ⟨_, rfl⟩
  | @const _ c' ci' mT₀ m' ρ a ls' R h1 h2 h3 h4 h5 h6 _ _ ih7 =>
    intro c ls ci eM hrk hci hlen
    injection eM with e1 e2; subst c' ls'
    have e3 := Option.some.inj (h1.symm.trans hci); subst ci'
    have hk : RP.rank c < k := Nat.lt_of_le_of_lt hrk hc₀
    -- (i) the local IH: same-rank bare-constant leaves of `R`, from `ih7` (strict sub-derivations)
    have LIH : LR.LocalIH RP.rank Γ₀ ρ c R := fun me e hR c'' ls'' ci'' he hr h1'' h2'' =>
      ih7 me e hR he (hr ▸ hrk) h1'' h2''
    -- (ii) type validity: the WF IH at `rank c < k` on `EnvStrongR.const`
    have hcl : (mkInst ls ci.type).ClosedN := (Params.henv.closedC hci).mkInstS
    have tyV : ∀ {n} {a₁ : WShape n}, LE_Interp .nil a₁.T (mkInst ls ci.type) →
        a₁.HasType .type → (LR Γ₀).TyDefEq (mkInst ls ci.type) (mkInst ls ci.type) a₁ := by
      intro n a₁ hA ha
      obtain ⟨u, Hty₀⟩ := (EnvStrongR.of_params RP).const ls hci
      have Hty := Hty₀.weak0 (Γ := Γ₀)
      obtain ⟨n', a', s, le_n, le_a, hA', hS, hmem'⟩ :=
        ((LE_Interp.soundSE (Params.env.below_le ..) Hty (LR.SubstWF.id hΓ₀).fits).2 hA).out
      have tyDE := (WFIH _ hk Hty hA' hS hmem').2 (LR.SubstWF.id hΓ₀)
      simp only [subst_id] at tyDE
      exact LR.toValTy le_n le_a ha hS hmem' tyDE
    -- (iii) the typed upper bound `m'` of the `const` node, lifted to a common level
    refine .inr ?_
    have hK1 : m'.1 ≤ max m'.1 a.1 := Nat.le_max_left ..
    have hK2 : a.1 ≤ max m'.1 a.1 := Nat.le_max_right ..
    refine ⟨max m'.1 a.1, m'.2.lift _, a.2.lift _, h3.trans (TShape.lift_eqv hK1).2,
      (TShape.HasType.def hK1 hK2).1 h4, h5.lift hK2, ?_⟩
    intro n' m₁ a₁ hle hA₁ hmem₁
    -- (iv) the spine lemma at `rargs = []`, `ρ = .nil`, `W = SubstWF.id`
    have H := LR.const_spine RP WFIH hk hci hlen LIH h6 (Ts := []) (B := mkInst ls ci.type) rfl rfl
      Valuation.LE.rfl (LR.SubstWF.id hΓ₀) (hle.trans (TShape.lift_eqv hK1).1)
      ((LE_Interp.closed_iff hcl).1 hA₁) hmem₁ fun _ => by
        rw [hcl.subst_eq .zero, hcl.subst_eq .zero]
        exact tyV ((LE_Interp.closed_iff hcl).1 hA₁) hmem₁.isType
    simpa only [openSpine, List.length_nil, List.range_zero, List.reverse_nil, List.map_nil,
      spine_nil, subst_id] using H
  | _ => intro _ _ _ eM; cases eM

/-- The `const` case of `LR.adequacy_rank` from `LR.const_local` at `c₀ := c` (R8's wiring):
a `(env.below rank k)` constant node, at any `ρ`. -/
theorem LR.const_case (RP : RankParams) {Γ₀ Γ : List SExpr} {k : Nat} (WFIH : LR.WFIH RP.rank Γ₀ k)
    {c : Name} {ci : VConstant} {ls : List SLevel}
    (h1 : (Params.env.below RP.rank k).constants c = some ci) (h2 : ls.length = ci.uvars)
    {ρ : Valuation} {n : Nat} {m a : WShape n} (hM : LE_Interp ρ m.T (.const c ls))
    (hA : LE_Interp ρ a.T (mkInst ls ci.type)) (hmem : m.HasType a) :
    LR.Adequate Γ₀ Γ ρ (.const c ls) (.const c ls) (mkInst ls ci.type) m a := by
  have hrk := VEnv.below_constants_lt h1
  have h1' := (Params.env.below_le ..).1 h1
  refine .refl fun σ _ W => ?_
  rw [(Params.henv.closedC h1').mkInstS.subst_eq .zero]
  obtain ⟨_, he⟩ | ⟨_, m', _, hle, _, _, H⟩ :=
    LR.const_local RP WFIH W.wf₀ hrk hM rfl (Nat.le_refl _) h1' h2
  · cases show m = .bot from TShape.le_bot.1 (he ▸ TShape.bot_le')
    exact (LR _).bot hmem.isType
  · exact H m a hle hA hmem

end SExpr
end Lean4Lean
