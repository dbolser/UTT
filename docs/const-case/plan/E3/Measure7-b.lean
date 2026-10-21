import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! # E3: the measure, `Pattern.gen`, and `LR.const_local` (PLAN.md §2 row E3, §1 D4)

Port of `docs/const-case/Measure.lean` Parts C-E (lens-3 measure skeleton) over the repo's
env-indexed strong judgment (`IsDefEqStrong E`, R4 `9dcefbc`) and its lemmas `VEnv.below`,
`below_le`/`below_mono`/`below_constants_lt`/`below_constants_of_lt`, `IsDefEqStrong.mono`,
`exists_below`, `mkSE`, `CtorProviderE.synE`, `weak_append`, `weak0`, `forallE_inv'`, `telescope`
(all imported, none redefined), with:
* Part A: `Pattern.gen` as a *function* (D4, item R5), with per-occurrence self variables for the
  same-rank bare-constant leaves of the RHS, and its env-level spec lemmas;
* Part B: the `SExpr`-level spec lemmas (a)-(g);
* Part C: the D4/D3 `Params` field package as a scratch structure `RankParams`, and
  `EnvStrongR` (rank-bounded strong typings of constant types and rule RHSs) with
  `EnvStrongR.of_params` (the Measure6.lean:298 pattern, via the repo's `mkSE`) and the lam-case
  chain `EnvStrongR.const_telescope` (via the repo's `telescope`);
* Part D: `LR.WFIH`, `LR.ConstGoal`, `LR.LocalIH` (same rank, no `Block`), `LR.const_spine`
  and `LR.pat_leaf_1a` (statements as in D4 / `plan/historical/PatLeafStmt2.lean`, bodies
  sorry), `LR.const_local` proved from `const_spine`, and the measure's outer levels
  (`LR.adequacy_rank_wf`: the WF induction on `k`; `LR.adequacy_of_rank`: via `exists_below`);
* Part E: the `openSpine` form of (b), the match of the instantiated LHS (`m2 = σ ∘ genIdx`),
  the untyped reduction half of the pat leaf (Measure.lean Part E, over `spine`), and the R8
  wiring of the outer `const` case (`LR.const_case`, `const_local` at `c₀ := c`).

Deliberate sorries (two, both marked): the bodies of `LR.const_spine` (R9) and
`LR.pat_leaf_1a` (E6/R10). -/
namespace Lean4Lean

/-! ## Part A: `Pattern.gen` (D4, item R5: defined before `class Params`) -/

/-- The fixed leaves of a rule RHS (Measure6.lean:69). -/
def Pattern.RHS.fixedLeaves {p : Pattern} : p.RHS → List VExpr
  | .fixed e _ => [e]
  | .var _ => []
  | .app f a => f.fixedLeaves ++ a.fixedLeaves

/-- Strip exactly `k` syntactic Π-binders: `e.piTelescope k = some (Hs, B)` iff
`Hs.length = k ∧ e = Hs.foldr .forallE B` (`piTelescope_eq_some`). -/
def VExpr.piTelescope : Nat → VExpr → Option (List VExpr × VExpr)
  | 0, e => some ([], e)
  | k+1, .forallE A B => (B.piTelescope k).map fun p => (A :: p.1, p.2)
  | _+1, _ => none

theorem VExpr.piTelescope_foldr : ∀ (Hs : List VExpr) (B : VExpr),
    (Hs.foldr .forallE B).piTelescope Hs.length = some (Hs, B)
  | [], _ => rfl
  | A :: Hs, B => by simp [piTelescope, piTelescope_foldr Hs B]

theorem VExpr.piTelescope_eq_some : ∀ {k : Nat} {e : VExpr} {Hs : List VExpr} {B : VExpr},
    e.piTelescope k = some (Hs, B) ↔ Hs.length = k ∧ e = Hs.foldr .forallE B
  | 0, e, Hs, B => by
    cases Hs <;> simp [piTelescope, eq_comm]
  | k+1, e, Hs, B => by
    constructor
    · intro h
      cases e <;> simp only [piTelescope, reduceCtorEq, Option.map_eq_some_iff] at h
      obtain ⟨⟨Hs', B'⟩, h', h''⟩ := h
      simp only [Prod.mk.injEq] at h''
      obtain ⟨rfl, rfl⟩ := h''
      have := (piTelescope_eq_some (k := k)).1 h'
      simp [this.1, this.2]
    · rintro ⟨h, rfl⟩; rw [← h]; exact piTelescope_foldr Hs B

theorem VExpr.foldr_forallE_inj : ∀ {Hs Hs' : List VExpr} {B B' : VExpr},
    Hs.length = Hs'.length → Hs.foldr .forallE B = Hs'.foldr .forallE B' → Hs = Hs' ∧ B = B'
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | A :: Hs, A' :: Hs', _, _, hl, h => by
    simp only [List.foldr_cons, VExpr.forallE.injEq] at h
    have := foldr_forallE_inj (by simpa using hl) h.2
    exact ⟨by rw [h.1, this.1], this.2⟩

theorem VExpr.instL_foldr_forallE {ls : List VLevel} :
    ∀ (Ts : List VExpr) (X : VExpr),
      (Ts.foldr .forallE X).instL ls = (Ts.map (·.instL ls)).foldr .forallE (X.instL ls)
  | [], _ => rfl
  | T :: Ts, X => by simp only [List.foldr_cons, List.map_cons, instL, instL_foldr_forallE Ts X]

/-- The output of `Pattern.gen` (D4). -/
structure PatGen where
  /-- innermost first: the ctor field types, then the head's first `m` binder types -/
  ctx : List VExpr
  /-- one closed type per same-rank bare-leaf occurrence of the RHS, in left-to-right order -/
  self : List VExpr
  /-- the rule's LHS, an open term over `ctx` -/
  lhs : VExpr
  /-- the rule's RHS over `ctx` (pattern variables ↦ `bvar (genIdx path)`, every fixed leaf kept) -/
  rhs : VExpr
  /-- the rule's RHS over `self ++ ctx`: the `j`-th self occurrence ↦ `bvar j`, pattern
  variables ↦ `bvar (self.length + genIdx path)` -/
  rhsAbs : VExpr
  /-- the rule's type over `ctx` -/
  type : VExpr

/-- `p = varN (.const c) n` ↦ `some (c, n)` (`eq_varN_of_constVarN?`, `constVarN?_varN`). -/
def Pattern.constVarN? : Pattern → Option (Name × Nat)
  | .const c => some (c, 0)
  | .var f => f.constVarN?.map fun x => (x.1, x.2 + 1)
  | .app .. => none

/-- The number of trailing `var` binders. -/
def Pattern.varDepth : Pattern → Nat
  | .var f => f.varDepth + 1
  | _ => 0

/-- `Pattern.gen`'s path ↦ `g.ctx` index. For iota `app (varN (const rec) m) (varN (const c') n)`:
`inr (some^i none) ↦ i` (the last field is `bvar 0`, since `Matches.var` binds the last
argument at `none`) and `inl (some^i none) ↦ n + i`. -/
def Pattern.genIdx : (p : Pattern) → p.Path → Nat
  | .const _, x => nomatch x
  | .var _, none => 0
  | .var f, some x => f.genIdx x + 1
  | .app f a, .inl x => a.varDepth + f.genIdx x
  | .app _ a, .inr y => a.genIdx y

/-- A fixed RHS leaf is a *self occurrence* iff it is a bare constant of rank `k`. -/
def VExpr.selfConst? (rank : Name → Nat) (k : Nat) : VExpr → Option (Name × List VLevel)
  | .const c us => if rank c = k then some (c, us) else none
  | _ => none

/-- The occurrences selected by `sel` among the fixed leaves of an RHS, by position, left to right. -/
def Pattern.RHS.selfConsts {p : Pattern} (sel : VExpr → Option (Name × List VLevel)) :
    p.RHS → List (Name × List VLevel)
  | .fixed e _ => (sel e).toList
  | .var _ => []
  | .app f a => f.selfConsts sel ++ a.selfConsts sel

/-- The same-rank (`rank = k`) bare-constant leaf occurrences of an RHS, left to right. -/
abbrev Pattern.RHS.selfOccs {p : Pattern} (rank : Name → Nat) (k : Nat) (r : p.RHS) :
    List (Name × List VLevel) :=
  r.selfConsts (VExpr.selfConst? rank k)

/-- The RHS as an open term over `self ++ ctx` (per occurrence; replaces Measure.lean's
`toVExpr`, which was keyed by `VExpr`): the selected occurrences, numbered left to right from
`j`, become `bvar j, bvar (j+1), …`; `.var path ↦ bvar (s + idx path)`; other fixed leaves stay. -/
def Pattern.RHS.toVExpr {p : Pattern} (sel : VExpr → Option (Name × List VLevel))
    (idx : p.Path → Nat) (s : Nat) : Nat → p.RHS → VExpr
  | j, .fixed e _ => if (sel e).isSome then .bvar j else e
  | _, .var path => .bvar (s + idx path)
  | j, .app f a => .app (f.toVExpr sel idx s j) (a.toVExpr sel idx s (j + (f.selfConsts sel).length))

/-- The RHS as an open term over `ctx`, no self-abstraction. -/
def Pattern.RHS.toOpen {p : Pattern} (idx : p.Path → Nat) : p.RHS → VExpr
  | .fixed e _ => e
  | .var path => .bvar (idx path)
  | .app f a => .app (f.toOpen idx) (a.toOpen idx)

/-- The types of the self occurrences (`none` if a constant is missing). -/
def Pattern.selfTypes (env : VEnv) : List (Name × List VLevel) → Option (List VExpr)
  | [] => some []
  | (c, us) :: l => do
    let ci ← env.constants c
    let Ts ← selfTypes env l
    pure (ci.type.instL us :: Ts)

/-- The part of `Pattern.gen` shared by delta and iota. -/
def Pattern.genCore (env : VEnv) (rank : Name → Nat) (p : Pattern) (r : p.RHS) (head : Name)
    (ctx : List VExpr) (lhs type : VExpr) : Option PatGen := do
  let sel := VExpr.selfConst? rank (rank head)
  let self ← Pattern.selfTypes env (r.selfConsts sel)
  pure { ctx, self, lhs, type, rhs := r.toOpen p.genIdx,
         rhsAbs := r.toVExpr sel p.genIdx self.length 0 }

/-- `classify c = some (.ctor n)`, as a `Bool`. -/
def Classification.isCtorOf : Option Classification → Nat → Bool
  | some (.ctor k), n => k == n
  | _, _ => false

theorem Classification.isCtorOf_iff {o : Option Classification} {n : Nat} :
    Classification.isCtorOf o n = true ↔ o = some (.ctor n) := by
  match o with
  | some (.ctor k) => simp [isCtorOf]
  | some (.etaCtor ..) | some (.symb _) | some (.indTy _) | none => simp [isCtorOf]

/-- The iota case of `Pattern.gen`: `p = app f a` with `f = varN (const rec) m`,
`a = varN (const c') n`, `classify c' = ctor n`, the recursor's type
`Hs.foldr .forallE (.forallE (.const I us) Bmaj)` with `Hs.length = m`, and the field telescope
`Fs` = the first `n` binders of `c'`'s type at the major domain's levels `us`. -/
def Pattern.genIota (env : VEnv) (rank : Name → Nat) (classify : Name → Option Classification)
    (f a : Pattern) (r : (Pattern.app f a).RHS) : Option PatGen :=
  match f.constVarN?, a.constVarN? with
  | some (rec, m), some (c', n) =>
    if Classification.isCtorOf (classify c') n then
      match env.constants rec with
      | some ci =>
        match ci.type.piTelescope m with
        | some (Hs, .forallE (.const _ us) Bmaj) =>
          match env.constants c' with
          | some ci' =>
            match (ci'.type.instL us).piTelescope n with
            | some (Fs, _) =>
              let ctorSpine := ((List.range n).reverse.map VExpr.bvar).foldl .app (.const c' us)
              Pattern.genCore env rank (.app f a) r rec (Fs.reverse ++ Hs.reverse)
                ((((List.range m).reverse.map fun i => VExpr.bvar (n + i)).foldl VExpr.app
                  (.const rec (VLevel.params ci.uvars))).app ctorSpine)
                ((Bmaj.liftN n 1).inst ctorSpine)
            | none => none
          | none => none
        | _ => none
      | none => none
    else none
  | _, _ => none

/-- `Pattern.gen env rank classify p r` (D4, item R5): the computed pattern context and the
rule's open LHS, RHS and type. Delta `.const c`: `ctx = []`, `lhs = const c params`,
`type = ci.type`. Iota: `genIota`. `none` for any other shape, and whenever the head's type has
fewer syntactic Π-binders than the pattern arity (`gen_arity`). Being a function, it leaves no
junk witnesses (`plan/PatTypedDegenerate.lean`, `plan/historical/JunkGen.lean`). -/
def Pattern.gen (env : VEnv) (rank : Name → Nat) (classify : Name → Option Classification) :
    (p : Pattern) → p.RHS → Option PatGen
  | .const c, r =>
    match env.constants c with
    | some ci => Pattern.genCore env rank (.const c) r c [] (.const c (VLevel.params ci.uvars)) ci.type
    | none => none
  | .app f a, r => Pattern.genIota env rank classify f a r
  | .var _, _ => none

/-! ### `Pattern.gen` inversion and the env-level spec lemmas -/

theorem Pattern.eq_varN_of_constVarN? : ∀ {p : Pattern} {c : Name} {n : Nat},
    p.constVarN? = some (c, n) → p = .varN (.const c) n
  | .const c', c, n, h => by
    simp only [constVarN?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | .var f, c, n, h => by
    simp only [constVarN?, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨c', n'⟩, h1, rfl, rfl⟩ := h
    rw [eq_varN_of_constVarN? h1]; rfl
  | .app .., _, _, h => by simp [constVarN?] at h

theorem Pattern.constVarN?_varN {c : Name} : ∀ {n : Nat},
    (Pattern.varN (.const c) n).constVarN? = some (c, n)
  | 0 => rfl
  | n+1 => by simp [varN, constVarN?, constVarN?_varN (n := n)]

theorem Pattern.head_varN {q : Pattern} : ∀ {n : Nat}, (Pattern.varN q n).head = q.head
  | 0 => rfl
  | n+1 => head_varN (n := n)

theorem Pattern.varDepth_varN {c : Name} : ∀ {n : Nat}, (Pattern.varN (.const c) n).varDepth = n
  | 0 => rfl
  | n+1 => by simp [varN, varDepth, varDepth_varN (n := n)]

theorem Pattern.genCore_eq_some {env : VEnv} {rank : Name → Nat} {p : Pattern} {r : p.RHS}
    {head : Name} {ctx : List VExpr} {lhs type : VExpr} {g : PatGen} :
    Pattern.genCore env rank p r head ctx lhs type = some g ↔
    ∃ self, Pattern.selfTypes env (r.selfOccs rank (rank head)) = some self ∧
      g = { ctx, self, lhs, type, rhs := r.toOpen p.genIdx,
            rhsAbs := r.toVExpr (VExpr.selfConst? rank (rank head)) p.genIdx self.length 0 } := by
  simp only [genCore, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq]
  exact exists_congr fun _ => and_congr_right fun _ => eq_comm

/-- Every successful `Pattern.gen` is a `genCore` call at the pattern's head. -/
theorem Pattern.gen_core {env : VEnv} {rank : Name → Nat} {classify} {p : Pattern} {r : p.RHS}
    {g : PatGen} (hg : Pattern.gen env rank classify p r = some g) :
    ∃ ctx lhs type, Pattern.genCore env rank p r p.head ctx lhs type = some g := by
  match p, r, hg with
  | .const c, r, hg =>
    simp only [gen] at hg; split at hg
    · exact ⟨_, _, _, hg⟩
    · cases hg
  | .var _, _, hg => simp [gen] at hg
  | .app f a, r, hg =>
    simp only [gen, genIota] at hg
    split at hg
    · rename_i rec m c' n h1 _
      have : (Pattern.app f a).head = rec := by
        rw [eq_varN_of_constVarN? h1]; simp [head, head_varN]
      rw [this]
      split at hg <;> [skip; cases hg]
      split at hg <;> [skip; cases hg]
      split at hg <;> [skip; cases hg]
      split at hg <;> [skip; cases hg]
      split at hg <;> [skip; cases hg]
      exact ⟨_, _, _, hg⟩
    · cases hg

/-- Inversion of the iota case: all the data `Pattern.gen` reads off the recursor and the
constructor. -/
theorem Pattern.gen_iota {env : VEnv} {rank : Name → Nat} {classify} {rec c' : Name} {m n : Nat}
    {r : (Pattern.app (.varN (.const rec) m) (.varN (.const c') n)).RHS} {g : PatGen}
    (hg : Pattern.gen env rank classify (.app (.varN (.const rec) m) (.varN (.const c') n)) r = some g) :
    ∃ (ci : VConstant) (Hs : List VExpr) (I : Name) (us : List VLevel) (Bmaj : VExpr)
      (ci' : VConstant) (Fs : List VExpr) (X : VExpr),
      env.constants rec = some ci ∧ Hs.length = m ∧
      ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj) ∧
      classify c' = some (.ctor n) ∧
      env.constants c' = some ci' ∧ Fs.length = n ∧ ci'.type.instL us = Fs.foldr .forallE X ∧
      Pattern.genCore env rank _ r rec (Fs.reverse ++ Hs.reverse)
        ((((List.range m).reverse.map fun i => VExpr.bvar (n + i)).foldl VExpr.app
          (.const rec (VLevel.params ci.uvars))).app
          (((List.range n).reverse.map VExpr.bvar).foldl .app (.const c' us)))
        ((Bmaj.liftN n 1).inst (((List.range n).reverse.map VExpr.bvar).foldl .app (.const c' us)))
        = some g := by
  simp only [gen, genIota, constVarN?_varN] at hg
  split at hg <;> [skip; cases hg]
  rename_i hcl
  split at hg <;> [skip; cases hg]
  rename_i ci hci
  split at hg <;> [skip; cases hg]
  rename_i Hs I us Bmaj hHs
  split at hg <;> [skip; cases hg]
  rename_i ci' hci'
  split at hg <;> [skip; cases hg]
  rename_i Fs X hFs
  obtain ⟨h1, h2⟩ := VExpr.piTelescope_eq_some.1 hHs
  obtain ⟨h3, h4⟩ := VExpr.piTelescope_eq_some.1 hFs
  exact ⟨ci, Hs, I, us, Bmaj, ci', Fs, X, hci, h1, h2, Classification.isCtorOf_iff.1 hcl, hci',
    h3, h4, hg⟩

/-- Delta case: `ctx = []`, `lhs = const c params`, `type = ci.type`. -/
theorem Pattern.gen_delta {env : VEnv} {rank : Name → Nat} {classify} {c : Name}
    {r : (Pattern.const c).RHS} {g : PatGen}
    (hg : Pattern.gen env rank classify (.const c) r = some g) :
    ∃ ci : VConstant, env.constants c = some ci ∧
      g.ctx = [] ∧ g.lhs = .const c (VLevel.params ci.uvars) ∧ g.type = ci.type := by
  simp only [gen] at hg; split at hg <;> [skip; cases hg]
  rename_i ci hci
  obtain ⟨_, _, rfl⟩ := genCore_eq_some.1 hg
  exact ⟨ci, hci, rfl, rfl, rfl⟩

/-- `rhs` and `rhsAbs` as computed. -/
theorem Pattern.gen_rhs_eq {env : VEnv} {rank : Name → Nat} {classify} {p : Pattern} {r : p.RHS}
    {g : PatGen} (hg : Pattern.gen env rank classify p r = some g) :
    g.rhs = r.toOpen p.genIdx ∧
    g.rhsAbs = r.toVExpr (VExpr.selfConst? rank (rank p.head)) p.genIdx g.self.length 0 := by
  obtain ⟨ctx, lhs, type, h⟩ := gen_core hg
  obtain ⟨self, _, rfl⟩ := genCore_eq_some.1 h
  exact ⟨rfl, rfl⟩

theorem VExpr.selfConst?_eq_some {rank : Name → Nat} {k : Nat} {e : VExpr} {c : Name}
    {us : List VLevel} : e.selfConst? rank k = some (c, us) ↔ e = .const c us ∧ rank c = k := by
  cases e with
  | const c' us' =>
    simp only [selfConst?]
    split <;> rename_i h
    · simp only [Option.some.injEq, Prod.mk.injEq, VExpr.const.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨⟨rfl, rfl⟩, h⟩
      · rintro ⟨⟨rfl, rfl⟩, -⟩; exact ⟨rfl, rfl⟩
    · simp only [reduceCtorEq, false_iff, not_and, VExpr.const.injEq]
      rintro ⟨rfl, rfl⟩; exact h
  | _ => simp [selfConst?]

/-- Every self occurrence is a fixed leaf, a bare constant of rank `k`. -/
theorem Pattern.RHS.mem_selfOccs {p : Pattern} {rank : Name → Nat} {k : Nat} :
    ∀ {r : p.RHS} {c : Name} {us : List VLevel}, (c, us) ∈ r.selfOccs rank k →
      VExpr.const c us ∈ r.fixedLeaves ∧ rank c = k
  | .fixed e _, c, us, h => by
    simp only [selfOccs, selfConsts, Option.mem_toList] at h
    obtain ⟨rfl, h2⟩ := VExpr.selfConst?_eq_some.1 h
    exact ⟨by simp [fixedLeaves], h2⟩
  | .var _, _, _, h => by simp [selfOccs, selfConsts] at h
  | .app f a, c, us, h => by
    simp only [selfOccs, selfConsts, List.mem_append] at h
    obtain h | h := h
    · have := mem_selfOccs (r := f) h; exact ⟨by simp [fixedLeaves, this.1], this.2⟩
    · have := mem_selfOccs (r := a) h; exact ⟨by simp [fixedLeaves, this.1], this.2⟩

theorem Pattern.selfTypes_spec {env : VEnv} : ∀ {l : List (Name × List VLevel)} {Ts : List VExpr},
    Pattern.selfTypes env l = some Ts →
    Ts.length = l.length ∧ ∀ (j : Nat) c us, l[j]? = some (c, us) →
      ∃ ci, env.constants c = some ci ∧ Ts[j]? = some (ci.type.instL us)
  | [], Ts, h => by
    simp only [selfTypes, Option.some.injEq] at h; subst h; exact ⟨rfl, by simp⟩
  | (c, us) :: l, Ts, h => by
    simp only [selfTypes, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ci, hci, Ts', hTs', rfl⟩ := h
    obtain ⟨ih1, ih2⟩ := selfTypes_spec hTs'
    refine ⟨by simp [ih1], fun j c' us' hj => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hj
      obtain ⟨rfl, rfl⟩ := hj
      exact ⟨ci, hci, rfl⟩
    | succ j => exact ih2 j c' us' (by simpa using hj)

/-- Spec lemma (g) `gen_self`, env part: one self variable per same-rank bare-leaf occurrence
of the RHS (`selfOccs`, left to right: the order of `toVExpr`'s numbering, hence of (c)'s
`selfσ`); the `j`-th, `.fixed (.const c' us)`, is a constant of the environment of rank
`rank p.head`, and `g.self[j]` is its type at `us`. The `mkInst` form is `Pattern.gen_self'`. -/
theorem Pattern.gen_self {env : VEnv} {rank : Name → Nat} {classify} {p : Pattern} {r : p.RHS}
    {g : PatGen} (hg : Pattern.gen env rank classify p r = some g) :
    g.self.length = (r.selfOccs rank (rank p.head)).length ∧
    ∀ (j : Nat) c' us, (r.selfOccs rank (rank p.head))[j]? = some (c', us) →
      ∃ ci', env.constants c' = some ci' ∧ rank c' = rank p.head ∧
        g.self[j]? = some (ci'.type.instL us) := by
  obtain ⟨ctx, lhs, type, h⟩ := gen_core hg
  obtain ⟨self, hself, rfl⟩ := genCore_eq_some.1 h
  obtain ⟨h1, h2⟩ := selfTypes_spec hself
  refine ⟨h1, fun j c' us hj => ?_⟩
  obtain ⟨ci', hci', h3⟩ := h2 j c' us hj
  exact ⟨ci', hci', (RHS.mem_selfOccs (List.mem_of_getElem? hj)).2, h3⟩

/-- Spec lemma (d) `gen_type`: the recursor's body with the major instantiated by the ctor
spine over the field variables (`Bmaj` lifted past the `n` field variables). `Hs`, `I`, `us`,
`Bmaj` are any decomposition of the recursor's type with `Hs.length = m` (unique; (a)). -/
theorem Pattern.gen_type {env : VEnv} {rank : Name → Nat} {classify} {rec c' : Name} {m n : Nat}
    {r : (Pattern.app (.varN (.const rec) m) (.varN (.const c') n)).RHS} {g : PatGen}
    (hg : Pattern.gen env rank classify (.app (.varN (.const rec) m) (.varN (.const c') n)) r = some g)
    {ci : VConstant} (h1 : env.constants rec = some ci)
    {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr} (hHs : Hs.length = m)
    (hT : ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj)) :
    g.type = (Bmaj.liftN n 1).inst (((List.range n).reverse.map VExpr.bvar).foldl .app (.const c' us)) := by
  obtain ⟨ci₁, Hs₁, I₁, us₁, Bmaj₁, ci', Fs, X, h1', hHs₁, hT₁, -, -, -, -, hc⟩ := gen_iota hg
  cases h1.symm.trans h1'
  subst hHs
  obtain ⟨-, he⟩ := VExpr.foldr_forallE_inj hHs₁.symm (hT.symm.trans hT₁)
  injection he with he1 he2
  injection he1 with _ he3
  subst he2 he3
  obtain ⟨_, _, rfl⟩ := genCore_eq_some.1 hc
  rfl

theorem Pattern.genIdx_varN_lt {c : Name} : ∀ {k : Nat} (path : (Pattern.varN (.const c) k).Path),
    (Pattern.varN (.const c) k).genIdx path < k
  | 0, path => nomatch path
  | k+1, none => Nat.succ_pos k
  | k+1, some x => Nat.succ_lt_succ (genIdx_varN_lt (k := k) x)

/-- `genIdx` lands in `g.ctx` (iota): `inl` paths in `[n, n+m)`, `inr` paths in `[0, n)`. -/
theorem Pattern.gen_genIdx_lt {env : VEnv} {rank : Name → Nat} {classify} {rec c' : Name}
    {m n : Nat} {r : (Pattern.app (.varN (.const rec) m) (.varN (.const c') n)).RHS} {g : PatGen}
    (hg : Pattern.gen env rank classify (.app (.varN (.const rec) m) (.varN (.const c') n)) r = some g)
    (path : (Pattern.app (.varN (.const rec) m) (.varN (.const c') n)).Path) :
    (Pattern.app (.varN (.const rec) m) (.varN (.const c') n)).genIdx path < g.ctx.length := by
  obtain ⟨ci, Hs, I, us, Bmaj, ci', Fs, X, -, hHs, -, -, -, hFs, -, hc⟩ := gen_iota hg
  obtain ⟨_, _, rfl⟩ := genCore_eq_some.1 hc
  simp only [List.length_append, List.length_reverse, hHs, hFs]
  cases path with
  | inl x => simp only [genIdx, varDepth_varN]; have := genIdx_varN_lt x; omega
  | inr y => simp only [genIdx]; have := genIdx_varN_lt y; omega

/-- `Arity (.const c) k (varN (.const c') m)` forces `k = m`. -/
theorem Arity.const_varN {c c' : Name} : ∀ {m k : Nat},
    Arity (.const c) k (.varN (.const c') m) → k = m
  | 0, _, h => by cases h; rfl
  | m+1, _, h => by
    cases h with
    | var h => rw [Arity.const_varN h]

/-- Spec lemma (e) `gen_arity`, from `hg` (any shape, delta too): the head's type has at
least the pattern arity many syntactic Π-binders. So `Pattern.gen` is `none` when the head's type
has fewer. The `Pat` form (via `pat_gen`) is `SExpr.RankParams.gen_arity`. -/
theorem Pattern.gen_arity {env : VEnv} {rank : Name → Nat} {classify} {p : Pattern} {r : p.RHS}
    {g : PatGen} (hg : Pattern.gen env rank classify p r = some g) {k : Nat}
    (hA : Arity (.const p.head) k p) {ci : VConstant} (h1 : env.constants p.head = some ci) :
    ∃ (Hs : List VExpr) (B : VExpr), Hs.length = k ∧ ci.type = Hs.foldr .forallE B := by
  match p, r, hg, hA, h1 with
  | .const c, _, _, hA, _ => cases hA; exact ⟨[], ci.type, rfl, rfl⟩
  | .var _, _, hg, _, _ => simp [gen] at hg
  | .app f a, r, hg, hA, h1 =>
    have hg' := hg
    simp only [gen, genIota] at hg
    split at hg
    · rename_i rec m c' n hf ha
      obtain rfl := eq_varN_of_constVarN? hf
      obtain rfl := eq_varN_of_constVarN? ha
      obtain ⟨ci₁, Hs, I, us, Bmaj, -, -, -, h1', hHs, hT, -⟩ := gen_iota hg'
      have hh : (Pattern.app (.varN (.const rec) m) (.varN (.const c') n)).head = rec := by
        simp [head, head_varN]
      rw [hh] at h1 hA
      cases h1.symm.trans h1'
      cases hA with
      | app hA =>
        rw [Arity.const_varN hA]
        exact ⟨Hs ++ [.const I us], Bmaj, by simp [hHs], by rw [List.foldr_append]; exact hT⟩
    · cases hg

namespace SExpr
variable [Params]

/-! ## Part B: the `SExpr`-level spec lemmas of `Pattern.gen` (D4 (a)-(g)) -/

theorem mkInst_foldl_app {ls : List SLevel} : ∀ (xs : List VExpr) (h : VExpr),
    mkInst ls (xs.foldl .app h) = spine (mkInst ls h) (xs.map (mkInst ls))
  | [], _ => rfl
  | x :: xs, h => mkInst_foldl_app xs (.app h x)

theorem spine_subst {σ : Subst} : ∀ (xs : List SExpr) (h : SExpr),
    (spine h xs).subst σ = spine (h.subst σ) (xs.map (·.subst σ))
  | [], _ => rfl
  | x :: xs, h => spine_subst xs (.app h x)

theorem mkInst_foldr_forallE {ls : List SLevel} : ∀ (Hs : List VExpr) (B : VExpr),
    mkInst ls (Hs.foldr .forallE B) = (Hs.map (mkInst ls)).foldr .forallE (mkInst ls B)
  | [], _ => rfl
  | H :: Hs, B => by simp only [List.foldr_cons, List.map_cons, mkInst, mkInst_foldr_forallE Hs B]

theorem SLevel.instV_param {ls : List SLevel} {i : Nat} (h : i < ls.length) :
    SLevel.instV ls (.param i) = ls[i] := by
  apply Subtype.ext; funext v
  simp [SLevel.instV, VLevel.eval, List.getD_eq_getElem?_getD, h]

/-- A constant's own level parameters, instantiated at `ls` (of the right length), are `ls`. -/
theorem SLevel.map_instV_params {ls : List SLevel} {k : Nat} (h : ls.length = k) :
    (VLevel.params k).map (SLevel.instV ls) = ls := by
  subst h
  apply List.ext_getElem (by simp [VLevel.params])
  intro i h1 h2
  simp only [VLevel.params, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply]
  exact SLevel.instV_param h2

theorem SLevel.instV_inst {ls : List SLevel} {us : List VLevel} {l : VLevel} :
    SLevel.instV ls (l.inst us) = SLevel.instV (us.map (SLevel.instV ls)) l := by
  apply Subtype.ext; funext v
  simp only [SLevel.instV, VLevel.eval_inst, List.map_map, Function.comp_def]

/-- `mkInst ls (e.instL us) = mkInst (us.map (instV ls)) e` (`plan/SelfType.lean`). -/
theorem mkInst_instL {ls : List SLevel} {us : List VLevel} :
    ∀ {e : VExpr}, mkInst ls (e.instL us) = mkInst (us.map (SLevel.instV ls)) e
  | .bvar _ => rfl
  | .sort u => by simp only [VExpr.instL, mkInst, SLevel.instV_inst]
  | .const c vs => by
    simp only [VExpr.instL, mkInst, List.map_map, Function.comp_def, SLevel.instV_inst]
  | .app f a | .lam f a | .forallE f a => by
    simp only [VExpr.instL, mkInst, mkInst_instL (e := f), mkInst_instL (e := a)]

/-- Spec lemma (a) `gen_head`: the recursor's type is `m` syntactic binders `Hs` then the major
binder at `const I us`; `c'` is a constructor of arity `n`, whose `ctor_syn` telescope `Ts` gives
the field types `Fs = Ts.map (instL us)` (the field telescope at the major domain's levels `us`;
stage 1a has no term parameters, so "at the parameter variables" is the level instantiation);
`g.ctx = Fs.reverse ++ Hs.reverse`. -/
theorem _root_.Lean4Lean.Pattern.gen_head {rank : Name → Nat} {rec c' : Name} {m n : Nat}
    {r : (Pattern.app (.varN (.const rec) m) (.varN (.const c') n)).RHS} {g : PatGen}
    (hg : Pattern.gen Params.env rank Params.classify
      (.app (.varN (.const rec) m) (.varN (.const c') n)) r = some g)
    {ci : VConstant} (h1 : Params.env.constants rec = some ci) :
    ∃ (Hs : List VExpr) (I : Name) (us : List VLevel) (Bmaj : VExpr),
      Hs.length = m ∧ ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj) ∧
      Params.classify c' = some (.ctor n) ∧
      ∃ (ci' : VConstant) (I' : Name) (Ts args : List VExpr),
        Params.env.constants c' = some ci' ∧ Ts.length = n ∧
        Params.classify I' = some (.indTy args.length) ∧
        ci'.type = Ts.foldr .forallE
          (args.foldr (fun A acc => acc.app A) (.const I' (VLevel.params ci'.uvars))) ∧
        g.ctx = (Ts.map (·.instL us)).reverse ++ Hs.reverse := by
  obtain ⟨ci₁, Hs, I, us, Bmaj, ci', Fs, X, h1', hHs, hT, hcl, hci', hFs, hX, hc⟩ :=
    Pattern.gen_iota hg
  cases h1.symm.trans h1'
  obtain ⟨I', Ts, args, hTs, hI', hty⟩ := Params.ctor_syn (cl := .ctor n) rfl hcl hci'
  have hTs : Ts.length = n := hTs
  refine ⟨Hs, I, us, Bmaj, hHs, hT, hcl, ci', I', Ts, args, hci', hTs, hI', hty, ?_⟩
  rw [hty, VExpr.instL_foldr_forallE] at hX
  obtain ⟨hF, -⟩ := VExpr.foldr_forallE_inj (by simp [hTs, hFs]) hX
  obtain ⟨_, _, rfl⟩ := Pattern.genCore_eq_some.1 hc
  rw [hF]

/-- Spec lemma (b) `gen_lhs`: under any `σ` (in particular `σ_p`, `σ_p (genIdx path) = m2 path`),
the LHS is the recursor spine at `σ (n+m-1) … σ n` applied to the ctor spine
`c' σ (n-1) … σ 0`, the ctor at the major domain's levels `us` (instantiated at `ls`). The
`openSpine rec ls (m+1)` form is `Pattern.gen_lhs_openSpine` (Part E). -/
theorem _root_.Lean4Lean.Pattern.gen_lhs {env : VEnv} {rank : Name → Nat} {classify}
    {rec c' : Name} {m n : Nat}
    {r : (Pattern.app (.varN (.const rec) m) (.varN (.const c') n)).RHS} {g : PatGen}
    (hg : Pattern.gen env rank classify (.app (.varN (.const rec) m) (.varN (.const c') n)) r = some g)
    {ci : VConstant} (h1 : env.constants rec = some ci)
    {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr} (hHs : Hs.length = m)
    (hT : ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj))
    {ls : List SLevel} (hls : ls.length = ci.uvars) (σ : Subst) :
    (mkInst ls g.lhs).subst σ =
      .app (spine (.const rec ls) ((List.range m).reverse.map fun i => σ (n + i)))
        (spine (.const c' (us.map (SLevel.instV ls))) ((List.range n).reverse.map σ)) := by
  obtain ⟨ci₁, Hs₁, I₁, us₁, Bmaj₁, ci', Fs, X, h1', hHs₁, hT₁, -, -, -, -, hc⟩ :=
    Pattern.gen_iota hg
  cases h1.symm.trans h1'
  subst hHs
  obtain ⟨-, he⟩ := VExpr.foldr_forallE_inj hHs₁.symm (hT.symm.trans hT₁)
  injection he with he1 he2
  injection he1 with _ he3
  subst he2 he3
  obtain ⟨_, _, rfl⟩ := Pattern.genCore_eq_some.1 hc
  simp only [mkInst, mkInst_foldl_app, SExpr.subst, spine_subst, List.map_map, Function.comp_def,
    SLevel.map_instV_params hls]

/-- The RHS with no self-abstraction, under `σ_p`. -/
theorem _root_.Lean4Lean.Pattern.RHS.toOpen_subst {p : Pattern} (idx : p.Path → Nat)
    (ls : List SLevel) {m2 : p.Path → SExpr} {σ : Subst} (hidx : ∀ path, σ (idx path) = m2 path) :
    ∀ r : p.RHS, (mkInst ls (r.toOpen idx)).subst σ = r.applyS ls m2
  | .fixed e cl => cl.mkInstS.subst_eq .zero
  | .var path => hidx path
  | .app f a => by
    simp only [Pattern.RHS.toOpen, Pattern.RHS.applyS, mkInst, SExpr.subst,
      toOpen_subst idx ls hidx f, toOpen_subst idx ls hidx a]

/-- Spec lemma (c) `RHS.toVExpr_subst`, per occurrence (replaces Measure6.lean:467, whose `self`
was keyed by `VExpr`), general form: if `σ` maps the `i`-th same-rank occurrence `(c, us)`
(numbered from `j`) to `mkInst ls (.const c us) = .const c (us.map (instV ls))` and
`σ (s + idx path) = m2 path`, the abstracted RHS under `σ` is the RHS instance. -/
theorem _root_.Lean4Lean.Pattern.RHS.toVExpr_subst {p : Pattern} (rank : Name → Nat) (k : Nat)
    (idx : p.Path → Nat) (s : Nat) (ls : List SLevel) {m2 : p.Path → SExpr} {σ : Subst}
    (hidx : ∀ path, σ (s + idx path) = m2 path) :
    ∀ (r : p.RHS) (j : Nat),
      (∀ (i : Nat) c us, (r.selfOccs rank k)[i]? = some (c, us) →
        σ (j + i) = .const c (us.map (SLevel.instV ls))) →
      (mkInst ls (r.toVExpr (VExpr.selfConst? rank k) idx s j)).subst σ = r.applyS ls m2
  | .fixed e cl, j, hself => by
    simp only [Pattern.RHS.toVExpr, Pattern.RHS.applyS]
    cases hs : e.selfConst? rank k with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      exact cl.mkInstS.subst_eq .zero
    | some x =>
      obtain ⟨c, us⟩ := x
      obtain ⟨rfl, -⟩ := VExpr.selfConst?_eq_some.1 hs
      simp only [Option.isSome_some, ↓reduceIte, mkInst, SExpr.subst]
      exact hself 0 c us (by simp [Pattern.RHS.selfOccs, Pattern.RHS.selfConsts, hs])
  | .var path, _, _ => by
    simp only [Pattern.RHS.toVExpr, Pattern.RHS.applyS, mkInst, SExpr.subst, hidx]
  | .app f a, j, hself => by
    simp only [Pattern.RHS.toVExpr, Pattern.RHS.applyS, mkInst, SExpr.subst]
    rw [toVExpr_subst rank k idx s ls hidx f j fun i c us h => hself i c us (by
          simp only [Pattern.RHS.selfOccs, Pattern.RHS.selfConsts]
          rw [List.getElem?_append_left]; · exact h
          exact (List.getElem?_eq_some_iff.1 h).1),
        toVExpr_subst rank k idx s ls hidx a _ fun i c us h => by
          rw [Nat.add_assoc]; exact hself _ c us (by
            simp only [Pattern.RHS.selfOccs, Pattern.RHS.selfConsts]
            rw [List.getElem?_append_right (Nat.le_add_right ..)]; simpa using h)]

/-- Spec lemma (c) at `g` (`gen_rhsAbs`): `(mkInst ls g.rhsAbs).subst (selfσ ++ σ_p) =
r.applyS ls m2`, stated for one substitution `σ` playing `selfσ ++ σ_p`: `σ j` is the `j`-th
same-rank bare-leaf occurrence `mkInst ls (.const c' us)` (in `gen_self`'s order), and
`σ (g.self.length + genIdx path) = m2 path` (`σ_p` shifted past the self variables). -/
theorem _root_.Lean4Lean.Pattern.gen_rhsAbs {env : VEnv} {rank : Name → Nat} {classify}
    {p : Pattern} {r : p.RHS} {g : PatGen} (hg : Pattern.gen env rank classify p r = some g)
    (ls : List SLevel) {m2 : p.Path → SExpr} {σ : Subst}
    (hself : ∀ (j : Nat) c' us, (r.selfOccs rank (rank p.head))[j]? = some (c', us) →
      σ j = .const c' (us.map (SLevel.instV ls)))
    (hidx : ∀ path, σ (g.self.length + p.genIdx path) = m2 path) :
    (mkInst ls g.rhsAbs).subst σ = r.applyS ls m2 := by
  rw [(Pattern.gen_rhs_eq hg).2]
  exact Pattern.RHS.toVExpr_subst _ _ _ _ ls hidx r 0 fun i c us h => by
    rw [Nat.zero_add]; exact hself i c us h

/-- Spec lemma (f) `gen_rhs`: `(mkInst ls g.rhs).subst σ_p = r.applyS ls m2`. D4 step 5 rewrites
`pat_defeq`'s `rhs` with it. (`rhs` is D4's primary choice: the RHS with each path mapped to
`bvar (genIdx path)` and every fixed leaf kept, no self-abstraction.) -/
theorem _root_.Lean4Lean.Pattern.gen_rhs {env : VEnv} {rank : Name → Nat} {classify}
    {p : Pattern} {r : p.RHS} {g : PatGen} (hg : Pattern.gen env rank classify p r = some g)
    (ls : List SLevel) {m2 : p.Path → SExpr} {σ : Subst}
    (hidx : ∀ path, σ (p.genIdx path) = m2 path) :
    (mkInst ls g.rhs).subst σ = r.applyS ls m2 := by
  rw [(Pattern.gen_rhs_eq hg).1]
  exact Pattern.RHS.toOpen_subst _ ls hidx r

/-- Spec lemma (g), `mkInst` form: the `j`-th self entry, at `mkInst ls`, is `ConstGoal`'s type
`mkInst ls' ci'.type` at the occurrence's levels `ls' = us.map (instV ls)`
(`mkInst ls (.const c' us) = .const c' ls'` by `rfl`). -/
theorem _root_.Lean4Lean.Pattern.gen_self' {env : VEnv} {rank : Name → Nat} {classify}
    {p : Pattern} {r : p.RHS} {g : PatGen} (hg : Pattern.gen env rank classify p r = some g)
    {j : Nat} {c' : Name} {us : List VLevel}
    (hj : (r.selfOccs rank (rank p.head))[j]? = some (c', us)) :
    ∃ ci', env.constants c' = some ci' ∧ rank c' = rank p.head ∧
      g.self[j]? = some (ci'.type.instL us) ∧
      ∀ ls, mkInst ls (ci'.type.instL us) = mkInst (us.map (SLevel.instV ls)) ci'.type := by
  obtain ⟨ci', h1, h2, h3⟩ := (Pattern.gen_self hg).2 j c' us hj
  exact ⟨ci', h1, h2, h3, fun _ => mkInst_instL⟩

/-- Spec lemma (e), `mkInst` form (for `Const.beyond`'s `hT`). -/
theorem _root_.Lean4Lean.Pattern.gen_arity_mkInst {env : VEnv} {rank : Name → Nat} {classify}
    {p : Pattern} {r : p.RHS} {g : PatGen} (hg : Pattern.gen env rank classify p r = some g)
    {k : Nat} (hA : Arity (.const p.head) k p) {ci : VConstant}
    (h1 : env.constants p.head = some ci) (ls : List SLevel) :
    ∃ (Hs : List SExpr) (B : SExpr), Hs.length = k ∧ mkInst ls ci.type = Hs.foldr .forallE B := by
  obtain ⟨Hs, B, h2, h3⟩ := Pattern.gen_arity hg hA h1
  exact ⟨Hs.map (mkInst ls), mkInst ls B, by simp [h2], h3 ▸ mkInst_foldr_forallE Hs B⟩

/-! ## Part C: the `Params` field package (D4/D3) and `EnvStrongR` -/

/-- The D4/D3 `Params` fields (stage 1a), as a scratch structure over `[Params]` (as
Measure.lean did). R5 adds them to `class Params` with `env`/`classify`/`Pat` the class's own;
E4's `ParamsR` must list exactly these. -/
structure RankParams where
  rank : Name → Nat
  rank_ordered : ∀ k, (Params.env.below rank k).Ordered
  type_below : ∀ {c ci}, Params.env.constants c = some ci →
    (Params.env.below rank (rank c)).IsType ci.uvars [] ci.type
  pat_rank : ∀ {p : Pattern} {r : p.RHS × p.Check} {c' us}, Params.Pat p r →
    VExpr.const c' us ∈ r.1.fixedLeaves → rank c' ≤ rank p.head
  pat_gen : ∀ {p : Pattern} {r : p.RHS × p.Check}, Params.Pat p r →
    (Pattern.gen Params.env rank Params.classify p r.1).isSome
  pat_typed : ∀ {p : Pattern} {r : p.RHS × p.Check} {g ci}, Params.Pat p r →
    Pattern.gen Params.env rank Params.classify p r.1 = some g →
    Params.env.constants p.head = some ci →
    OnCtx (g.self ++ g.ctx) (fun Γ A => (Params.env.below rank (rank p.head)).IsType ci.uvars Γ A) ∧
    (Params.env.below rank (rank p.head)).HasType ci.uvars (g.self ++ g.ctx) g.rhsAbs
      (g.type.liftN g.self.length)
  pat_defeq : ∀ {p : Pattern} {r : p.RHS × p.Check} {g ci}, Params.Pat p r →
    Pattern.gen Params.env rank Params.classify p r.1 = some g →
    Params.env.constants p.head = some ci →
    Params.env.IsDefEq ci.uvars g.ctx g.lhs g.rhs g.type
  /-- stage 1a only -/
  pat_check : ∀ {p : Pattern} {r : p.RHS × p.Check}, Params.Pat p r → r.2 = .true
  /-- stage-1a restriction (D3), not a kernel invariant -/
  indTy_closed : ∀ {I k ci}, Params.classify I = some (.indTy k) → Params.env.constants I = some ci →
    k = 0 ∧ ∃ u, ci.type = .sort u
  /-- stage-1a restriction (D3), not a kernel invariant -/
  ctor_fields_closed : ∀ {c : Name} {cl : Classification} {ci : VConstant},
    (cl matches .ctor .. | .etaCtor ..) → Params.classify c = some cl →
    Params.env.constants c = some ci →
    ∃ (I : Name) (Ts : List VExpr), ci.type = Ts.foldr .forallE (.const I (VLevel.params ci.uvars)) ∧
      ∀ T ∈ Ts, ∃ I' us, T = .const I' us ∧ Params.classify I' = some (.indTy 0)

/-- Spec lemma (e) `gen_arity`, for any `Pat` (delta too), via `pat_gen`: the head's type has at
least the pattern arity many syntactic Π-binders (likewise `mkInst ls ci.type`). Used by
`Const.beyond` (R9). -/
theorem RankParams.gen_arity (RP : RankParams) {p : Pattern} {r : p.RHS × p.Check} {k : Nat}
    {ci : VConstant} (hP : Params.Pat p r) (hA : Arity (.const p.head) k p)
    (h1 : Params.env.constants p.head = some ci) :
    ∃ (Hs : List VExpr) (B : VExpr), Hs.length = k ∧ ci.type = Hs.foldr .forallE B ∧
      ∀ ls, mkInst ls ci.type = (Hs.map (mkInst ls)).foldr .forallE (mkInst ls B) := by
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 (RP.pat_gen hP)
  obtain ⟨Hs, B, h2, h3⟩ := Pattern.gen_arity hg hA h1
  exact ⟨Hs, B, h2, h3, fun _ => h3 ▸ mkInst_foldr_forallE Hs B⟩

theorem onCtx_levelWF_instL {vs : List VLevel} (hvs : ∀ l ∈ vs, l.WF Params.univs) :
    ∀ Γ : List VExpr, OnCtx (Γ.map (VExpr.instL vs)) (fun _ A => A.LevelWF Params.univs)
  | [] => trivial
  | _ :: Γ => ⟨onCtx_levelWF_instL hvs Γ, VExpr.LevelWF.instL hvs⟩

theorem map_mkInst_map_mk {vs : List VLevel} (hvs : ∀ l ∈ vs, l.WF Params.univs) (Γ : List VExpr) :
    Γ.map (mkInst (vs.map SLevel.mk)) = (Γ.map (VExpr.instL vs)).map mk := by
  simp only [List.map_map]; exact List.map_congr_left fun _ _ => mkInst_map_mk hvs

/-- A VExpr typing in the rank prefix `below rank k`, under a typed context, as a strong
`SExpr` derivation over `below rank k` at any levels: `VEnv.IsDefEq.strong` (`rank_ordered`)
→ `instL` → the repo's `mkSE` (with `CtorProviderE.synE (below_le ..)`). -/
theorem RankParams.strongR (RP : RankParams) {k U : Nat} {Γ : List VExpr} {e A : VExpr}
    (hΓ : OnCtx Γ ((Params.env.below RP.rank k).IsType U))
    (H : (Params.env.below RP.rank k).HasType U Γ e A) (ls : List SLevel) :
    IsDefEqStrong (Params.env.below RP.rank k) (Γ.map (mkInst ls)) (mkInst ls e) (mkInst ls e)
      (mkInst ls A) := by
  obtain ⟨vs, hvs, rfl⟩ := SLevel.exists_map_mk ls
  have hS := (VEnv.IsDefEq.strong (RP.rank_ordered k) hΓ H).instL hvs
  have := hS.mkSE (CtorProviderE.synE (Params.env.below_le ..)) (onCtx_levelWF_instL hvs Γ)
  rw [map_mkInst_map_mk hvs, mkInst_map_mk hvs, mkInst_map_mk hvs]
  exact this

/-- Rank-bounded strong typings (D4; replaces Measure.lean's `EnvStrongR`, which used `Block`):
the type of each constant `c` in the prefix `below rank (rank c)`, and each rule's generated
context entries and abstracted RHS in the prefix `below rank (rank p.head)`, at any levels. -/
structure EnvStrongR (RP : RankParams) : Prop where
  const : ∀ {c ci} (ls : List SLevel), Params.env.constants c = some ci →
    ∃ u, IsDefEqStrong (Params.env.below RP.rank (RP.rank c)) []
      (mkInst ls ci.type) (mkInst ls ci.type) (.sort u)
  pat_ctx : ∀ {p : Pattern} {r : p.RHS × p.Check} {g ci} (ls : List SLevel) {Δ Γ : List VExpr} {A},
    Params.Pat p r → Pattern.gen Params.env RP.rank Params.classify p r.1 = some g →
    Params.env.constants p.head = some ci → g.self ++ g.ctx = Δ ++ A :: Γ →
    ∃ u, IsDefEqStrong (Params.env.below RP.rank (RP.rank p.head)) (Γ.map (mkInst ls))
      (mkInst ls A) (mkInst ls A) (.sort u)
  pat_rhs : ∀ {p : Pattern} {r : p.RHS × p.Check} {g ci} (ls : List SLevel),
    Params.Pat p r → Pattern.gen Params.env RP.rank Params.classify p r.1 = some g →
    Params.env.constants p.head = some ci →
    IsDefEqStrong (Params.env.below RP.rank (RP.rank p.head)) ((g.self ++ g.ctx).map (mkInst ls))
      (mkInst ls g.rhsAbs) (mkInst ls g.rhsAbs) (mkInst ls (g.type.liftN g.self.length))

/-- `EnvStrongR` from the `Params` fields (Measure6.lean:298 pattern): `type_below`/`pat_typed`,
then `VEnv.IsDefEq.strong` (`rank_ordered`), `instL` and the repo's `mkSE` (no `hE`). -/
theorem EnvStrongR.of_params (RP : RankParams) : EnvStrongR RP where
  const := fun ls h1 => by
    obtain ⟨u, hu⟩ := RP.type_below h1
    exact ⟨_, RP.strongR (Γ := []) trivial hu ls⟩
  pat_ctx := fun {p r g ci} ls {Δ Γ A} hP hg h1 heq => by
    have hc := (RP.pat_typed hP hg h1).1
    rw [heq] at hc
    -- the suffix `A :: Γ` of the context (inline: the repo's `OnCtx.of_append` lives in
    -- `Lean4Lean.Verify`, which this module does not import)
    have hc' : OnCtx (A :: Γ)
        (fun Γ A => (Params.env.below RP.rank (RP.rank p.head)).IsType ci.uvars Γ A) := by
      clear heq; induction Δ with
      | nil => exact hc
      | cons _ Δ ih => exact ih hc.1
    obtain ⟨hΓ, u, hA⟩ := hc'
    exact ⟨_, RP.strongR hΓ hA ls⟩
  pat_rhs := fun ls hP hg h1 =>
    have ⟨hc, H⟩ := RP.pat_typed hP hg h1
    RP.strongR hc H ls

/-- The spine lemma's lam-case domain chain (D4; R9): `EnvStrongR.const` (from `type_below`
via `rank_ordered`, `strong`, `instL`, `mkSE`) rewritten with `hT`, then the repo's
`IsDefEqStrong.telescope`: every domain of the syntactic telescope, and its codomain, strongly
typed in `below rank (rank c)`, in its own telescope context; `weak_append` then moves each to
`… ++ Γ₀`, and `.mono (below_le ..)` to `Params.env` for `Adequate.cons`. -/
theorem EnvStrongR.const_telescope {RP : RankParams} (envR : EnvStrongR RP) {c : Name}
    {ci : VConstant} {ls : List SLevel} (h1 : Params.env.constants c = some ci)
    {Ts : List SExpr} {B : SExpr} (hT : mkInst ls ci.type = Ts.foldr .forallE B) :
    TelStrongE (Params.env.below RP.rank (RP.rank c)) [] Ts B := by
  obtain ⟨u, H⟩ := envR.const ls h1
  rw [hT] at H
  exact IsDefEqStrong.telescope H

/-! ## Part D: the measure (D4). Outer: well-founded on the rank bound `k` (`LR.WFIH`). Middle:
structural on `H : IsDefEqStrong (below k)` (the 13 existing cases; R7). Inner, const case only:
structural on `hM : LE_Interp ρ mT M` (`LR.const_local`), with the local IH restricted to
same-rank bare-constant leaves (`LR.LocalIH`, no `Block`); then `Const`/`RHS` in `const_spine`. -/

/-- `const c ls (bvar (k-1)) … (bvar 0)` (docs/const-case/CtorClause.lean:102). -/
def openSpine (c : Name) (ls : List SLevel) (k : Nat) : SExpr :=
  spine (.const c ls) ((List.range k).reverse.map .bvar)

/-- Telescope valuation (docs/const-case/CtorClause.lean:106). -/
def Valuation.ofRargs {n} (rargs : List (WShape n)) : Valuation :=
  rargs.foldr (fun x ρ => ρ.push x.T) .nil

/-- The WF IH of `LR.adequacy_rank` at bound `k` (D4). -/
def LR.WFIH (rank : Name → Nat) (Γ₀ : List SExpr) (k : Nat) : Prop :=
  ∀ k' < k, ∀ {Γ M N A}, IsDefEqStrong (Params.env.below rank k') Γ M N A →
    ∀ {ρ n} {m a : WShape n}, LE_Interp ρ m.T M → LE_Interp ρ a.T A → m.HasType a →
      LR.Adequate Γ₀ Γ ρ M N A m a

/-- `LR.const_local`'s conclusion (D4) for `hM : LE_Interp ρ mT (.const c ls)`: `⊥`, or an
∃-typed upper bound `m'` (what `SubstWF.cons` can push for a self occurrence,
`plan/HasTypeGap.lean`) at which the constant is related at every typed shape below. -/
def LR.ConstGoal (Γ₀ : List SExpr) (ρ : Valuation) (mT : TShape) (c : Name) (ls : List SLevel)
    (ci : VConstant) : Prop :=
  (∃ n, mT = (WShape.bot (n := n)).T) ∨
  ∃ (n : Nat) (m' a' : WShape n), mT ≤ m'.T ∧ m'.HasType a' ∧ LE_Interp ρ a'.T (mkInst ls ci.type) ∧
    ∀ {n'} (m a : WShape n'), m.T ≤ m'.T → LE_Interp ρ a.T (mkInst ls ci.type) → m.HasType a →
      (LR Γ₀).DefEq (.const c ls) (.const c ls) (mkInst ls ci.type) m a

/-- The local IH for the `R`-premise of `LE_Interp.const` (D4): same-rank bare-constant leaves
(`rank c' = rank c`; no `Block`, no same-block restriction). -/
def LR.LocalIH (rank : Name → Nat) (Γ₀ : List SExpr) (ρ₀ : Valuation) (c : Name)
    (R : TShape → SExpr → Prop) : Prop :=
  ∀ m e, R m e → ∀ c' ls' ci', e = .const c' ls' → rank c' = rank c →
    Params.env.constants c' = some ci' → ls'.length = ci'.uvars → LR.ConstGoal Γ₀ ρ₀ m c' ls' ci'

/-- The spine lemma (item R9; D4, `plan/historical/PatLeafStmt2.lean` with `rank := RP.rank` and
the repo's `IsDefEqStrong E`): induction on `Const`, at every valuation above the telescope
valuation that a `SubstWF` covers, goal at every typed shape below. -/
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

/-- The E6 interface (R10 proves exactly this; R9 calls it at `Const.pat` with `hg` from
`RP.pat_gen`, `hty` from `RP.pat_typed`, `hdef` from `RP.pat_defeq`). Statement as
`plan/historical/PatLeafStmt2.lean:168` with the real `Pattern.gen`, `rank := RP.rank` and the
repo's `IsDefEqStrong E`. -/
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

/-- Semantic type validity of a constant's type (Measure.lean `const_local` step (i)):
`EnvStrongR.const` (from `type_below`) → `weak0` to `Γ₀`, then the WF IH at `rank c < k` and
`LR.toValTy`. -/
theorem LR.constType_valid (RP : RankParams) {Γ₀ : List SExpr} {k : Nat}
    (WFIH : LR.WFIH RP.rank Γ₀ k) (hΓ₀ : ⊢ Γ₀) {c : Name} {ci : VConstant} {ls : List SLevel}
    (hc : RP.rank c < k) (h1 : Params.env.constants c = some ci)
    {ρ : Valuation} {n : Nat} {a : WShape n}
    (hA : LE_Interp ρ a.T (mkInst ls ci.type)) (ht : a.HasType .type) :
    (LR Γ₀).TyDefEq (mkInst ls ci.type) (mkInst ls ci.type) a := by
  obtain ⟨u, H₀⟩ := (EnvStrongR.of_params RP).const ls h1
  have Hty := H₀.weak0 (Γ := Γ₀)
  have hcl := (Params.henv.closedC h1).mkInstS (ls := ls)
  have hA₀ : LE_Interp .nil a.T (mkInst ls ci.type) := (LE_Interp.closed_iff hcl).1 hA
  obtain ⟨n', a', s, le_n, le_a, hA', hS', hmem'⟩ :=
    (LE_Interp.soundSE (Params.env.below_le ..) Hty .nil).2 hA₀ |>.out
  have tyDE := (WFIH _ hc Hty hA' hS' hmem').2 (LR.SubstWF.id hΓ₀)
  simp only [subst_id] at tyDE
  exact LR.toValTy le_n le_a ht hS' hmem' tyDE

/-- The local induction (D4): induction on `hM` through the `R`-closure of `LE_Interp.const`.
Its only recursive calls are the local IH `ih7` on the `R`-premise's sub-derivations (handed to
`const_spine` as `LR.LocalIH`, same rank) and the WF IH at `rank c ≤ rank c₀ < k` (type
validity, `constType_valid`; and inside `const_spine`). `hc₀ : rank c₀ < k` comes from
`(below k).constants c₀ = some _` at the outer `const` node (R8 wires it at `c₀ := c`). -/
theorem LR.const_local (RP : RankParams) {Γ₀ : List SExpr} {k : Nat} {c₀ : Name}
    (WFIH : LR.WFIH RP.rank Γ₀ k) (hΓ₀ : ⊢ Γ₀) (hc₀ : RP.rank c₀ < k) :
    ∀ {ρ mT M} (_hM : LE_Interp ρ mT M) {c ls ci}, M = .const c ls → RP.rank c ≤ RP.rank c₀ →
      Params.env.constants c = some ci → ls.length = ci.uvars →
      LR.ConstGoal Γ₀ ρ mT c ls ci := by
  intro ρ mT M hM
  induction hM with
  | bot => intro c ls ci _ _ _ _; exact .inl ⟨_, rfl⟩
  | @const _ c ci _ m' ρ aT ls R h1 h2 h3 h4 h5 h6 _ _ ih7 =>
    intro c₁ ls₁ ci₁ eM hrk h1' hlen
    cases eM; cases h1.symm.trans h1'
    have hc : RP.rank c < k := Nat.lt_of_le_of_lt hrk hc₀
    -- the local IH, same rank (no `Block`): `ih7` on the `R`-premise's sub-derivations
    have LIH : LR.LocalIH RP.rank Γ₀ ρ c R := fun m e hR c' ls' ci' he hr h1'' h2'' =>
      ih7 m e hR he (Nat.le_trans (Nat.le_of_eq hr) hrk) h1'' h2''
    -- the typed upper bound `m'` of the derivation, at a common level
    have hK := Nat.max_le.1 (Nat.le_refl (max m'.1 aT.1))
    refine .inr ⟨_, m'.2.lift _, aT.2.lift _, h3.trans (TShape.lift_eqv hK.1).2,
      (TShape.HasType.def hK.1 hK.2).1 h4, h5.mono (TShape.lift_eqv hK.2).1, ?_⟩
    intro n' m₁ a₁ hle hA hmem
    have hcl := (Params.henv.closedC h1).mkInstS (ls := ls)
    have hA₀ : LE_Interp .nil a₁.T (mkInst ls ci.type) := (LE_Interp.closed_iff hcl).1 hA
    -- type validity: the WF IH at `rank c < k`
    have tyV := LR.constType_valid RP WFIH hΓ₀ hc h1 hA hmem.isType
    -- the spine lemma at the empty spine, `σ = σ' = id`
    have := LR.const_spine RP WFIH hc h1 hlen LIH h6 (Ts := []) (B := mkInst ls ci.type) rfl rfl
      (ρ := .nil) Valuation.LE.rfl (LR.SubstWF.id hΓ₀) (hle.trans (TShape.lift_eqv hK.1).1) hA₀
      hmem (fun _ => by rw [hcl.subst_eq .zero, hcl.subst_eq .zero]; exact tyV)
    simpa [openSpine] using this
  | _ => intro c ls ci eM; cases eM

/-- `LR.adequacy_rank`'s well-founded induction (D4 measure level (1)): a step that proves
adequacy at bound `k` from `LR.WFIH rank Γ₀ k` gives it at every bound. -/
theorem LR.adequacy_rank_wf (rank : Name → Nat) {Γ₀ : List SExpr}
    (step : ∀ k, LR.WFIH rank Γ₀ k → ∀ {Γ M N A}, IsDefEqStrong (Params.env.below rank k) Γ M N A →
      ∀ {ρ n} {m a : WShape n}, LE_Interp ρ m.T M → LE_Interp ρ a.T A → m.HasType a →
        LR.Adequate Γ₀ Γ ρ M N A m a) :
    ∀ k {Γ M N A}, IsDefEqStrong (Params.env.below rank k) Γ M N A →
      ∀ {ρ n} {m a : WShape n}, LE_Interp ρ m.T M → LE_Interp ρ a.T A → m.HasType a →
        LR.Adequate Γ₀ Γ ρ M N A m a := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih => exact step k fun k' hk => ih k' hk

/-- `LR.adequacy` is recovered from the rank-indexed form through the repo's `exists_below`
(D4: "`LR.adequacy` (148) is recovered from `(H.strong hΓ).exists_below Params.rank`"). -/
theorem LR.adequacy_of_rank (rank : Name → Nat) {Γ₀ : List SExpr}
    (hrank : ∀ k {Γ M N A}, IsDefEqStrong (Params.env.below rank k) Γ M N A →
      ∀ {ρ n} {m a : WShape n}, LE_Interp ρ m.T M → LE_Interp ρ a.T A → m.HasType a →
        LR.Adequate Γ₀ Γ ρ M N A m a)
    {M N A : SExpr} {Γ : List SExpr} (hΓ : ⊢ Γ) (H : Γ ⊢ M ≡ N : A) {ρ n} {m a : WShape n}
    (hM : LE_Interp ρ m.T M) (hA : LE_Interp ρ a.T A) (hmem : m.HasType a) :
    LR.Adequate Γ₀ Γ ρ M N A m a :=
  let ⟨_, H'⟩ := (H.strong hΓ).exists_below rank
  hrank _ H' hM hA hmem

/-! ## Part E: the pat leaf, syntactic half (Measure.lean Part E, ported to `spine`).
`openSpine` forms of (b), the match of the instantiated LHS (`m2 = σ ∘ genIdx`, which supplies
(c)/(f)'s `hidx` through `MatchesS.determ`), the untyped reduction chain major → extra
(D4 step 5, untyped side), and the R8 wiring of the outer `const` case. -/

theorem openSpine_subst (c : Name) (ls : List SLevel) (k : Nat) (σ : Subst) :
    (openSpine c ls k).subst σ = spine (.const c ls) ((List.range k).reverse.map σ) := by
  simp only [openSpine, spine_subst, List.map_map, Function.comp_def, SExpr.subst]

omit [Params] in
theorem range_reverse_succ (k : Nat) :
    (List.range (k+1)).reverse = ((List.range k).reverse.map (· + 1)) ++ [0] := by
  rw [List.range_succ_eq_map, List.reverse_cons, List.map_reverse]

theorem _root_.Lean4Lean.Pattern.gen_lhs_openSpine {env : VEnv} {rank : Name → Nat} {classify}
    {rec c' : Name} {m n : Nat}
    {r : (Pattern.app (.varN (.const rec) m) (.varN (.const c') n)).RHS} {g : PatGen}
    (hg : Pattern.gen env rank classify (.app (.varN (.const rec) m) (.varN (.const c') n)) r = some g)
    {ci : VConstant} (h1 : env.constants rec = some ci)
    {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr} (hHs : Hs.length = m)
    (hT : ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj))
    {ls : List SLevel} (hls : ls.length = ci.uvars) (σ : Subst) :
    (mkInst ls g.lhs).subst σ = (openSpine rec ls (m+1)).subst
      (Subst.cons (fun i => σ (n + i))
        (spine (.const c' (us.map (SLevel.instV ls))) ((List.range n).reverse.map σ))) := by
  rw [Pattern.gen_lhs hg h1 hHs hT hls σ, openSpine_subst, range_reverse_succ, List.map_append,
    List.map_map, List.map_singleton, spine_snoc]
  rfl

/-- `varN (const c) k` matches the open spine instance `c τ(k-1) … τ 0` with `m2 = τ ∘ genIdx`. -/
theorem _root_.Lean4Lean.Pattern.MatchesS.varN_genIdx {c : Name} {ls : List SLevel} :
    ∀ (k : Nat) (τ : Subst),
      (Pattern.varN (.const c) k).MatchesS (spine (.const c ls) ((List.range k).reverse.map τ)) ls
        (fun path => τ ((Pattern.varN (.const c) k).genIdx path))
  | 0, τ => Pattern.MatchesS.congr .const nofun
  | k+1, τ => by
    rw [range_reverse_succ, List.map_append, List.map_map, List.map_singleton, spine_snoc]
    have := (Pattern.MatchesS.varN_genIdx (c := c) (ls := ls) k (fun i => τ (i + 1))).var (a' := τ 0)
    refine this.congr fun path => ?_
    cases path <;> rfl

/-- (b') The instantiated LHS matches the pattern, with `m2 = σ ∘ genIdx` (so, by
`MatchesS.determ`, every match of it has `σ_p (genIdx path) = m2 path`, the hypothesis of (c)/(f)). -/
theorem _root_.Lean4Lean.Pattern.gen_lhs_matches {env : VEnv} {rank : Name → Nat} {classify}
    {rec c' : Name} {m n : Nat}
    {r : (Pattern.app (.varN (.const rec) m) (.varN (.const c') n)).RHS} {g : PatGen}
    (hg : Pattern.gen env rank classify (.app (.varN (.const rec) m) (.varN (.const c') n)) r = some g)
    {ci : VConstant} (h1 : env.constants rec = some ci)
    {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr} (hHs : Hs.length = m)
    (hT : ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj))
    {ls : List SLevel} (hls : ls.length = ci.uvars) (σ : Subst) :
    (Pattern.app (.varN (.const rec) m) (.varN (.const c') n)).MatchesS ((mkInst ls g.lhs).subst σ)
      ls (fun path => σ ((Pattern.app (.varN (.const rec) m) (.varN (.const c') n)).genIdx path)) := by
  rw [Pattern.gen_lhs hg h1 hHs hT hls σ]
  refine ((Pattern.MatchesS.varN_genIdx m (fun i => σ (n + i))).app
    (Pattern.MatchesS.varN_genIdx (ls := us.map (SLevel.instV ls)) n σ)).congr fun path => ?_
  cases path <;> simp [Pattern.genIdx, Pattern.varDepth_varN]

omit [Params] in
theorem _root_.Lean4Lean.Pattern.varN_var (p : Pattern) :
    ∀ n, (Pattern.var p).varN n = (p.varN n).var
  | 0 => rfl
  | n+1 => by simp only [Pattern.varN, varN_var p n]

/-- A `varN` pattern matches any spine of the right length (the arguments are unconstrained). -/
theorem _root_.Lean4Lean.Pattern.MatchesS.spine {q : Pattern} {h : SExpr} {ls}
    {g : q.Path → SExpr} (H : q.MatchesS h ls g) : ∀ xs : List SExpr,
      ∃ g', (q.varN xs.length).MatchesS (SExpr.spine h xs) ls g'
  | [] => ⟨g, H⟩
  | x :: xs => by
    have ⟨g', h'⟩ := Pattern.MatchesS.spine (q := q.var) (H.var (a' := x)) xs
    revert g' h'; rw [Pattern.varN_var]
    exact fun g' h' => ⟨g', h'⟩

/-- `extra` when the rule has no side conditions. -/
theorem WHRed.extra_true {Γ : List SExpr} {p : Pattern} {r : p.RHS × p.Check} {e m1}
    {m2 : p.Path → SExpr} (hP : Params.Pat p r) (hck : r.2 = .true) (hm : p.MatchesS e m1 m2) :
    Γ ⊢ e ⤳ r.1.applyS m1 m2 :=
  WHRed.extra hP hm (dfs := []) (by rw [hck]; rfl) nofun

/-- The reduction half of the pat leaf for an iota rule `rec x₁…xₘ (ctor z₁…zₙ)` (Measure.lean
Part E, over `spine`): once the major premise head-reduces to a syntactic constructor spine, the
whole spine head-reduces to the RHS instance (`WHRedS.major`, `pat_check`). -/
theorem pat_leaf_reduce {Γ : List SExpr} {rec ctor : Name} {m n : Nat}
    {r : (Pattern.app (.varN (.const rec) m) (.varN (.const ctor) n)).RHS ×
      (Pattern.app (.varN (.const rec) m) (.varN (.const ctor) n)).Check}
    (hP : Params.Pat (.app (.varN (.const rec) m) (.varN (.const ctor) n)) r) (hck : r.2 = .true)
    {ls ls' : List SLevel} (xs zs : List SExpr) (hxs : xs.length = m) (hzs : zs.length = n)
    {x_maj : SExpr} (hred : Γ ⊢ x_maj ⤳* spine (.const ctor ls') zs) :
    ∃ m2, Γ ⊢ (spine (.const rec ls) xs).app x_maj ⤳* r.1.applyS ls m2 := by
  subst hxs; subst hzs
  obtain ⟨g1, h1⟩ := Pattern.MatchesS.spine (q := .const rec) (.const (ls := ls)) xs
  obtain ⟨g2, h2⟩ := Pattern.MatchesS.spine (q := .const ctor) (.const (ls := ls')) zs
  have hmaj : IsMajorPremise (spine (.const rec ls) xs) := IsMajorPremise.mk hP h1
  exact ⟨_, .tail (WHRedS.major hmaj hred) (WHRed.extra_true hP hck (h1.app h2))⟩

/-- The `const` case of `LR.adequacy_rank` (R8's wiring, D4): at an outer
`IsDefEqStrong.const` node in `below rank k`, `const_local` at `c₀ := c` (`rank c < k` from
`below_constants_lt`). -/
theorem LR.const_case (RP : RankParams) {Γ₀ Γ : List SExpr} {k : Nat}
    (WFIH : LR.WFIH RP.rank Γ₀ k) {c : Name} {ci : VConstant} {ls : List SLevel}
    (h1 : (Params.env.below RP.rank k).constants c = some ci) (h2 : ls.length = ci.uvars)
    {ρ : Valuation} {n : Nat} {m a : WShape n}
    (hM : LE_Interp ρ m.T (.const c ls)) (hA : LE_Interp ρ a.T (mkInst ls ci.type))
    (hmem : m.HasType a) :
    LR.Adequate Γ₀ Γ ρ (.const c ls) (.const c ls) (mkInst ls ci.type) m a := by
  have hrk := VEnv.below_constants_lt h1
  have h1' := (Params.env.below_le ..).1 h1
  refine .refl fun σ σ' W => ?_
  rw [(Params.henv.closedC h1').mkInstS.subst_eq .zero]
  obtain ⟨n₀, hb⟩ | ⟨n₀, m', a', hle, -, -, H⟩ :=
    LR.const_local RP WFIH W.wf₀ hrk hM rfl (Nat.le_refl _) h1' h2
  · have hb' : m.T ≤ TShape.bot := hb ▸ TShape.bot_eqv.1
    cases show m = .bot from TShape.le_bot.1 hb'
    exact (LR _).bot hmem.isType
  · exact H m a hle hA hmem

end SExpr
end Lean4Lean
