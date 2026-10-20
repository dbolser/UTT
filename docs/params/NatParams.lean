import Lean4Lean.Experimental.SExpr

/-! # Sketch: a `Params` instance for an environment with `ℕ`

`Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec`, and the two iota rules as `SimplePattern.iota`.
Pure syntax.  Everything checkable by `rfl` is checked; every `sorry` is marked `-- SORRY:`
and listed at the end.  (`Theory.Meta`/`Quot` need Batteries, not built in the snapshot,
so `vconst`/`vdefeq` are replaced by a local converter and hand-written rules.) -/

namespace Lean4Lean
open Lean (Name)

namespace NatEnv

/-! ## Constants (de Bruijn) -/

def natTy : VExpr := .const ``Nat []
def natCI  : VConstant := ⟨0, .sort (.succ .zero)⟩            -- Nat : Type
def zeroCI : VConstant := ⟨0, natTy⟩                           -- Nat.zero : Nat
def succCI : VConstant := ⟨0, .forallE natTy natTy⟩            -- Nat.succ : Nat → Nat

/-- binder types of `Nat.rec.{u}`, in the contexts where they occur -/
def motiveTy : VExpr := .forallE natTy (.sort (.param 0))                 -- motive : Nat → Sort u
def zTy : VExpr := .app (.bvar 0) (.const ``Nat.zero [])                  -- [motive] ⊢ motive .zero
def sTy : VExpr := .forallE natTy (.forallE (.app (.bvar 2) (.bvar 0))    -- [motive,z] ⊢
  (.app (.bvar 3) (.app (.const ``Nat.succ []) (.bvar 1))))               --   (n:Nat) → motive n → motive (.succ n)
/-- `Nat.rec.{u} : {motive} → motive .zero → ((n) → motive n → motive (.succ n)) → (t : Nat) → motive t` -/
def recCI : VConstant := ⟨1,
  .forallE motiveTy (.forallE zTy (.forallE sTy (.forallE natTy (.app (.bvar 3) (.bvar 0)))))⟩

/-! ### Cross-check of the encodings against Lean's own declarations -/
section Check
deriving instance DecidableEq for VLevel, VExpr
open Lean in
partial def toV (ls : List Name) : Expr → Option VExpr
  | .bvar i => some (.bvar i)
  | .sort u => (VLevel.ofLevel ls u).map .sort
  | .const c us => (us.mapM (VLevel.ofLevel ls)).map (.const c)
  | .app f a => do return .app (← toV ls f) (← toV ls a)
  | .lam _ t b _ => do return .lam (← toV ls t) (← toV ls b)
  | .forallE _ t b _ => do return .forallE (← toV ls t) (← toV ls b)
  | _ => none
open Lean Elab Command in
#eval show CommandElabM Unit from do
  for (n, ci) in [(``Nat, natCI), (``Nat.zero, zeroCI), (``Nat.succ, succCI), (``Nat.rec, recCI)] do
    let info ← getConstInfo n
    let ok := info.levelParams.length == ci.uvars && toV info.levelParams info.type == some ci.type
    logInfo m!"{n} encoding matches Lean: {ok}"
end Check

/-! ## Classification -/

def classify (c : Name) : Option Classification :=
  if c = ``Nat then some (.indTy 0) else
  if c = ``Nat.zero then some (.ctor 0) else
  if c = ``Nat.succ then some (.ctor 1) else
  if c = ``Nat.rec then some (.symb 4) else none      -- rec: motive, z, s, major

theorem classify_cases (h : classify c = some cl) :
    (c = ``Nat ∧ cl = .indTy 0) ∨ (c = ``Nat.zero ∧ cl = .ctor 0) ∨
    (c = ``Nat.succ ∧ cl = .ctor 1) ∨ (c = ``Nat.rec ∧ cl = .symb 4) := by
  unfold classify at h; repeat' split at h
  all_goals simp_all

/-! ## The two iota patterns -/

/-- `Nat.rec motive z s`: the recursor prefix; the major premise is argument 3. -/
def recPre : Pattern := .var (.var (.var (.const ``Nat.rec)))
def zeroPat : Pattern := (SimplePattern.iota ``Nat.rec 3 ``Nat.zero 0).toPattern
def succPat : Pattern := (SimplePattern.iota ``Nat.rec 3 ``Nat.succ 1).toPattern

example : zeroPat = .app recPre (.const ``Nat.zero) := rfl
example : succPat = .app recPre (.var (.const ``Nat.succ)) := rfl

/-- Paths into `recPre`; the outermost `var` binds the *last* argument (`Matches.var`). -/
def pS      : recPre.Path := none
def pZ      : recPre.Path := some none
def pMotive : recPre.Path := some (some none)

/-- `Nat.rec motive z s Nat.zero ≡ z` -/
def zeroRHS : zeroPat.RHS := .var (.inl pZ)

/-- `Nat.rec motive z s (Nat.succ n) ≡ s n (Nat.rec motive z s n)`;
the recursive call's head is `fixed` and re-instantiated at the matched level. -/
def succRHS : succPat.RHS :=
  let n : succPat.Path := .inr none
  .app (.app (.var (.inl pS)) (.var n))
    (.app (.app (.app (.app (.fixed (.const ``Nat.rec [.param 0]) trivial)
      (.var (.inl pMotive))) (.var (.inl pZ))) (.var (.inl pS))) (.var n))

inductive Pat : (p : Pattern) → p.RHS × p.Check → Prop
  | zero : Pat zeroPat (zeroRHS, .true)
  | succ : Pat succPat (succRHS, .true)

/-- The RHS encodings mean what they should, on an arbitrary instance. -/
theorem zero_instance (u : VLevel) (M Z S : VExpr) : ∃ m2,
    zeroPat.Matches (.app (.app (.app (.app (.const ``Nat.rec [u]) M) Z) S) (.const ``Nat.zero []))
      [u] m2 ∧ zeroRHS.apply [u] m2 = Z :=
  ⟨_, .app (.var (.var (.var .const))) .const, rfl⟩

theorem succ_instance (u : VLevel) (M Z S N : VExpr) : ∃ m2,
    succPat.Matches
      (.app (.app (.app (.app (.const ``Nat.rec [u]) M) Z) S) (.app (.const ``Nat.succ []) N))
      [u] m2 ∧
    succRHS.apply [u] m2 =
      .app (.app S N) (.app (.app (.app (.app (.const ``Nat.rec [u]) M) Z) S) N) :=
  ⟨_, .app (.var (.var (.var .const))) (.var .const), rfl⟩

/-! ## The iota rules as `VDefEq`: the encodings available

(A) Lean4Lean's own convention (what `vdefeq(motive z s => …)` produces, cf. `quotDefEq`):
closed and **lambda-wrapped**.  Typable in `[]`, so compatible with `Ordered`; but
`Pattern.Matches` has no `lam` case, so `extra_patV` is *refuted* by any env containing it. -/
def recApp (motive z s t : VExpr) : VExpr :=
  .app (.app (.app (.app (.const ``Nat.rec [.param 0]) motive) z) s) t

def iotaZeroLam : VDefEq := ⟨1,
  .lam motiveTy (.lam zTy (.lam sTy (recApp (.bvar 2) (.bvar 1) (.bvar 0) (.const ``Nat.zero [])))),
  .lam motiveTy (.lam zTy (.lam sTy (.bvar 1))),
  .forallE motiveTy (.forallE zTy (.forallE sTy (.app (.bvar 2) (.const ``Nat.zero []))))⟩

def iotaSuccLam : VDefEq := ⟨1,
  .lam motiveTy (.lam zTy (.lam sTy (.lam natTy
    (recApp (.bvar 3) (.bvar 2) (.bvar 1) (.app (.const ``Nat.succ []) (.bvar 0)))))),
  .lam motiveTy (.lam zTy (.lam sTy (.lam natTy
    (.app (.app (.bvar 1) (.bvar 0)) (recApp (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)))))),
  .forallE motiveTy (.forallE zTy (.forallE sTy (.forallE natTy
    (.app (.bvar 3) (.app (.const ``Nat.succ []) (.bvar 0))))))⟩

theorem _root_.Lean4Lean.Pattern.not_matches_lam {p : Pattern} {m1 m2} : ¬ p.Matches (.lam A b) m1 m2 := nofun

theorem iotaZeroLam_unmatchable (ls : List VLevel) (p : Pattern) (m1 m2) :
    ¬ p.Matches (iotaZeroLam.lhs.instL ls) m1 m2 := Pattern.not_matches_lam

/-- (B) Open encoding: `bvar`s as the metavariables.  Pattern-matchable, but not
`VDefEq.WF` in any ordered env (well-typed terms in `[]` are closed), hence not `Ordered`. -/
def iotaZeroOpen : VDefEq := ⟨1,
  recApp (.bvar 2) (.bvar 1) (.bvar 0) (.const ``Nat.zero []), .bvar 1,
  .app (.bvar 2) (.const ``Nat.zero [])⟩

theorem iotaZeroOpen_matches : ∃ m2,
    zeroPat.Matches iotaZeroOpen.lhs [.param 0] m2 ∧
    zeroRHS.apply [.param 0] m2 = iotaZeroOpen.rhs :=
  ⟨_, .app (.var (.var (.var .const))) .const, rfl⟩

theorem iotaZeroOpen_not_wf {env : VEnv} (henv : env.Ordered) : ¬ iotaZeroOpen.WF env := by
  intro ⟨h, _⟩
  have := h.closedN henv trivial
  simp [iotaZeroOpen, recApp, VExpr.ClosedN] at this

/-! (C) Finitely many *closed instances* `Nat.rec M Z S Nat.zero ≡ Z` for concrete `M Z S`:
compatible with both `Ordered` and `extra_patV`, but not the iota rule. -/

/-! ## Environments, as the `addConst`/`addDefEq` chains `Ordered` needs -/

def env1 : VEnv := ((∅ : VEnv).addConst ``Nat natCI).getD ∅
def env2 : VEnv := (env1.addConst ``Nat.zero zeroCI).getD ∅
def env3 : VEnv := (env2.addConst ``Nat.succ succCI).getD ∅
/-- the four constants, no rules -/
def envC : VEnv := (env3.addConst ``Nat.rec recCI).getD ∅
/-- the four constants plus the two iota rules in encoding (A) -/
def envA : VEnv := (envC.addDefEq iotaSuccLam).addDefEq iotaZeroLam

example : envC.constants ``Nat.rec = some recCI := rfl
example : envC.constants ``Nat.zero = some zeroCI := rfl
example : envC.constants `Foo = none := rfl
example : envC.defeqs df ↔ False := Iff.rfl
example : envA.defeqs iotaZeroLam := .inl rfl

/-- typing of the three constants, in any env that has them and any context -/
theorem hasType_nat {env : VEnv} (h : env.constants ``Nat = some natCI) (Γ) :
    env.HasType U Γ natTy (.sort (.succ .zero)) :=
  .constDF (ci := natCI) h (by simp) (by simp) rfl .nil
theorem hasType_zero {env : VEnv} (h : env.constants ``Nat.zero = some zeroCI) (Γ) :
    env.HasType U Γ (.const ``Nat.zero []) natTy :=
  .constDF (ci := zeroCI) h (by simp) (by simp) rfl .nil
theorem hasType_succ {env : VEnv} (h : env.constants ``Nat.succ = some succCI) (Γ) :
    env.HasType U Γ (.const ``Nat.succ []) (.forallE natTy natTy) :=
  .constDF (ci := succCI) h (by simp) (by simp) rfl .nil

theorem natCI_wf : natCI.WF ∅ := ⟨_, .sortDF trivial trivial rfl⟩
theorem zeroCI_wf : zeroCI.WF env1 := ⟨_, hasType_nat rfl []⟩
theorem succCI_wf : succCI.WF env2 := ⟨_, .forallEDF (hasType_nat rfl []) (hasType_nat rfl _)⟩
/-- `Nat.rec`'s type is a type: the concrete derivation (each step's type pinned). -/
theorem recCI_wf : recCI.WF env3 :=
  have hN : ∀ Γ, env3.HasType 1 Γ natTy (.sort (.succ .zero)) := hasType_nat rfl
  have hZ : ∀ Γ, env3.HasType 1 Γ (.const ``Nat.zero []) natTy := hasType_zero rfl
  have hS : ∀ Γ, env3.HasType 1 Γ (.const ``Nat.succ []) (.forallE natTy natTy) := hasType_succ rfl
  have hU : ∀ Γ, env3.HasType 1 Γ (.sort (.param 0)) (.sort (.succ (.param 0))) :=
    fun _ => .sortDF (by decide) (by decide) rfl
  let mTy : VExpr := .forallE natTy (.sort (.param 0))
  -- motiveTy
  have hM : env3.HasType 1 [] motiveTy (.sort (.imax (.succ .zero) (.succ (.param 0)))) :=
    .forallEDF (hN _) (hU _)
  -- zTy  under [motive]
  have hb0 : env3.HasType 1 [motiveTy] (.bvar 0) mTy := .bvar .zero
  have hzTy : env3.HasType 1 [motiveTy] zTy (.sort (.param 0)) := .appDF hb0 (hZ _)
  -- sTy  under [z, motive]
  let Γn : List VExpr := [natTy, zTy, motiveTy]
  have hb2 : env3.HasType 1 Γn (.bvar 2) mTy := .bvar (.succ (.succ .zero))
  have hMn : env3.HasType 1 Γn (.app (.bvar 2) (.bvar 0)) (.sort (.param 0)) :=
    .appDF hb2 (.bvar .zero)
  let Γih : List VExpr := .app (.bvar 2) (.bvar 0) :: Γn
  have hb3 : env3.HasType 1 Γih (.bvar 3) mTy := .bvar (.succ (.succ (.succ .zero)))
  have hb1 : env3.HasType 1 Γih (.bvar 1) natTy := .bvar (.succ .zero)
  have hMsn : env3.HasType 1 Γih (.app (.bvar 3) (.app (.const ``Nat.succ []) (.bvar 1)))
      (.sort (.param 0)) := .appDF hb3 (.appDF (hS _) hb1)
  have hsTy : env3.HasType 1 [zTy, motiveTy] sTy
      (.sort (.imax (.succ .zero) (.imax (.param 0) (.param 0)))) :=
    .forallEDF (hN _) (.forallEDF hMn hMsn)
  -- (t : Nat) → motive t  under [s, z, motive]
  let Γt : List VExpr := [natTy, sTy, zTy, motiveTy]
  have hb3' : env3.HasType 1 Γt (.bvar 3) mTy := .bvar (.succ (.succ (.succ .zero)))
  have hMt : env3.HasType 1 Γt (.app (.bvar 3) (.bvar 0)) (.sort (.param 0)) :=
    .appDF hb3' (.bvar .zero)
  have hlast : env3.HasType 1 [sTy, zTy, motiveTy] (.forallE natTy (.app (.bvar 3) (.bvar 0)))
      (.sort (.imax (.succ .zero) (.param 0))) := .forallEDF (hN _) hMt
  ⟨_, .forallEDF hM (.forallEDF hzTy (.forallEDF hsTy hlast))⟩

theorem envC_ordered : envC.Ordered :=
  .const (n := ``Nat.rec) (.const (n := ``Nat.succ) (.const (n := ``Nat.zero)
    (.const (n := ``Nat) .empty natCI_wf rfl) zeroCI_wf rfl) succCI_wf rfl) recCI_wf rfl

theorem iotaSuccLam_wf : iotaSuccLam.WF envC :=
  sorry -- SORRY (routine but long): typing of the lambda-wrapped rule, both sides
theorem iotaZeroLam_wf : iotaZeroLam.WF (envC.addDefEq iotaSuccLam) :=
  sorry -- SORRY (routine but long)

theorem envA_ordered : envA.Ordered := .defeq (.defeq envC_ordered iotaSuccLam_wf) iotaZeroLam_wf

/-- `extra_patV` (verbatim field statement, `univs := 0`) is **false** for `envA`, whatever
`Pat` is: the rule's lhs is a `lam`. -/
theorem extra_patV_false_envA (Pat : (p : Pattern) → p.RHS × p.Check → Prop) :
    ¬ ∀ {df : VDefEq} {ls : List VLevel} {Γ : List VExpr},
      envA.defeqs df → (∀ l ∈ ls, l.WF 0) → ls.length = df.uvars →
      ∃ p r m1 m2, Pat p r ∧ p.Matches (df.lhs.instL ls) m1 m2 ∧
        r.2.OK (envA.IsDefEqU 0 Γ) m1 m2 ∧ df.rhs.instL ls = r.1.apply m1 m2 := by
  intro H
  obtain ⟨p, r, m1, m2, _, hm, _⟩ :=
    H (df := iotaZeroLam) (ls := [.zero]) (Γ := []) (.inl rfl) (by simp [VLevel.WF]) rfl
  exact iotaZeroLam_unmatchable _ _ _ _ hm

/-! ## `Params` for `envC` (constants only; `Pat` still has the two schematic iota patterns —
no field of `Params` requires `Pat` instances to be env rules) -/

/-! `pat_uniq` for the two patterns is a finite check: enumerate the subpatterns of each
pattern (6 + 7), compute `inter` by `decide`. -/
section PatUniq
deriving instance DecidableEq for Pattern

def _root_.Lean4Lean.Pattern.subs : Pattern → List Pattern
  | .const c => [.const c]
  | .app f a => .app f a :: (f.subs ++ a.subs)
  | .var f => .var f :: f.subs

theorem _root_.Lean4Lean.Subpattern.mem_subs {p q : Pattern} : Subpattern p q → p ∈ q.subs
  | .refl => by cases p <;> simp [Pattern.subs]
  | .appL h => by simp [Pattern.subs, h.mem_subs]
  | .appR h => by simp [Pattern.subs, h.mem_subs]
  | .varL h => by simp [Pattern.subs, h.mem_subs]

theorem _root_.Lean4Lean.Pattern.inter_ne_some {p q : Pattern} (h : (p.inter q).isNone = true) : p.inter q ≠ some r := by
  intro e; rw [e] at h; cases h

theorem pat_uniq_nat : Pat p₁ r → Pat p₂ r' → Subpattern p₃ p₁ → p₂.inter p₃ = some p₄ →
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r' := by
  intro h1 h2 h3 h4
  have h3 := h3.mem_subs
  cases h1 <;> cases h2 <;>
    simp only [zeroPat, succPat, SimplePattern.toPattern, Pattern.varN, Pattern.subs,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at h3 <;>
    rcases h3 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact ⟨rfl, rfl, HEq.rfl⟩
    | exact absurd h4 (Pattern.inter_ne_some (by decide))
end PatUniq

/-- `ctor_sort` for `ℕ`: every derivable sort of `Nat` (resp. `Nat → Nat`) is non-zero. -/
theorem ctor_sort_nat {c : Name} {cl : Classification} {ci : VConstant} {U : Nat}
    {vs : List VLevel} {u : VLevel} :
    (cl matches .ctor .. | .etaCtor ..) → classify c = some cl → envC.constants c = some ci →
    (∀ l ∈ vs, l.WF U) → vs.length = ci.uvars →
    envC.HasType U [] (ci.type.instL vs) (.sort u) → ∀ ns, u.eval ns ≠ 0 :=
  sorry -- SORRY (blocked): needs `IsDefEq.uniq` + `IsDefEqU.sort_inv` (Injectivity.lean, itself
        -- `sorry`) to get `u ≈ succ zero` from `HasType [] Nat (sort u)`; then `eval ≠ 0` is `rfl`.

/-! ## The rank fields (PLAN D4/D3; proofs from E4, `docs/const-case/plan/E4/NatParamsA.lean`)

E4 proves these over `envA`; here they are over `envC`, which has the same constants and no
rules. `pat_defeq` is the exception: it is false over `envC` (marked sorry below). -/

/-! ### `Nat.rec`'s binder typings, as named layers (E4's) -/

/-- `[motive] ⊢ motive : Nat → Sort u` etc.: the contexts of the rules' telescopes. -/
abbrev Γm : List VExpr := [motiveTy]
abbrev Γz : List VExpr := [zTy, motiveTy]
abbrev Γs : List VExpr := [sTy, zTy, motiveTy]
abbrev Γn : List VExpr := [natTy, sTy, zTy, motiveTy]

/-- A variable's typing at a stated type (the lookup's computed type, by `rfl`). -/
theorem hasBVar {env : VEnv} {U : Nat} {Γ : List VExpr} {i : Nat} {A B : VExpr}
    (h : Lookup Γ i A) (e : A = B) : env.HasType U Γ (.bvar i) B := e ▸ .bvar h

theorem motiveTy_wf : env3.HasType 1 [] motiveTy (.sort (.imax (.succ .zero) (.succ (.param 0)))) :=
  .forallEDF (hasType_nat rfl _) (.sortDF (by decide) (by decide) rfl)
theorem zTy_wf : env3.HasType 1 Γm zTy (.sort (.param 0)) :=
  have hb0 : env3.HasType 1 Γm (.bvar 0) motiveTy := hasBVar .zero rfl
  .appDF hb0 (hasType_zero rfl _)
theorem sTy_wf : env3.HasType 1 Γz sTy
    (.sort (.imax (.succ .zero) (.imax (.param 0) (.param 0)))) :=
  have hb2 : env3.HasType 1 [natTy, zTy, motiveTy] (.bvar 2) motiveTy :=
    hasBVar (.succ (.succ .zero)) rfl
  have hb0 : env3.HasType 1 [natTy, zTy, motiveTy] (.bvar 0) natTy := hasBVar .zero rfl
  have hMn : env3.HasType 1 [natTy, zTy, motiveTy] (.app (.bvar 2) (.bvar 0)) (.sort (.param 0)) :=
    .appDF hb2 hb0
  have hb3 : env3.HasType 1 [.app (.bvar 2) (.bvar 0), natTy, zTy, motiveTy] (.bvar 3) motiveTy :=
    hasBVar (.succ (.succ (.succ .zero))) rfl
  have hb1 : env3.HasType 1 [.app (.bvar 2) (.bvar 0), natTy, zTy, motiveTy] (.bvar 1) natTy :=
    hasBVar (.succ .zero) rfl
  have hsucc : env3.HasType 1 [.app (.bvar 2) (.bvar 0), natTy, zTy, motiveTy]
      (.const ``Nat.succ []) (.forallE natTy natTy) := hasType_succ rfl _
  have hMsn : env3.HasType 1 [.app (.bvar 2) (.bvar 0), natTy, zTy, motiveTy]
      (.app (.bvar 3) (.app (.const ``Nat.succ []) (.bvar 1))) (.sort (.param 0)) :=
    .appDF hb3 (.appDF hsucc hb1)
  .forallEDF (hasType_nat rfl _) (.forallEDF hMn hMsn)
theorem natTy_wf (Γ) : env3.HasType 1 Γ natTy (.sort (.succ .zero)) := hasType_nat rfl Γ

theorem env1_ordered : env1.Ordered := .const (n := ``Nat) .empty natCI_wf rfl
theorem env3_ordered : env3.Ordered :=
  .const (n := ``Nat.succ) (.const (n := ``Nat.zero)
    (.const (n := ``Nat) .empty natCI_wf rfl) zeroCI_wf rfl) succCI_wf rfl

/-- The telescopes of the two rules are well formed (`env3`, `U = 1`). -/
theorem ctx_s_wf : OnCtx Γs (env3.IsType 1) :=
  ⟨⟨⟨trivial, _, motiveTy_wf⟩, _, zTy_wf⟩, _, sTy_wf⟩
theorem ctx_n_wf : OnCtx Γn (env3.IsType 1) := ⟨ctx_s_wf, _, natTy_wf _⟩

/-! ### The rules' open bodies

`Ls ≡ Rs : Ts` in `Γn` (succ rule) and `Lz ≡ Rz : Tz` in `Γs` (zero rule) are the bodies of
`iotaSuccLam` (4 binders stripped) and `iotaZeroLam` (3). -/

def Ls : VExpr := recApp (.bvar 3) (.bvar 2) (.bvar 1) (.app (.const ``Nat.succ []) (.bvar 0))
def Rs : VExpr := .app (.app (.bvar 1) (.bvar 0)) (recApp (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
def Ts : VExpr := .app (.bvar 3) (.app (.const ``Nat.succ []) (.bvar 0))
def Lz : VExpr := recApp (.bvar 2) (.bvar 1) (.bvar 0) (.const ``Nat.zero [])
def Rz : VExpr := .bvar 1
def Tz : VExpr := .app (.bvar 2) (.const ``Nat.zero [])

/-! ### Ranks and the prefixes `envC.below rank k`

E4's ranks: `Nat 0, zero 1, succ 1, rec 2` (every other name 2; it has no constant).
`envC.below rank k` is extensionally `∅`, `env1`, `env3`, `envC` for `k = 0, 1, 2, ≥ 3`. -/

def rank (c : Name) : Nat :=
  if c = ``Nat then 0 else if c = ``Nat.zero then 1 else if c = ``Nat.succ then 1 else 2

theorem envC_constants (c : Name) : envC.constants c =
    if ``Nat.rec = c then some recCI else if ``Nat.succ = c then some succCI else
    if ``Nat.zero = c then some zeroCI else if ``Nat = c then some natCI else none := rfl
theorem env3_constants (c : Name) : env3.constants c =
    if ``Nat.succ = c then some succCI else
    if ``Nat.zero = c then some zeroCI else if ``Nat = c then some natCI else none := rfl
theorem env1_constants (c : Name) : env1.constants c = if ``Nat = c then some natCI else none := rfl

theorem rank_le (c : Name) : rank c ≤ 2 := by
  unfold rank; repeat' split
  all_goals decide

theorem below_ge3 {k : Nat} (hk : 3 ≤ k) : envC.below rank k = envC := by
  apply VEnv.ext
  · funext c
    simp only [VEnv.below]
    rw [if_pos (Nat.lt_of_le_of_lt (rank_le c) hk)]
  · funext df
    apply propext
    exact ⟨And.left, fun h => (h : False).elim⟩

theorem below_2 : envC.below rank 2 = env3 := by
  apply VEnv.ext
  · funext c
    by_cases h1 : c = ``Nat.rec; · subst h1; rfl
    by_cases h2 : c = ``Nat.succ; · subst h2; rfl
    by_cases h3 : c = ``Nat.zero; · subst h3; rfl
    by_cases h4 : c = ``Nat; · subst h4; rfl
    simp [VEnv.below, envC_constants, env3_constants, Ne.symm h1, Ne.symm h2, Ne.symm h3,
      Ne.symm h4]
  · funext df
    apply propext
    exact ⟨fun h => (h.1 : False).elim, fun h => (h : False).elim⟩

theorem below_1 : envC.below rank 1 = env1 := by
  apply VEnv.ext
  · funext c
    by_cases h1 : c = ``Nat.rec; · subst h1; rfl
    by_cases h2 : c = ``Nat.succ; · subst h2; rfl
    by_cases h3 : c = ``Nat.zero; · subst h3; rfl
    by_cases h4 : c = ``Nat; · subst h4; rfl
    simp [VEnv.below, envC_constants, env1_constants, Ne.symm h1, Ne.symm h2, Ne.symm h3,
      Ne.symm h4]
  · funext df
    apply propext
    exact ⟨fun h => (h.1 : False).elim, fun h => (h : False).elim⟩

theorem below_0 : envC.below rank 0 = ∅ := by
  apply VEnv.ext
  · funext c
    simp only [VEnv.below, Nat.not_lt_zero, if_false]
    rfl
  · funext df
    apply propext
    exact ⟨fun h => (h.1 : False).elim, fun h => h.elim⟩

/-- `rank_ordered`: every prefix is one of the `Ordered` chains `∅`/`env1`/`env3`/`envC`. -/
theorem rank_ordered : ∀ k, (envC.below rank k).Ordered
  | 0 => by rw [below_0]; exact .empty
  | 1 => by rw [below_1]; exact env1_ordered
  | 2 => by rw [below_2]; exact env3_ordered
  | k+3 => by rw [below_ge3 (by omega)]; exact envC_ordered

theorem envC_constants_cases {c : Name} {ci : VConstant} (h : envC.constants c = some ci) :
    (c = ``Nat.rec ∧ ci = recCI) ∨ (c = ``Nat.succ ∧ ci = succCI) ∨
    (c = ``Nat.zero ∧ ci = zeroCI) ∨ (c = ``Nat ∧ ci = natCI) := by
  rw [envC_constants] at h; repeat' split at h
  all_goals simp_all

/-- `Nat.succ`'s type only mentions `Nat`, so it is a type already in `env1`. -/
theorem succCI_wf1 : succCI.WF env1 := ⟨_, .forallEDF (hasType_nat rfl []) (hasType_nat rfl _)⟩

/-- `type_below`: each constant's type is a type in the prefix of its own rank. -/
theorem type_below {c : Name} {ci : VConstant} (h : envC.constants c = some ci) :
    (envC.below rank (rank c)).IsType ci.uvars [] ci.type := by
  rcases envC_constants_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [show rank ``Nat.rec = 2 from rfl, below_2]; exact recCI_wf
  · rw [show rank ``Nat.succ = 1 from rfl, below_1]; exact succCI_wf1
  · rw [show rank ``Nat.zero = 1 from rfl, below_1]; exact zeroCI_wf
  · rw [show rank ``Nat = 0 from rfl, below_0]; exact natCI_wf

/-! ### `Pattern.gen` on `envC`, both rules, by `rfl`

The generated `ctx`/`lhs`/`rhs`/`type` are the open bodies of the λ-wrapped rules (`Γn ⊢ Ls ≡ Rs :
Ts`, 4 binders stripped; `Γs ⊢ Lz ≡ Rz : Tz`, 3 binders), and the succ rule's recursive call
`Nat.rec.{u}` (rank 2 = rank of the head) is its one self occurrence. -/

/-- The succ rule's abstracted RHS `s n (self motive z s n)` in `[self, n, s, z, motive]`. -/
def RsAbs : VExpr := .app (.app (.bvar 2) (.bvar 1))
  (.app (.app (.app (.app (.bvar 0) (.bvar 4)) (.bvar 3)) (.bvar 2)) (.bvar 1))

def genSucc : PatGen :=
  { ctx := Γn, self := [recCI.type], lhs := Ls, rhs := Rs, rhsAbs := RsAbs, type := Ts }
def genZero : PatGen :=
  { ctx := Γs, self := [], lhs := Lz, rhs := Rz, rhsAbs := .bvar 1, type := Tz }

theorem gen_succ : Pattern.gen envC rank classify succPat succRHS = some genSucc := rfl
theorem gen_zero : Pattern.gen envC rank classify zeroPat zeroRHS = some genZero := rfl

/-- Negative control: a wrong self list is rejected (so the `rfl` above is not vacuous). -/
example : Pattern.gen envC rank classify succPat succRHS ≠ some { genSucc with self := [] } := by
  rw [gen_succ]; intro h; cases h

theorem head_succ : succPat.head = ``Nat.rec := rfl
theorem head_zero : zeroPat.head = ``Nat.rec := rfl

theorem pat_rank {p : Pattern} {r : p.RHS × p.Check} {c' : Name} {us : List VLevel}
    (hP : Pat p r) (h : .const c' us ∈ r.1.fixedLeaves) : rank c' ≤ rank p.head := by
  cases hP with
  | zero => simp [zeroRHS, Pattern.RHS.fixedLeaves] at h
  | succ =>
    simp only [succRHS, Pattern.RHS.fixedLeaves, List.nil_append, List.append_nil,
      List.mem_singleton, VExpr.const.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Nat.le_refl _

theorem pat_gen {p : Pattern} {r : p.RHS × p.Check} (hP : Pat p r) :
    (Pattern.gen envC rank classify p r.1).isSome := by
  cases hP with
  | zero => rw [gen_zero]; rfl
  | succ => rw [gen_succ]; rfl

theorem pat_check {p : Pattern} {r : p.RHS × p.Check} (hP : Pat p r) : r.2 = .true := by
  cases hP <;> rfl

/-! ### `pat_typed`: the generated contexts and `rhsAbs` typed in `env3 = envC.below rank 2` -/

abbrev Γr : List VExpr := recCI.type :: Γn

/-- `[self : rec.type, n, s, z, motive]` is a well-formed context of `env3`. -/
theorem ctx_r_wf : OnCtx Γr (env3.IsType 1) :=
  ⟨ctx_n_wf, let ⟨_, h⟩ := recCI_wf; ⟨_, h.weak0 env3_ordered⟩⟩

/-- `[self, n, s, z, motive] ⊢ s n (self motive z s n) : motive (succ n)` in `env3`. -/
theorem RsAbs_wf : env3.HasType 1 Γr RsAbs (Ts.liftN 1) :=
  have b0 : env3.HasType 1 Γr (.bvar 0) recCI.type := hasBVar .zero rfl
  have b1 : env3.HasType 1 Γr (.bvar 1) natTy := hasBVar (.succ .zero) rfl
  have b2 : env3.HasType 1 Γr (.bvar 2) (.forallE natTy (.forallE (.app (.bvar 5) (.bvar 0))
      (.app (.bvar 6) (.app (.const ``Nat.succ []) (.bvar 1))))) :=
    hasBVar (.succ (.succ .zero)) rfl
  have b3 : env3.HasType 1 Γr (.bvar 3) (.app (.bvar 4) (.const ``Nat.zero [])) :=
    hasBVar (.succ (.succ (.succ .zero))) rfl
  have b4 : env3.HasType 1 Γr (.bvar 4) motiveTy :=
    hasBVar (.succ (.succ (.succ (.succ .zero)))) rfl
  (b2.app b1).app ((((b0.app b4).app b3).app b2).app b1)

/-- The zero rule's `rhsAbs = z` in `[s, z, motive]`, in `env3`. -/
theorem RzAbs_wf : env3.HasType 1 Γs (.bvar 1) (Tz.liftN 0) := hasBVar (.succ .zero) rfl

theorem envC_const_rec : envC.constants ``Nat.rec = some recCI := rfl
theorem envC_const_succ : envC.constants ``Nat.succ = some succCI := rfl
theorem envC_const_zero : envC.constants ``Nat.zero = some zeroCI := rfl
theorem envC_const_nat : envC.constants ``Nat = some natCI := rfl

theorem pat_typed {p : Pattern} {r : p.RHS × p.Check} {g : PatGen} {ci : VConstant}
    (hP : Pat p r) (hg : Pattern.gen envC rank classify p r.1 = some g)
    (hci : envC.constants p.head = some ci) :
    OnCtx (g.self ++ g.ctx) (fun Γ A => (envC.below rank (rank p.head)).IsType ci.uvars Γ A) ∧
    (envC.below rank (rank p.head)).HasType ci.uvars (g.self ++ g.ctx) g.rhsAbs
      (g.type.liftN g.self.length) := by
  cases hP with
  | zero =>
    rw [gen_zero] at hg; cases hg
    rw [head_zero, envC_const_rec] at hci; cases hci
    rw [head_zero, show rank ``Nat.rec = 2 from rfl, below_2]
    exact ⟨ctx_s_wf, RzAbs_wf⟩
  | succ =>
    rw [gen_succ] at hg; cases hg
    rw [head_succ, envC_const_rec] at hci; cases hci
    rw [head_succ, show rank ``Nat.rec = 2 from rfl, below_2]
    exact ⟨ctx_r_wf, RsAbs_wf⟩

/-! ### `pat_defeq`: false here

It asks for the rules' open equations (`Γn ⊢ Ls ≡ Rs : Ts`, `Γs ⊢ Lz ≡ Rz : Tz`) in `envC`,
which has no rules. E4 proves them over `envA` (`succ_open`, `zero_open`). -/

theorem pat_defeq_nat {p : Pattern} {r : p.RHS × p.Check} {g : PatGen} {ci : VConstant} :
    Pat p r → Pattern.gen envC rank classify p r.1 = some g →
    envC.constants p.head = some ci →
    envC.IsDefEq ci.uvars g.ctx g.lhs g.rhs g.type :=
  sorry -- SORRY(R5): false over envC, which has no rules; R12 moves the instance to envA (docs/const-case/plan/E4/)

/-! ### The classification fields -/

theorem indTy_closed {I : Name} {k : Nat} {ci : VConstant} (hcl : classify I = some (.indTy k))
    (hci : envC.constants I = some ci) : k = 0 ∧ ∃ u, ci.type = .sort u := by
  rcases classify_cases hcl with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> cases h
  rw [envC_const_nat] at hci; cases hci
  exact ⟨rfl, _, rfl⟩

theorem ctor_fields_closed {c : Name} {cl : Classification} {ci : VConstant}
    (hctor : cl matches .ctor .. | .etaCtor ..) (hcl : classify c = some cl)
    (hci : envC.constants c = some ci) :
    ∃ (I : Name) (Ts : List VExpr), ci.type = Ts.foldr .forallE (.const I (VLevel.params ci.uvars)) ∧
      ∀ T ∈ Ts, ∃ (I' : Name) (us : List VLevel), T = .const I' us ∧
        classify I' = some (.indTy 0) := by
  rcases classify_cases hcl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact nomatch hctor
  · rw [envC_const_zero] at hci; cases hci
    exact ⟨``Nat, [], rfl, nofun⟩
  · rw [envC_const_succ] at hci; cases hci
    refine ⟨``Nat, [natTy], rfl, fun T hT => ?_⟩
    rw [List.mem_singleton] at hT; subst hT
    exact ⟨``Nat, [], rfl, rfl⟩
  · exact nomatch hctor

@[instance_reducible] def natParams : Params := {
  env := envC
  henv := envC_ordered
  univs := 0
  Pat := Pat
  classify := classify
  pat_simple := fun h => by cases h <;> exact ⟨_, rfl⟩
  pat_wf := fun h => by cases h <;> exact ⟨rfl, rfl⟩
  pat_uniq := pat_uniq_nat
  extra_patV := fun h => h.elim        -- vacuous: `envC.defeqs _` is `False`
  ctor_syn := fun hctor hcl hci => by
    rcases classify_cases hcl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact nomatch hctor
    · cases Option.some.inj hci; exact ⟨``Nat, [], [], rfl, rfl, rfl⟩
    · cases Option.some.inj hci; exact ⟨``Nat, [natTy], [], rfl, rfl, rfl⟩
    · exact nomatch hctor
  ctor_sort := ctor_sort_nat           -- SORRY (blocked)
  rank := rank
  rank_ordered := rank_ordered
  type_below := type_below
  pat_rank := pat_rank
  pat_gen := pat_gen
  pat_typed := pat_typed
  pat_defeq := pat_defeq_nat           -- SORRY(R5) (false over `envC`)
  pat_check := pat_check
  indTy_closed := indTy_closed
  ctor_fields_closed := ctor_fields_closed
}

#print axioms natParams
-- which pieces carry `sorryAx`:
#print axioms envC_ordered
#print axioms pat_uniq_nat
#print axioms extra_patV_false_envA
#print axioms iotaZeroOpen_not_wf
#print axioms ctor_sort_nat
#print axioms envA_ordered
#print axioms rank_ordered
#print axioms type_below
#print axioms pat_typed
#print axioms pat_defeq_nat

/-! ## Summary

`sorry`s in this file (all marked `-- SORRY`):
* `iotaZeroLam_wf`, `iotaSuccLam_wf` — typing of the lambda-wrapped rules (routine, long);
  only `envA_ordered` depends on them, and `envA` is the env on which `extra_patV` is refuted.
* `ctor_sort_nat` — blocked on the repo's own sorried `IsDefEqU.sort_inv` (Injectivity.lean).
* `pat_defeq_nat` — false over `envC`, which has no rules; R12 moves the instance to `envA`,
  where E4 proves it (`docs/const-case/plan/E4/NatParamsA.lean`, `succ_open`/`zero_open`).
`ctor_sort_nat` and `pat_defeq_nat` are the two `sorryAx`s reaching `natParams`.

Field status for `ℕ` (`natParams`, env = four constants, `Pat` = the two iota patterns):
* `env`, `univs`, `Pat`, `classify`           — defined.
* `henv`                                       — proven (`envC_ordered`, incl. `recCI_wf`).
* `pat_simple`, `pat_wf`                       — proven, `rfl`-level.
* `pat_uniq`                                   — proven, finite `decide` over 13 subpatterns.
* `ctor_syn`                                   — proven (`Ts = []` / `[natTy]`, `args = []`).
* `extra_patV`                                 — vacuous here; **false** for any `Ordered` env
  that carries a schematic iota rule: lambda-wrapped (Lean4Lean's `vdefeq` convention) has an
  unmatchable `lam` lhs (`extra_patV_false_envA`); open-`bvar` is not `VDefEq.WF`
  (`iotaZeroOpen_not_wf`).  `Params` has no `Pat ⊆ env.defeqs` direction, so `Pat` may still
  hold the schematic rules.
* `ctor_sort`                                  — true (`u ≈ 1`), proof needs sort inversion.
* `rank`, `rank_ordered`, `type_below`         — ranks `Nat 0, zero 1, succ 1, rec 2`; the
  prefixes `envC.below rank k` are `∅`/`env1`/`env3`/`envC` (E4's proofs, over `envC`).
* `pat_rank`, `pat_gen`, `pat_check`           — proven; `Pattern.gen` evaluated by `rfl`.
* `pat_typed`                                  — proven, in `env3 = envC.below rank 2`.
* `pat_defeq`                                  — **false** here (no rules); proven over `envA` in E4.
* `indTy_closed`, `ctor_fields_closed`         — proven. -/

end NatEnv
end Lean4Lean
