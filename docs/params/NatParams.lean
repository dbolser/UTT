import Lean4Lean.Experimental.SExpr

/-! # A `Params` instance for an environment with `ℕ` and its iota rules

`natParams : Params` over `envA`: the constants `Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec` plus the
two iota rules in Lean4Lean's `vdefeq` convention (closed and λ-wrapped), `Pat` the two iota
patterns as `SimplePattern.iota`, ranks `Nat 0, zero 1, succ 1, rec 2`. Every field is proved
except `ctor_sort`: `ctor_sort_nat` is the one `sorry`, marked `-- SORRY`, blocked on the repo's
own sorried `IsDefEqU.sort_inv`. The proofs are experiment E4's
(`docs/const-case/plan/E4/NatParamsA.lean`, PLAN R12), against the repo's `Pattern.gen` (R5) and
the λ-`extra_patV` (D5, R6). (`Theory.Meta`/`Quot` need Batteries, not built in the snapshot,
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
closed and **lambda-wrapped**.  Typable in `[]`, so compatible with `Ordered`.  `Pattern.Matches`
has no `lam` case, which refuted the `Δ = []` `extra_patV` (before R6, `extra_patV_false_envA`
below); the λ-`extra_patV` (D5, R6) strips the binders first, and `envA` satisfies it. This is
the encoding `natParams` uses. -/
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
compatible with both `Ordered` and the `Δ = []` `extra_patV`, but not the iota rule. -/

/-! ## Environments, as the `addConst`/`addDefEq` chains `Ordered` needs -/

def env1 : VEnv := ((∅ : VEnv).addConst ``Nat natCI).getD ∅
def env2 : VEnv := (env1.addConst ``Nat.zero zeroCI).getD ∅
def env3 : VEnv := (env2.addConst ``Nat.succ succCI).getD ∅
/-- the four constants, no rules -/
def envC : VEnv := (env3.addConst ``Nat.rec recCI).getD ∅
/-- the four constants plus the two iota rules in encoding (A): `natParams`' environment -/
def envA : VEnv := (envC.addDefEq iotaSuccLam).addDefEq iotaZeroLam

example : envA.constants ``Nat.rec = some recCI := rfl
example : envA.constants ``Nat.zero = some zeroCI := rfl
example : envA.constants `Foo = none := rfl
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

/-! ### `Nat.rec`'s binder typings, as named layers -/

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
theorem recBody_wf : env3.HasType 1 Γs (.forallE natTy (.app (.bvar 3) (.bvar 0)))
    (.sort (.imax (.succ .zero) (.param 0))) :=
  have hb3 : env3.HasType 1 (natTy :: Γs) (.bvar 3) motiveTy := hasBVar (.succ (.succ (.succ .zero))) rfl
  have hb0 : env3.HasType 1 (natTy :: Γs) (.bvar 0) natTy := hasBVar .zero rfl
  .forallEDF (natTy_wf _) (.appDF hb3 hb0)

/-- `Nat.rec`'s type is a type: the concrete derivation, layer by layer. -/
theorem recCI_wf : recCI.WF env3 :=
  ⟨_, .forallEDF motiveTy_wf (.forallEDF zTy_wf (.forallEDF sTy_wf recBody_wf))⟩

theorem env1_ordered : env1.Ordered := .const (n := ``Nat) .empty natCI_wf rfl
theorem env3_ordered : env3.Ordered :=
  .const (n := ``Nat.succ) (.const (n := ``Nat.zero)
    (.const (n := ``Nat) .empty natCI_wf rfl) zeroCI_wf rfl) succCI_wf rfl

theorem envC_ordered : envC.Ordered := .const (n := ``Nat.rec) env3_ordered recCI_wf rfl

theorem env3_le_envC : env3 ≤ envC := VEnv.addConst_le (n := ``Nat.rec) (ci := recCI) rfl
theorem envC_le_envA : envC ≤ envA := VEnv.addDefEq_le.trans VEnv.addDefEq_le

/-- The telescopes of the two rules are well formed (`env3`, `U = 1`). -/
theorem ctx_s_wf : OnCtx Γs (env3.IsType 1) :=
  ⟨⟨⟨trivial, _, motiveTy_wf⟩, _, zTy_wf⟩, _, sTy_wf⟩
theorem ctx_n_wf : OnCtx Γn (env3.IsType 1) := ⟨ctx_s_wf, _, natTy_wf _⟩

/-! ## The rules' open bodies and their typings

`Ls ≡ Rs : Ts` in `Γn` (succ rule) and `Lz ≡ Rz : Tz` in `Γs` (zero rule) are the bodies of
`iotaSuccLam` (4 binders stripped) and `iotaZeroLam` (3). -/

def Ls : VExpr := recApp (.bvar 3) (.bvar 2) (.bvar 1) (.app (.const ``Nat.succ []) (.bvar 0))
def Rs : VExpr := .app (.app (.bvar 1) (.bvar 0)) (recApp (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
def Ts : VExpr := .app (.bvar 3) (.app (.const ``Nat.succ []) (.bvar 0))
def Lz : VExpr := recApp (.bvar 2) (.bvar 1) (.bvar 0) (.const ``Nat.zero [])
def Rz : VExpr := .bvar 1
def Tz : VExpr := .app (.bvar 2) (.const ``Nat.zero [])

theorem iotaSuccLam_eq : iotaSuccLam = ⟨1,
    .lam motiveTy (.lam zTy (.lam sTy (.lam natTy Ls))),
    .lam motiveTy (.lam zTy (.lam sTy (.lam natTy Rs))),
    .forallE motiveTy (.forallE zTy (.forallE sTy (.forallE natTy Ts)))⟩ := rfl
theorem iotaZeroLam_eq : iotaZeroLam = ⟨1,
    .lam motiveTy (.lam zTy (.lam sTy Lz)), .lam motiveTy (.lam zTy (.lam sTy Rz)),
    .forallE motiveTy (.forallE zTy (.forallE sTy Tz))⟩ := rfl

/-- `Nat.rec.{u}` at its own level, in any context of `envC`. -/
theorem hasType_rec (Γ : List VExpr) :
    envC.HasType 1 Γ (.const ``Nat.rec [.param 0]) recCI.type :=
  .const (ci := recCI) rfl (by decide) rfl

theorem bvar0_n : envC.HasType 1 Γn (.bvar 0) natTy := hasBVar .zero rfl
theorem bvar1_n : envC.HasType 1 Γn (.bvar 1) (.forallE natTy (.forallE (.app (.bvar 4) (.bvar 0))
    (.app (.bvar 5) (.app (.const ``Nat.succ []) (.bvar 1))))) := hasBVar (.succ .zero) rfl
theorem bvar2_n : envC.HasType 1 Γn (.bvar 2) (.app (.bvar 3) (.const ``Nat.zero [])) :=
  hasBVar (.succ (.succ .zero)) rfl
theorem bvar3_n : envC.HasType 1 Γn (.bvar 3) motiveTy := hasBVar (.succ (.succ (.succ .zero))) rfl

/-- `Nat.rec m z s : (t : Nat) → motive t` for the context variables `m z s` of `Γn`. -/
theorem hasType_recPre_n : envC.HasType 1 Γn
    (.app (.app (.app (.const ``Nat.rec [.param 0]) (.bvar 3)) (.bvar 2)) (.bvar 1))
    (.forallE natTy (.app (.bvar 4) (.bvar 0))) :=
  (((hasType_rec Γn).app bvar3_n).app bvar2_n).app bvar1_n

theorem Ls_wf : envC.HasType 1 Γn Ls Ts :=
  hasType_recPre_n.app ((hasType_succ (env := envC) rfl Γn).app bvar0_n)

theorem recn_wf : envC.HasType 1 Γn (recApp (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
    (.app (.bvar 3) (.bvar 0)) := hasType_recPre_n.app bvar0_n

theorem Rs_wf : envC.HasType 1 Γn Rs Ts := (bvar1_n.app bvar0_n).app recn_wf

theorem Lz_wf : envC.HasType 1 Γs Lz Tz :=
  have hb2 : envC.HasType 1 Γs (.bvar 2) motiveTy := hasBVar (.succ (.succ .zero)) rfl
  have hb1 : envC.HasType 1 Γs (.bvar 1) (.app (.bvar 2) (.const ``Nat.zero [])) :=
    hasBVar (.succ .zero) rfl
  have hb0 : envC.HasType 1 Γs (.bvar 0) (.forallE natTy (.forallE (.app (.bvar 3) (.bvar 0))
      (.app (.bvar 4) (.app (.const ``Nat.succ []) (.bvar 1))))) := hasBVar .zero rfl
  ((((hasType_rec Γs).app hb2).app hb1).app hb0).app (hasType_zero rfl Γs)

theorem Rz_wf : envC.HasType 1 Γs Rz Tz := hasBVar (.succ .zero) rfl

/-! ## The λ-closed rules are well typed, so `envA` is `Ordered` -/

theorem motiveTy_wfC : envC.HasType 1 [] motiveTy (.sort (.imax (.succ .zero) (.succ (.param 0)))) :=
  motiveTy_wf.mono env3_le_envC
theorem zTy_wfC : envC.HasType 1 Γm zTy (.sort (.param 0)) := zTy_wf.mono env3_le_envC
theorem sTy_wfC : envC.HasType 1 Γz sTy (.sort (.imax (.succ .zero) (.imax (.param 0) (.param 0)))) :=
  sTy_wf.mono env3_le_envC
theorem natTy_wfC (Γ) : envC.HasType 1 Γ natTy (.sort (.succ .zero)) := hasType_nat rfl Γ

/-- The layers of `iotaSuccLam.lhs`: each λ-suffix, typed in its context. -/
theorem Fs3 : envC.HasType 1 Γs (.lam natTy Ls) (.forallE natTy Ts) := .lam (natTy_wfC _) Ls_wf
theorem Fs2 : envC.HasType 1 Γz (.lam sTy (.lam natTy Ls)) (.forallE sTy (.forallE natTy Ts)) :=
  .lam sTy_wfC Fs3
theorem Fs1 : envC.HasType 1 Γm (.lam zTy (.lam sTy (.lam natTy Ls)))
    (.forallE zTy (.forallE sTy (.forallE natTy Ts))) := .lam zTy_wfC Fs2
theorem Fs0 : envC.HasType 1 [] iotaSuccLam.lhs iotaSuccLam.type := .lam motiveTy_wfC Fs1
/-- The layers of `iotaSuccLam.rhs`. -/
theorem Gs3 : envC.HasType 1 Γs (.lam natTy Rs) (.forallE natTy Ts) := .lam (natTy_wfC _) Rs_wf
theorem Gs2 : envC.HasType 1 Γz (.lam sTy (.lam natTy Rs)) (.forallE sTy (.forallE natTy Ts)) :=
  .lam sTy_wfC Gs3
theorem Gs1 : envC.HasType 1 Γm (.lam zTy (.lam sTy (.lam natTy Rs)))
    (.forallE zTy (.forallE sTy (.forallE natTy Ts))) := .lam zTy_wfC Gs2
theorem Gs0 : envC.HasType 1 [] iotaSuccLam.rhs iotaSuccLam.type := .lam motiveTy_wfC Gs1
/-- The layers of `iotaZeroLam.lhs`/`rhs`. -/
theorem Fz2 : envC.HasType 1 Γz (.lam sTy Lz) (.forallE sTy Tz) := .lam sTy_wfC Lz_wf
theorem Fz1 : envC.HasType 1 Γm (.lam zTy (.lam sTy Lz)) (.forallE zTy (.forallE sTy Tz)) :=
  .lam zTy_wfC Fz2
theorem Fz0 : envC.HasType 1 [] iotaZeroLam.lhs iotaZeroLam.type := .lam motiveTy_wfC Fz1
theorem Gz2 : envC.HasType 1 Γz (.lam sTy Rz) (.forallE sTy Tz) := .lam sTy_wfC Rz_wf
theorem Gz1 : envC.HasType 1 Γm (.lam zTy (.lam sTy Rz)) (.forallE zTy (.forallE sTy Tz)) :=
  .lam zTy_wfC Gz2
theorem Gz0 : envC.HasType 1 [] iotaZeroLam.rhs iotaZeroLam.type := .lam motiveTy_wfC Gz1

/-- Both sides of the succ rule, typed by the λ-closures above. -/
theorem iotaSuccLam_wf : iotaSuccLam.WF envC := ⟨Fs0, Gs0⟩
theorem iotaZeroLam_wf : iotaZeroLam.WF (envC.addDefEq iotaSuccLam) :=
  ⟨Fz0.mono VEnv.addDefEq_le, Gz0.mono VEnv.addDefEq_le⟩

theorem envA_ordered : envA.Ordered := .defeq (.defeq envC_ordered iotaSuccLam_wf) iotaZeroLam_wf

/-! ## Historical finding: the `Δ = []` `extra_patV` is false for `envA`

Before R6, `extra_patV` demanded a pattern match of every rule instance itself (no binders
stripped). `ExtraPatVOld Pat` is that field's body over `envA` (`univs := 0`), and it fails for
every choice of `Pat`: the rule's lhs is a `lam`. This is why R6 restated the field on
λ-telescopes (PLAN D5); the restated field holds for `envA` (`extra_patV` below). -/

/-- The `extra_patV` field before R6 (verbatim body, `env := envA`, `univs := 0`). -/
def ExtraPatVOld (Pat : (p : Pattern) → p.RHS × p.Check → Prop) : Prop :=
  ∀ {df : VDefEq} {ls : List VLevel} {Γ : List VExpr},
    envA.defeqs df → (∀ l ∈ ls, l.WF 0) → ls.length = df.uvars →
    ∃ p r m1 m2, Pat p r ∧ p.Matches (df.lhs.instL ls) m1 m2 ∧
      r.2.OK (envA.IsDefEqU 0 Γ) m1 m2 ∧ df.rhs.instL ls = r.1.apply m1 m2

theorem extra_patV_false_envA (Pat : (p : Pattern) → p.RHS × p.Check → Prop) :
    ¬ ExtraPatVOld Pat := by
  intro H
  obtain ⟨p, r, m1, m2, _, hm, _⟩ :=
    H (df := iotaZeroLam) (ls := [.zero]) (Γ := []) (.inl rfl) (by simp [VLevel.WF]) rfl
  exact iotaZeroLam_unmatchable _ _ _ _ hm

/-! ## Beta along the context variables: the open equations

`lam_step` peels one λ-layer off a closed rule applied to the context's variables, using only
weakening and `beta` (no inversion): from `Γ ⊢ X ≡ λA.body : ΠA.B` and `A::Γ ⊢ body : B`,
`A::Γ ⊢ X↑ (bvar 0) ≡ body : B`. -/
theorem lam_step {env : VEnv} {U : Nat} {Γ : List VExpr} {X A body B : VExpr} (henv : env.Ordered)
    (hX : env.IsDefEq U Γ X (.lam A body) (.forallE A B))
    (hb : env.HasType U (A :: Γ) body B) :
    env.IsDefEq U (A :: Γ) (.app X.lift (.bvar 0)) body B := by
  have h1 := hX.weakN henv (.one (A := A))
  have h2 : env.HasType U (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have h4 := hb.weakN henv (.succ (.one (A := A)))
  have h3 : env.IsDefEq U (A :: Γ) (.app X.lift (.bvar 0))
      (.app (.lam A.lift (body.liftN 1 (0+1))) (.bvar 0)) ((B.liftN 1 (0+1)).inst (.bvar 0)) :=
    .appDF h1 h2
  have h5 : env.IsDefEq U (A :: Γ) (.app (.lam A.lift (body.liftN 1 (0+1))) (.bvar 0))
      ((body.liftN 1 (0+1)).inst (.bvar 0)) ((B.liftN 1 (0+1)).inst (.bvar 0)) := .beta h4 h2
  have := h3.trans h5
  rwa [VExpr.inst_liftN_bvar, VExpr.inst_liftN_bvar] at this

/-- The same along a congruence: `Γ ⊢ X ≡ Y : ΠA.B` gives `A::Γ ⊢ X↑ (bvar 0) ≡ Y↑ (bvar 0) : B`. -/
theorem app_step {env : VEnv} {U : Nat} {Γ : List VExpr} {X Y A B : VExpr} (henv : env.Ordered)
    (hX : env.IsDefEq U Γ X Y (.forallE A B)) :
    env.IsDefEq U (A :: Γ) (.app X.lift (.bvar 0)) (.app Y.lift (.bvar 0)) B := by
  have h1 := hX.weakN henv (.one (A := A))
  have h2 : env.HasType U (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have h3 : env.IsDefEq U (A :: Γ) (.app X.lift (.bvar 0)) (.app Y.lift (.bvar 0))
      ((B.liftN 1 (0+1)).inst (.bvar 0)) := .appDF h1 h2
  rwa [VExpr.inst_liftN_bvar] at h3

/-- The succ rule's open equation `Γn ⊢ Ls ≡ Rs : Ts` in `envA` (D5's `pat_defeq` row: the
λ-wrapped rule (`extra`) applied to the context's variables (`app_step` ×4), with each side
beta-reduced along the same spine (`lam_step` ×4, on the λ-layers `Fs1`-`Ls_wf` / `Gs1`-`Rs_wf`)). -/
theorem succ_open : envA.IsDefEq 1 Γn Ls Rs Ts := by
  have hrule : envA.IsDefEq 1 [] iotaSuccLam.lhs iotaSuccLam.rhs iotaSuccLam.type :=
    .extra (env := envA) (uvars := 1) (Γ := []) (df := iotaSuccLam) (ls := [.param 0])
      (Or.inr (Or.inl rfl)) (by decide) rfl
  have a4 := app_step envA_ordered (app_step envA_ordered
    (app_step envA_ordered (app_step envA_ordered hrule)))
  have lF := lam_step envC_ordered (lam_step envC_ordered
    (lam_step envC_ordered (lam_step envC_ordered Fs0 Fs1) Fs2) Fs3) Ls_wf
  have lG := lam_step envC_ordered (lam_step envC_ordered
    (lam_step envC_ordered (lam_step envC_ordered Gs0 Gs1) Gs2) Gs3) Rs_wf
  exact (lF.mono envC_le_envA).symm.trans (a4.trans (lG.mono envC_le_envA))

/-- The zero rule's open equation `Γs ⊢ Lz ≡ Rz : Tz` in `envA` (3 layers). -/
theorem zero_open : envA.IsDefEq 1 Γs Lz Rz Tz := by
  have hrule : envA.IsDefEq 1 [] iotaZeroLam.lhs iotaZeroLam.rhs iotaZeroLam.type :=
    .extra (env := envA) (uvars := 1) (Γ := []) (df := iotaZeroLam) (ls := [.param 0])
      (Or.inl rfl) (by decide) rfl
  have a3 := app_step envA_ordered (app_step envA_ordered (app_step envA_ordered hrule))
  have lF := lam_step envC_ordered (lam_step envC_ordered (lam_step envC_ordered Fz0 Fz1) Fz2) Lz_wf
  have lG := lam_step envC_ordered (lam_step envC_ordered (lam_step envC_ordered Gz0 Gz1) Gz2) Rz_wf
  exact (lF.mono envC_le_envA).symm.trans (a3.trans (lG.mono envC_le_envA))

/-! ## Ranks and the prefixes `envA.below rank k`

Ranks `Nat 0, zero 1, succ 1, rec 2` (every other name 2; it has no constant).
`envA.below rank k` is extensionally `∅`, `env1`, `env3`, `envA` for `k = 0, 1, 2, ≥ 3`. -/

def rank (c : Name) : Nat :=
  if c = ``Nat then 0 else if c = ``Nat.zero then 1 else if c = ``Nat.succ then 1 else 2

theorem envA_constants (c : Name) : envA.constants c =
    if ``Nat.rec = c then some recCI else if ``Nat.succ = c then some succCI else
    if ``Nat.zero = c then some zeroCI else if ``Nat = c then some natCI else none := rfl
theorem env3_constants (c : Name) : env3.constants c =
    if ``Nat.succ = c then some succCI else
    if ``Nat.zero = c then some zeroCI else if ``Nat = c then some natCI else none := rfl
theorem env1_constants (c : Name) : env1.constants c = if ``Nat = c then some natCI else none := rfl
theorem envA_defeqs (df : VDefEq) : envA.defeqs df ↔ df = iotaZeroLam ∨ df = iotaSuccLam ∨ False :=
  Iff.rfl

/-- Every rank is at most 2 (the rank of `Nat.rec`). -/
theorem rank_le (c : Name) : rank c ≤ 2 := by
  unfold rank; repeat' split
  all_goals decide

/-- A rule of `envA` has all its constants below `k` iff `rec` (rank 2) is. -/
theorem rule_onConsts {df : VDefEq} (hdf : envA.defeqs df) {k : Nat} :
    df.OnConsts (rank · < k) ↔ 2 < k := by
  have hrec : rank ``Nat.rec = 2 := rfl
  have hb : ∀ e : VExpr, 2 < k → e.OnConsts (rank · < k) := fun e hk =>
    (VExpr.onConsts_rankBound rank e).mono fun c _ => Nat.lt_of_le_of_lt (rank_le c) hk
  rcases hdf with rfl | rfl | h
  · exact ⟨fun h => hrec ▸ h.1.2.2.2.1.1.1.1, fun hk => ⟨hb _ hk, hb _ hk, hb _ hk⟩⟩
  · exact ⟨fun h => hrec ▸ h.1.2.2.2.2.1.1.1.1, fun hk => ⟨hb _ hk, hb _ hk, hb _ hk⟩⟩
  · exact (h : False).elim

theorem below_ge3 {k : Nat} (hk : 3 ≤ k) : envA.below rank k = envA := by
  apply VEnv.ext
  · funext c
    simp only [VEnv.below]
    rw [if_pos (Nat.lt_of_le_of_lt (rank_le c) hk)]
  · funext df
    apply propext
    exact ⟨And.left, fun h => ⟨h, (rule_onConsts h).2 hk⟩⟩

theorem below_2 : envA.below rank 2 = env3 := by
  apply VEnv.ext
  · funext c
    by_cases h1 : c = ``Nat.rec; · subst h1; rfl
    by_cases h2 : c = ``Nat.succ; · subst h2; rfl
    by_cases h3 : c = ``Nat.zero; · subst h3; rfl
    by_cases h4 : c = ``Nat; · subst h4; rfl
    simp [VEnv.below, envA_constants, env3_constants, Ne.symm h1, Ne.symm h2, Ne.symm h3,
      Ne.symm h4]
  · funext df
    apply propext
    exact ⟨fun h => absurd ((rule_onConsts h.1).1 h.2) (by omega), fun h => h.elim⟩

theorem below_1 : envA.below rank 1 = env1 := by
  apply VEnv.ext
  · funext c
    by_cases h1 : c = ``Nat.rec; · subst h1; rfl
    by_cases h2 : c = ``Nat.succ; · subst h2; rfl
    by_cases h3 : c = ``Nat.zero; · subst h3; rfl
    by_cases h4 : c = ``Nat; · subst h4; rfl
    simp [VEnv.below, envA_constants, env1_constants, Ne.symm h1, Ne.symm h2, Ne.symm h3,
      Ne.symm h4]
  · funext df
    apply propext
    exact ⟨fun h => absurd ((rule_onConsts h.1).1 h.2) (by omega), fun h => h.elim⟩

theorem below_0 : envA.below rank 0 = ∅ := by
  apply VEnv.ext
  · funext c
    simp only [VEnv.below, Nat.not_lt_zero, if_false]
    rfl
  · funext df
    apply propext
    exact ⟨fun h => absurd ((rule_onConsts h.1).1 h.2) (by omega), fun h => h.elim⟩

/-- `rank_ordered`: every prefix is one of the `Ordered` chains `∅`/`env1`/`env3`/`envA`. -/
theorem rank_ordered : ∀ k, (envA.below rank k).Ordered
  | 0 => by rw [below_0]; exact .empty
  | 1 => by rw [below_1]; exact env1_ordered
  | 2 => by rw [below_2]; exact env3_ordered
  | k+3 => by rw [below_ge3 (by omega)]; exact envA_ordered

theorem envA_constants_cases {c : Name} {ci : VConstant} (h : envA.constants c = some ci) :
    (c = ``Nat.rec ∧ ci = recCI) ∨ (c = ``Nat.succ ∧ ci = succCI) ∨
    (c = ``Nat.zero ∧ ci = zeroCI) ∨ (c = ``Nat ∧ ci = natCI) := by
  rw [envA_constants] at h; repeat' split at h
  all_goals simp_all

/-- `Nat.succ`'s type only mentions `Nat`, so it is a type already in `env1`. -/
theorem succCI_wf1 : succCI.WF env1 := ⟨_, .forallEDF (hasType_nat rfl []) (hasType_nat rfl _)⟩

/-- `type_below`: each constant's type is a type in the prefix of its own rank. -/
theorem type_below {c : Name} {ci : VConstant} (h : envA.constants c = some ci) :
    (envA.below rank (rank c)).IsType ci.uvars [] ci.type := by
  rcases envA_constants_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [show rank ``Nat.rec = 2 from rfl, below_2]; exact recCI_wf
  · rw [show rank ``Nat.succ = 1 from rfl, below_1]; exact succCI_wf1
  · rw [show rank ``Nat.zero = 1 from rfl, below_1]; exact zeroCI_wf
  · rw [show rank ``Nat = 0 from rfl, below_0]; exact natCI_wf

/-! ## `Pattern.gen` on `envA`, both rules, by `rfl`

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

theorem gen_succ : Pattern.gen envA rank classify succPat succRHS = some genSucc := rfl
theorem gen_zero : Pattern.gen envA rank classify zeroPat zeroRHS = some genZero := rfl

/-- Negative control: a wrong self list is rejected (so the `rfl` above is not vacuous). -/
example : Pattern.gen envA rank classify succPat succRHS ≠ some { genSucc with self := [] } := by
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
    (Pattern.gen envA rank classify p r.1).isSome := by
  cases hP with
  | zero => rw [gen_zero]; rfl
  | succ => rw [gen_succ]; rfl

theorem pat_check {p : Pattern} {r : p.RHS × p.Check} (hP : Pat p r) : r.2 = .true := by
  cases hP <;> rfl

/-! ### `pat_typed`: the generated contexts and `rhsAbs` typed in `env3 = envA.below rank 2` -/

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

theorem envA_const_rec : envA.constants ``Nat.rec = some recCI := rfl
theorem envA_const_succ : envA.constants ``Nat.succ = some succCI := rfl
theorem envA_const_zero : envA.constants ``Nat.zero = some zeroCI := rfl
theorem envA_const_nat : envA.constants ``Nat = some natCI := rfl

theorem pat_typed {p : Pattern} {r : p.RHS × p.Check} {g : PatGen} {ci : VConstant}
    (hP : Pat p r) (hg : Pattern.gen envA rank classify p r.1 = some g)
    (hci : envA.constants p.head = some ci) :
    OnCtx (g.self ++ g.ctx) (fun Γ A => (envA.below rank (rank p.head)).IsType ci.uvars Γ A) ∧
    (envA.below rank (rank p.head)).HasType ci.uvars (g.self ++ g.ctx) g.rhsAbs
      (g.type.liftN g.self.length) := by
  cases hP with
  | zero =>
    rw [gen_zero] at hg; cases hg
    rw [head_zero, envA_const_rec] at hci; cases hci
    rw [head_zero, show rank ``Nat.rec = 2 from rfl, below_2]
    exact ⟨ctx_s_wf, RzAbs_wf⟩
  | succ =>
    rw [gen_succ] at hg; cases hg
    rw [head_succ, envA_const_rec] at hci; cases hci
    rw [head_succ, show rank ``Nat.rec = 2 from rfl, below_2]
    exact ⟨ctx_r_wf, RsAbs_wf⟩

/-! ### `pat_defeq`: the open equations, in `envA` (`succ_open`, `zero_open` above) -/

theorem pat_defeq {p : Pattern} {r : p.RHS × p.Check} {g : PatGen} {ci : VConstant}
    (hP : Pat p r) (hg : Pattern.gen envA rank classify p r.1 = some g)
    (hci : envA.constants p.head = some ci) :
    envA.IsDefEq ci.uvars g.ctx g.lhs g.rhs g.type := by
  cases hP with
  | zero =>
    rw [gen_zero] at hg; cases hg
    rw [head_zero, envA_const_rec] at hci; cases hci
    exact zero_open
  | succ =>
    rw [gen_succ] at hg; cases hg
    rw [head_succ, envA_const_rec] at hci; cases hci
    exact succ_open

/-! ## The classification fields -/

theorem indTy_closed {I : Name} {k : Nat} {ci : VConstant} (hcl : classify I = some (.indTy k))
    (hci : envA.constants I = some ci) : k = 0 ∧ ∃ u, ci.type = .sort u := by
  rcases classify_cases hcl with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> cases h
  rw [envA_const_nat] at hci; cases hci
  exact ⟨rfl, _, rfl⟩

theorem ctor_fields_closed {c : Name} {cl : Classification} {ci : VConstant}
    (hctor : cl matches .ctor .. | .etaCtor ..) (hcl : classify c = some cl)
    (hci : envA.constants c = some ci) :
    ∃ (I : Name) (Ts : List VExpr), ci.type = Ts.foldr .forallE (.const I (VLevel.params ci.uvars)) ∧
      ∀ T ∈ Ts, ∃ (I' : Name) (us : List VLevel), T = .const I' us ∧
        classify I' = some (.indTy 0) := by
  rcases classify_cases hcl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact nomatch hctor
  · rw [envA_const_zero] at hci; cases hci
    exact ⟨``Nat, [], rfl, nofun⟩
  · rw [envA_const_succ] at hci; cases hci
    refine ⟨``Nat, [natTy], rfl, fun T hT => ?_⟩
    rw [List.mem_singleton] at hT; subst hT
    exact ⟨``Nat, [], rfl, rfl⟩
  · exact nomatch hctor

theorem ctor_syn {c : Name} {cl : Classification} {ci : VConstant}
    (hctor : cl matches .ctor .. | .etaCtor ..) (hcl : classify c = some cl)
    (hci : envA.constants c = some ci) :
    ∃ (I : Name) (Ts args : List VExpr),
      Ts.length = cl.arity ∧ classify I = some (.indTy args.length) ∧
      ci.type = Ts.foldr .forallE
        (args.foldr (fun A acc => acc.app A) (.const I (VLevel.params ci.uvars))) := by
  rcases classify_cases hcl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact nomatch hctor
  · cases Option.some.inj hci; exact ⟨``Nat, [], [], rfl, rfl, rfl⟩
  · cases Option.some.inj hci; exact ⟨``Nat, [natTy], [], rfl, rfl, rfl⟩
  · exact nomatch hctor

/-! ## The iota-rule invariants (PLAN D4, from E6) -/

/-- The major domain of `Nat.rec` is `const Nat []`, and `Nat` is an inductive type. (In `envA`
every constant domain of a top-level binder is `Nat`, so the proof does not need the rule.) -/
theorem rec_major_indTy {rec c' : Name} {m n : Nat}
    {r : (Pattern.iota rec m c' n).RHS × (Pattern.iota rec m c' n).Check} {ci : VConstant}
    {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr}
    (_ : Pat (.iota rec m c' n) r) (h1 : envA.constants rec = some ci)
    (hty : ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj)) (_ : Hs.length = m) :
    ∃ k, classify I = some (.indTy k) := by
  have hI : I = ``Nat := by
    rcases envA_constants_cases h1 with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      rcases Hs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
      simp_all [recCI, succCI, zeroCI, natCI, natTy, motiveTy, zTy, sTy]
  exact ⟨0, hI ▸ rfl⟩

/-- Neither rule's right-hand side is a bare constructor field: `zeroRHS` is the minor `z`
(`.var (.inl pZ)`), `succRHS` is an application. -/
theorem rhs_not_field {rec c' : Name} {m n : Nat}
    {r : (Pattern.iota rec m c' n).RHS × (Pattern.iota rec m c' n).Check}
    (hP : Pat (.iota rec m c' n) r) : ∀ x, r.1 ≠ .var (.inr x) := by
  -- generalize the two `varN`s, which `cases` cannot unify with the rules' patterns
  suffices ∀ {f a : Pattern} {r : (Pattern.app f a).RHS × (Pattern.app f a).Check},
      Pat (.app f a) r → ∀ x, r.1 ≠ .var (.inr x) from this hP
  intro f a r hP
  cases hP <;> nofun

/-- `ctor_sort` for `ℕ`: every derivable sort of `Nat` (resp. `Nat → Nat`) is non-zero. -/
theorem ctor_sort_nat {c : Name} {cl : Classification} {ci : VConstant} {U : Nat}
    {vs : List VLevel} {u : VLevel} :
    (cl matches .ctor .. | .etaCtor ..) → classify c = some cl → envA.constants c = some ci →
    (∀ l ∈ vs, l.WF U) → vs.length = ci.uvars →
    envA.HasType U [] (ci.type.instL vs) (.sort u) → ∀ ns, u.eval ns ≠ 0 :=
  sorry -- SORRY (blocked): needs `IsDefEq.uniq` + `IsDefEqU.sort_inv` (Injectivity.lean, itself
        -- `sorry`) to get `u ≈ succ zero` from `HasType [] Nat (sort u)`; then `eval ≠ 0` is `rfl`.
        -- The rules of `envA` do not change this.

/-! ## `pat_uniq`

A finite check: enumerate the subpatterns of each pattern (6 + 7), compute `inter` by `decide`. -/
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

/-! ## The λ-`extra_patV` for `envA` (D5, R6)

Each rule, at any well-formed level `l`, is the λ-closure over `Δ` (3 binders for the zero rule,
4 for succ) of the `instL [l]` image of its open equation (`zero_open`/`succ_open`, via
`IsDefEq.instL`), whose left side matches the rule's pattern (`zero_instance`/`succ_instance`,
at `M Z S (N) := bvar …`). -/

theorem onCtx_mono_A {Γ : List VExpr} (h : OnCtx Γ (env3.IsType 1)) : OnCtx Γ (envA.IsType 1) :=
  OnCtx.mono (fun h => h.mono (env3_le_envC.trans envC_le_envA)) h

theorem extra_patV {U : Nat} {df : VDefEq} {ls : List VLevel} {Γ : List VExpr} :
    envA.defeqs df → (∀ l ∈ ls, l.WF U) → ls.length = df.uvars →
    ∃ (Δ : List VExpr) (L R T : VExpr),
      df.lhs.instL ls = Δ.foldr .lam L ∧ df.rhs.instL ls = Δ.foldr .lam R ∧
      df.type.instL ls = Δ.foldr .forallE T ∧
      OnCtx Δ.reverse (envA.IsType U) ∧
      envA.IsDefEq U Δ.reverse L R T ∧
      ∃ p r m1 m2, Pat p r ∧ p.Matches L m1 m2 ∧
        r.2.OK (envA.IsDefEqU U (Δ.reverse ++ Γ)) m1 m2 ∧ R = r.1.apply m1 m2 := by
  intro hdf hls hlen
  rcases hdf with rfl | rfl | h
  · -- zero rule: strip 3 binders
    match ls, hlen with
    | [l], _ =>
      obtain ⟨m2, hm, hr⟩ := zero_instance l (.bvar 2) (.bvar 1) (.bvar 0)
      exact ⟨Γs.reverse.map (VExpr.instL [l]), Lz.instL [l], Rz.instL [l], Tz.instL [l],
        rfl, rfl, rfl, OnCtx.instL hls (onCtx_mono_A ctx_s_wf), VEnv.IsDefEq.instL hls zero_open,
        zeroPat, (zeroRHS, .true), [l], m2, .zero, hm, trivial, hr.symm⟩
  · -- succ rule: strip 4 binders
    match ls, hlen with
    | [l], _ =>
      obtain ⟨m2, hm, hr⟩ := succ_instance l (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)
      exact ⟨Γn.reverse.map (VExpr.instL [l]), Ls.instL [l], Rs.instL [l], Ts.instL [l],
        rfl, rfl, rfl, OnCtx.instL hls (onCtx_mono_A ctx_n_wf), VEnv.IsDefEq.instL hls succ_open,
        succPat, (succRHS, .true), [l], m2, .succ, hm, trivial, hr.symm⟩
  · exact (h : False).elim

/-! ## The instance -/

/-- `Params` over `envA` (the four `Nat` constants plus the two λ-wrapped iota rules), `Pat` the
two iota patterns, ranks `Nat 0, zero 1, succ 1, rec 2`. -/
@[instance_reducible] def natParams : Params := {
  env := envA
  henv := envA_ordered
  univs := 0
  Pat := Pat
  classify := classify
  pat_simple := fun h => by cases h <;> exact ⟨_, rfl⟩
  pat_wf := fun h => by cases h <;> exact ⟨rfl, rfl⟩
  pat_uniq := pat_uniq_nat
  extra_patV := extra_patV
  ctor_syn := ctor_syn
  ctor_sort := ctor_sort_nat           -- SORRY (blocked on `IsDefEqU.sort_inv`)
  rank := rank
  rank_ordered := rank_ordered
  type_below := type_below
  pat_rank := pat_rank
  pat_gen := pat_gen
  pat_typed := pat_typed
  pat_defeq := pat_defeq
  pat_check := pat_check
  indTy_closed := indTy_closed
  ctor_fields_closed := ctor_fields_closed
  rec_major_indTy := rec_major_indTy
  rhs_not_field := rhs_not_field
}

#print axioms natParams
-- which pieces carry `sorryAx` (only `ctor_sort_nat`):
#print axioms envA_ordered
#print axioms extra_patV
#print axioms pat_defeq
#print axioms pat_uniq_nat
#print axioms rank_ordered
#print axioms type_below
#print axioms pat_typed
#print axioms ctor_sort_nat
#print axioms extra_patV_false_envA
#print axioms iotaZeroOpen_not_wf

/-! ## Summary

One `sorry` in this file, marked `-- SORRY`: `ctor_sort_nat`, blocked on the repo's own sorried
`IsDefEqU.sort_inv` (Injectivity.lean). It is the only `sorryAx` reaching `natParams`.

Field status for `ℕ` (`natParams`, env = `envA`, the four constants plus the two λ-wrapped iota
rules; `Pat` = the two iota patterns):
* `env`, `univs`, `Pat`, `classify`           — defined.
* `henv`                                       — proven (`envA_ordered`: `recCI_wf` and the two
  rules' typings `iotaSuccLam_wf`, `iotaZeroLam_wf`).
* `pat_simple`, `pat_wf`                       — proven, `rfl`-level.
* `pat_uniq`                                   — proven, finite `decide` over 13 subpatterns.
* `extra_patV`                                 — proven (the λ-form, D5/R6): each rule is the
  λ-closure of its open equation (`zero_open`/`succ_open`), whose lhs matches the rule's pattern.
  The `Δ = []` form it replaced is false here (`extra_patV_false_envA`); the open-`bvar` encoding
  that would satisfy it is not `VDefEq.WF` (`iotaZeroOpen_not_wf`).
* `ctor_syn`                                   — proven (`Ts = []` / `[natTy]`, `args = []`).
* `ctor_sort`                                  — true (`u ≈ 1`), proof needs sort inversion: the
  one `sorry`.
* `rank`, `rank_ordered`, `type_below`         — ranks `Nat 0, zero 1, succ 1, rec 2`; the
  prefixes `envA.below rank k` are `∅`/`env1`/`env3`/`envA`.
* `pat_rank`, `pat_gen`, `pat_check`           — proven; `Pattern.gen` evaluated by `rfl`.
* `pat_typed`                                  — proven, in `env3 = envA.below rank 2`.
* `pat_defeq`                                  — proven: the open equations `succ_open`,
  `zero_open` (the λ-rule applied to the context's variables, beta-reduced on both sides).
* `indTy_closed`, `ctor_fields_closed`         — proven.
* `rec_major_indTy`, `rhs_not_field`           — proven (PLAN D4, from E6; landed by R10):
  `Nat.rec`'s major domain is `const Nat []` with `Nat` an `indTy`; `zeroRHS` is the minor `z`,
  `succRHS` an application. -/

end NatEnv
end Lean4Lean
