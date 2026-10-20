import Lean4Lean.Experimental.E3.Measure7
/-! # E4: the post-R5/R6 `Params` field list (`ParamsR`) and an instance over `envA`

PLAN.md §2 row E4, §1 D5 (satisfiability table) and D4/D3 (the new fields).

* `ParamsR` (namespace `Lean4Lean`, VExpr level): every field of today's `class Params`
  (SExpr.lean:98) text for text, with the old (`Δ = []`) `extra_patV` replaced by D5's λ-form
  (the body of `ExtraPatVLam`, plan/E5/LamRules.lean:10-19), plus the ten fields of E3's
  `RankParams` (Measure7.lean), with `Params.env`/`Params.univs`/`Params.Pat`/`Params.classify`
  read as the structure's own fields.
* `NatEnvA.natParamsR : ParamsR` over `envA` (docs/params/NatParams.lean:162, definitions copied:
  docs files are not importable), with ranks Nat 0, zero 1, succ 1, rec 2 (as E3's GenNat.lean;
  every other name 2), so `envA.below rank k` is `∅`, `env1`, `env3`, `envA` for `k = 0, 1, 2, ≥3`.
  `Pattern.gen` (E3, attempt b) is evaluated on both rules by `rfl` (`gen_zero`, `gen_succ`).
  The open equations of `pat_defeq` and of the λ-`extra_patV` come from the λ-rule itself
  (`extra`), opened binder by binder (`lam_open_tel`: weaken, `appDF` with `bvar 0`, `beta` on both
  sides, the bodies typed directly); spec lemma (f) is not needed here.
  NatParams.lean's `iotaSuccLam_wf`/`iotaZeroLam_wf` are proved (`lamDF_tel` over the open
  typings). One sorry: `ctor_sort_nat` (blocked on `IsDefEqU.sort_inv`, as in NatParams.lean).
-/
namespace Lean4Lean
open Lean (Name)

/-- The post-R5/R6 `Params` field list (E4 pins it for R5). -/
structure ParamsR where
  env : VEnv
  henv : env.Ordered
  univs : Nat
  Pat : (p : Pattern) → p.RHS × p.Check → Prop
  classify : Name → Option Classification
  pat_simple : Pat p r → ∃ sp : SimplePattern, p = sp.toPattern
  pat_wf : Pat p r → p.WF classify
  pat_uniq : Pat p₁ r → Pat p₂ r' → Subpattern p₃ p₁ → p₂.inter p₃ = some p₄ →
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r'
  /-- D5's λ-`extra_patV` (replaces SExpr.lean:120, the `Δ = []` form): every instantiated
  defeq rule is the λ-closure over `Δ` of a well-typed open equation whose left side is a
  pattern instance. -/
  extra_patV {df : VDefEq} {ls : List VLevel} {Γ : List VExpr} :
    env.defeqs df → (∀ l ∈ ls, l.WF univs) → ls.length = df.uvars →
    ∃ (Δ : List VExpr) (L R T : VExpr),
      df.lhs.instL ls = Δ.foldr .lam L ∧ df.rhs.instL ls = Δ.foldr .lam R ∧
      df.type.instL ls = Δ.foldr .forallE T ∧
      OnCtx Δ.reverse (env.IsType univs) ∧
      env.IsDefEq univs Δ.reverse L R T ∧
      ∃ p r m1 m2, Pat p r ∧ p.Matches L m1 m2 ∧
        r.2.OK (env.IsDefEqU univs (Δ.reverse ++ Γ)) m1 m2 ∧ R = r.1.apply m1 m2
  /-- The type of a constructor (`classify c = ctor/etaCtor`) *is* syntactically a Π-telescope
  `Ts` over an application of the inductive type `I` (at the constant's own universe parameters)
  to `args`, with `Ts.length` the classified arity and `I` classified as an inductive type with
  `args.length` indices.  Lean's kernel guarantees this shape for every constructor it accepts.
  A merely *definitional* equation to such a telescope would not do: the strong judgment
  `IsDefEqStrong.const` needs the equation as a strong derivation, and translating a defeq
  derivation that lives in the full environment can require the strong typing of the very
  constant whose type is being described (`IsDefEq.strong` is then unprovable in general). -/
  ctor_syn {c : Name} {cl : Classification} {ci : VConstant} :
    (cl matches .ctor .. | .etaCtor ..) → classify c = some cl → env.constants c = some ci →
    ∃ (I : Name) (Ts args : List VExpr),
      Ts.length = cl.arity ∧ classify I = some (.indTy args.length) ∧
      ci.type = Ts.foldr .forallE
        (args.foldr (fun A acc => acc.app A) (.const I (VLevel.params ci.uvars)))
  /-- Every derivable sort of (an instance of) a constructor's type is non-zero under every
  universe assignment.  This is what makes the instantiated sort `SLevel.mk u ≠ .zero` demanded
  by `CtorBundle.hu0`; it excludes classifying constructors of universe-polymorphic inductives
  that can be instantiated to `Prop` (e.g. `PUnit.{u}`), which must stay unclassified.  It is
  stated for every derivable sort rather than one canonical sort because the strong `const`
  rule ties the bundle's sort to the sort of the derivation at hand, and sort uniqueness is not
  available at this point. -/
  ctor_sort {c : Name} {cl : Classification} {ci : VConstant} {U : Nat} {vs : List VLevel}
      {u : VLevel} :
    (cl matches .ctor .. | .etaCtor ..) → classify c = some cl → env.constants c = some ci →
    (∀ l ∈ vs, l.WF U) → vs.length = ci.uvars →
    env.HasType U [] (ci.type.instL vs) (.sort u) → ∀ ns, u.eval ns ≠ 0
  rank : Name → Nat
  rank_ordered : ∀ k, (env.below rank k).Ordered
  type_below : ∀ {c ci}, env.constants c = some ci →
    (env.below rank (rank c)).IsType ci.uvars [] ci.type
  pat_rank : ∀ {p : Pattern} {r : p.RHS × p.Check} {c' us}, Pat p r →
    VExpr.const c' us ∈ r.1.fixedLeaves → rank c' ≤ rank p.head
  pat_gen : ∀ {p : Pattern} {r : p.RHS × p.Check}, Pat p r →
    (Pattern.gen env rank classify p r.1).isSome
  pat_typed : ∀ {p : Pattern} {r : p.RHS × p.Check} {g ci}, Pat p r →
    Pattern.gen env rank classify p r.1 = some g →
    env.constants p.head = some ci →
    OnCtx (g.self ++ g.ctx) (fun Γ A => (env.below rank (rank p.head)).IsType ci.uvars Γ A) ∧
    (env.below rank (rank p.head)).HasType ci.uvars (g.self ++ g.ctx) g.rhsAbs
      (g.type.liftN g.self.length)
  pat_defeq : ∀ {p : Pattern} {r : p.RHS × p.Check} {g ci}, Pat p r →
    Pattern.gen env rank classify p r.1 = some g →
    env.constants p.head = some ci →
    env.IsDefEq ci.uvars g.ctx g.lhs g.rhs g.type
  /-- stage 1a only -/
  pat_check : ∀ {p : Pattern} {r : p.RHS × p.Check}, Pat p r → r.2 = .true
  /-- stage-1a restriction (D3), not a kernel invariant -/
  indTy_closed : ∀ {I k ci}, classify I = some (.indTy k) → env.constants I = some ci →
    k = 0 ∧ ∃ u, ci.type = .sort u
  /-- stage-1a restriction (D3), not a kernel invariant -/
  ctor_fields_closed : ∀ {c : Name} {cl : Classification} {ci : VConstant},
    (cl matches .ctor .. | .etaCtor ..) → classify c = some cl →
    env.constants c = some ci →
    ∃ (I : Name) (Ts : List VExpr), ci.type = Ts.foldr .forallE (.const I (VLevel.params ci.uvars)) ∧
      ∀ T ∈ Ts, ∃ I' us, T = .const I' us ∧ classify I' = some (.indTy 0)

namespace NatEnvA

/-! ## The `ℕ` environment (copied from docs/params/NatParams.lean) -/

def natTy : VExpr := .const ``Nat []
def natCI  : VConstant := ⟨0, .sort (.succ .zero)⟩            -- Nat : Type
def zeroCI : VConstant := ⟨0, natTy⟩                           -- Nat.zero : Nat
def succCI : VConstant := ⟨0, .forallE natTy natTy⟩            -- Nat.succ : Nat → Nat

def motiveTy : VExpr := .forallE natTy (.sort (.param 0))                 -- motive : Nat → Sort u
def zTy : VExpr := .app (.bvar 0) (.const ``Nat.zero [])                  -- [motive] ⊢ motive .zero
def sTy : VExpr := .forallE natTy (.forallE (.app (.bvar 2) (.bvar 0))    -- [motive,z] ⊢
  (.app (.bvar 3) (.app (.const ``Nat.succ []) (.bvar 1))))               --   (n:Nat) → motive n → motive (.succ n)
def recCI : VConstant := ⟨1,
  .forallE motiveTy (.forallE zTy (.forallE sTy (.forallE natTy (.app (.bvar 3) (.bvar 0)))))⟩

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

def recPre : Pattern := .var (.var (.var (.const ``Nat.rec)))
def zeroPat : Pattern := (SimplePattern.iota ``Nat.rec 3 ``Nat.zero 0).toPattern
def succPat : Pattern := (SimplePattern.iota ``Nat.rec 3 ``Nat.succ 1).toPattern

def pS      : recPre.Path := none
def pZ      : recPre.Path := some none
def pMotive : recPre.Path := some (some none)

/-- `Nat.rec motive z s Nat.zero ≡ z` -/
def zeroRHS : zeroPat.RHS := .var (.inl pZ)

/-- `Nat.rec motive z s (Nat.succ n) ≡ s n (Nat.rec motive z s n)` -/
def succRHS : succPat.RHS :=
  let n : succPat.Path := .inr none
  .app (.app (.var (.inl pS)) (.var n))
    (.app (.app (.app (.app (.fixed (.const ``Nat.rec [.param 0]) trivial)
      (.var (.inl pMotive))) (.var (.inl pZ))) (.var (.inl pS))) (.var n))

inductive Pat : (p : Pattern) → p.RHS × p.Check → Prop
  | zero : Pat zeroPat (zeroRHS, .true)
  | succ : Pat succPat (succRHS, .true)

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

/-- encoding (A): closed, λ-wrapped iota rules -/
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

def env1 : VEnv := ((∅ : VEnv).addConst ``Nat natCI).getD ∅
def env2 : VEnv := (env1.addConst ``Nat.zero zeroCI).getD ∅
def env3 : VEnv := (env2.addConst ``Nat.succ succCI).getD ∅
/-- the four constants, no rules -/
def envC : VEnv := (env3.addConst ``Nat.rec recCI).getD ∅
/-- the four constants plus the two iota rules in encoding (A) -/
def envA : VEnv := (envC.addDefEq iotaSuccLam).addDefEq iotaZeroLam

/-- ranks as in E3's GenNat.lean: Nat 0, zero 1, succ 1, rec 2 (every other name 2) -/
def rank (c : Name) : Nat :=
  if c = ``Nat then 0 else if c = ``Nat.zero then 1 else if c = ``Nat.succ then 1 else 2

def gZero : PatGen where
  ctx := [sTy, zTy, motiveTy]
  self := []
  lhs := recApp (.bvar 2) (.bvar 1) (.bvar 0) (.const ``Nat.zero [])
  rhs := .bvar 1
  rhsAbs := .bvar 1
  type := .app (.bvar 2) (.const ``Nat.zero [])

def gSucc : PatGen where
  ctx := [natTy, sTy, zTy, motiveTy]
  self := [recCI.type]
  lhs := recApp (.bvar 3) (.bvar 2) (.bvar 1) (.app (.const ``Nat.succ []) (.bvar 0))
  rhs := .app (.app (.bvar 1) (.bvar 0)) (recApp (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
  rhsAbs := .app (.app (.bvar 2) (.bvar 1))
    (.app (.app (.app (.app (.bvar 0) (.bvar 4)) (.bvar 3)) (.bvar 2)) (.bvar 1))
  type := .app (.bvar 3) (.app (.const ``Nat.succ []) (.bvar 0))

/-- `Pattern.gen` on the zero rule (E3 attempt b's `gen`, evaluated by `rfl`): ctx `[s, z, motive]`,
no self occurrence. -/
theorem gen_zero : Pattern.gen envA rank classify zeroPat zeroRHS = some gZero := rfl
/-- `Pattern.gen` on the succ rule: ctx `[n, s, z, motive]`, one self occurrence (the recursive
call `Nat.rec.{u}`, rank 2 = rank of the head). -/
theorem gen_succ : Pattern.gen envA rank classify succPat succRHS = some gSucc := rfl

/-! The generated data are the open bodies of the λ-wrapped rules: `ctx` is the stripped binder
telescope (3 binders for the zero rule, 4 for succ) and `lhs`/`rhs`/`type` the bodies. So
`pat_defeq`'s equation and `extra_patV`'s open equation (at `u = .param 0`) are the same. -/
example : gZero.ctx = [motiveTy, zTy, sTy].reverse ∧
    iotaZeroLam.lhs = [motiveTy, zTy, sTy].foldr .lam gZero.lhs ∧
    iotaZeroLam.rhs = [motiveTy, zTy, sTy].foldr .lam gZero.rhs ∧
    iotaZeroLam.type = [motiveTy, zTy, sTy].foldr .forallE gZero.type := ⟨rfl, rfl, rfl, rfl⟩
example : gSucc.ctx = [motiveTy, zTy, sTy, natTy].reverse ∧
    iotaSuccLam.lhs = [motiveTy, zTy, sTy, natTy].foldr .lam gSucc.lhs ∧
    iotaSuccLam.rhs = [motiveTy, zTy, sTy, natTy].foldr .lam gSucc.rhs ∧
    iotaSuccLam.type = [motiveTy, zTy, sTy, natTy].foldr .forallE gSucc.type :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Generic typings (any environment holding the constants, any level `u`)

`mTy u`, `recAppU u`, `recTyU u` are `motiveTy`, `recApp`, `recCI.type` at the level `u`
(at `u = .param 0` they are those terms, by `rfl`). -/

def mTy (u : VLevel) : VExpr := .forallE natTy (.sort u)
def recAppU (u : VLevel) (motive z s t : VExpr) : VExpr :=
  .app (.app (.app (.app (.const ``Nat.rec [u]) motive) z) s) t
def recTyU (u : VLevel) : VExpr :=
  .forallE (mTy u) (.forallE zTy (.forallE sTy (.forallE natTy (.app (.bvar 3) (.bvar 0)))))

example : mTy (.param 0) = motiveTy := rfl
example : recTyU (.param 0) = recCI.type := rfl
example (u : VLevel) : recCI.type.instL [u] = recTyU u := rfl

theorem ty_nat {E : VEnv} {U : Nat} (hN : E.constants ``Nat = some natCI) (Γ : List VExpr) :
    E.HasType U Γ natTy (.sort (.succ .zero)) :=
  .constDF (ci := natCI) hN (by simp) (by simp) rfl .nil
theorem ty_zero {E : VEnv} {U : Nat} (hZ : E.constants ``Nat.zero = some zeroCI)
    (Γ : List VExpr) : E.HasType U Γ (.const ``Nat.zero []) natTy :=
  .constDF (ci := zeroCI) hZ (by simp) (by simp) rfl .nil
theorem ty_succ {E : VEnv} {U : Nat} (hS : E.constants ``Nat.succ = some succCI)
    (Γ : List VExpr) : E.HasType U Γ (.const ``Nat.succ []) (.forallE natTy natTy) :=
  .constDF (ci := succCI) hS (by simp) (by simp) rfl .nil
theorem ty_rec {E : VEnv} {U : Nat} {u : VLevel} (hu : u.WF U)
    (hR : E.constants ``Nat.rec = some recCI) (Γ : List VExpr) :
    E.HasType U Γ (.const ``Nat.rec [u]) (recTyU u) :=
  .constDF (ci := recCI) hR (by simpa using hu) (by simpa using hu) rfl (.cons rfl .nil)

theorem ty_mTy {E : VEnv} {U : Nat} {u : VLevel} (hu : u.WF U)
    (hN : E.constants ``Nat = some natCI) (Γ : List VExpr) :
    E.HasType U Γ (mTy u) (.sort (.imax (.succ .zero) (.succ u))) :=
  .forallEDF (ty_nat hN _) (.sortDF hu hu rfl)

theorem ty_zTy {E : VEnv} {U : Nat} {u : VLevel} (hZ : E.constants ``Nat.zero = some zeroCI)
    (Γ : List VExpr) : E.HasType U (mTy u :: Γ) zTy (.sort u) :=
  VEnv.IsDefEq.appDF (VEnv.IsDefEq.bvar (Γ := mTy u :: Γ) .zero) (ty_zero hZ _)

theorem ty_sTy {E : VEnv} {U : Nat} {u : VLevel}
    (hN : E.constants ``Nat = some natCI) (hS : E.constants ``Nat.succ = some succCI)
    (Γ : List VExpr) :
    E.HasType U (zTy :: mTy u :: Γ) sTy (.sort (.imax (.succ .zero) (.imax u u))) :=
  have hMn : E.HasType U (natTy :: zTy :: mTy u :: Γ) (.app (.bvar 2) (.bvar 0)) (.sort u) :=
    VEnv.IsDefEq.appDF (VEnv.IsDefEq.bvar (Γ := natTy :: zTy :: mTy u :: Γ) (.succ (.succ .zero)))
      (VEnv.IsDefEq.bvar (Γ := natTy :: zTy :: mTy u :: Γ) .zero)
  have hMsn : E.HasType U (.app (.bvar 2) (.bvar 0) :: natTy :: zTy :: mTy u :: Γ)
      (.app (.bvar 3) (.app (.const ``Nat.succ []) (.bvar 1))) (.sort u) :=
    VEnv.IsDefEq.appDF
      (VEnv.IsDefEq.bvar (Γ := .app (.bvar 2) (.bvar 0) :: natTy :: zTy :: mTy u :: Γ)
        (.succ (.succ (.succ .zero))))
      (VEnv.IsDefEq.appDF (ty_succ hS _)
        (VEnv.IsDefEq.bvar (Γ := .app (.bvar 2) (.bvar 0) :: natTy :: zTy :: mTy u :: Γ)
          (.succ .zero)))
  .forallEDF (ty_nat hN _) (.forallEDF hMn hMsn)

theorem ty_recTy {E : VEnv} {U : Nat} {u : VLevel} (hu : u.WF U)
    (hN : E.constants ``Nat = some natCI) (hZ : E.constants ``Nat.zero = some zeroCI)
    (hS : E.constants ``Nat.succ = some succCI) (Γ : List VExpr) :
    E.IsType U Γ (recTyU u) :=
  have hMt : E.HasType U (natTy :: sTy :: zTy :: mTy u :: Γ) (.app (.bvar 3) (.bvar 0))
      (.sort u) :=
    VEnv.IsDefEq.appDF
      (VEnv.IsDefEq.bvar (Γ := natTy :: sTy :: zTy :: mTy u :: Γ) (.succ (.succ (.succ .zero))))
      (VEnv.IsDefEq.bvar (Γ := natTy :: sTy :: zTy :: mTy u :: Γ) .zero)
  ⟨_, .forallEDF (ty_mTy hu hN _) (.forallEDF (ty_zTy hZ _) (.forallEDF (ty_sTy hN hS _)
    (.forallEDF (ty_nat hN _) hMt)))⟩

/-- the zero rule's binder context `[s, z, motive]` (innermost first) is well-typed -/
theorem ctx_zero {E : VEnv} {U : Nat} {u : VLevel} (hu : u.WF U)
    (hN : E.constants ``Nat = some natCI) (hZ : E.constants ``Nat.zero = some zeroCI)
    (hS : E.constants ``Nat.succ = some succCI) :
    OnCtx [sTy, zTy, mTy u] (E.IsType U) :=
  ⟨⟨⟨trivial, _, ty_mTy hu hN []⟩, _, ty_zTy hZ []⟩, _, ty_sTy hN hS []⟩

/-- the succ rule's binder context `[n, s, z, motive]` is well-typed -/
theorem ctx_succ {E : VEnv} {U : Nat} {u : VLevel} (hu : u.WF U)
    (hN : E.constants ``Nat = some natCI) (hZ : E.constants ``Nat.zero = some zeroCI)
    (hS : E.constants ``Nat.succ = some succCI) :
    OnCtx [natTy, sTy, zTy, mTy u] (E.IsType U) :=
  ⟨ctx_zero hu hN hZ hS, _, ty_nat hN _⟩

/-- zero rule, open LHS: `[s, z, motive] ⊢ Nat.rec.{u} motive z s Nat.zero : motive Nat.zero` -/
theorem ty_zeroL {E : VEnv} {U : Nat} {u : VLevel} (hu : u.WF U)
    (hZ : E.constants ``Nat.zero = some zeroCI) (hR : E.constants ``Nat.rec = some recCI) :
    E.HasType U [sTy, zTy, mTy u] (recAppU u (.bvar 2) (.bvar 1) (.bvar 0) (.const ``Nat.zero []))
      (.app (.bvar 2) (.const ``Nat.zero [])) :=
  have h1 := VEnv.IsDefEq.appDF (ty_rec hu hR _)
    (VEnv.IsDefEq.bvar (Γ := [sTy, zTy, mTy u]) (.succ (.succ .zero)))
  have h2 := VEnv.IsDefEq.appDF h1 (VEnv.IsDefEq.bvar (Γ := [sTy, zTy, mTy u]) (.succ .zero))
  have h3 := VEnv.IsDefEq.appDF h2 (VEnv.IsDefEq.bvar (Γ := [sTy, zTy, mTy u]) .zero)
  VEnv.IsDefEq.appDF h3 (ty_zero hZ _)

/-- zero rule, open RHS: `[s, z, motive] ⊢ z : motive Nat.zero` -/
theorem ty_zeroR {E : VEnv} {U : Nat} {u : VLevel} :
    E.HasType U [sTy, zTy, mTy u] (.bvar 1) (.app (.bvar 2) (.const ``Nat.zero [])) :=
  .bvar (.succ .zero)

/-- succ rule, open LHS: `[n, s, z, motive] ⊢ Nat.rec.{u} motive z s (succ n) : motive (succ n)` -/
theorem ty_succL {E : VEnv} {U : Nat} {u : VLevel} (hu : u.WF U)
    (hS : E.constants ``Nat.succ = some succCI) (hR : E.constants ``Nat.rec = some recCI) :
    E.HasType U [natTy, sTy, zTy, mTy u]
      (recAppU u (.bvar 3) (.bvar 2) (.bvar 1) (.app (.const ``Nat.succ []) (.bvar 0)))
      (.app (.bvar 3) (.app (.const ``Nat.succ []) (.bvar 0))) :=
  have h1 := VEnv.IsDefEq.appDF (ty_rec hu hR _)
    (VEnv.IsDefEq.bvar (Γ := [natTy, sTy, zTy, mTy u]) (.succ (.succ (.succ .zero))))
  have h2 := VEnv.IsDefEq.appDF h1
    (VEnv.IsDefEq.bvar (Γ := [natTy, sTy, zTy, mTy u]) (.succ (.succ .zero)))
  have h3 := VEnv.IsDefEq.appDF h2 (VEnv.IsDefEq.bvar (Γ := [natTy, sTy, zTy, mTy u]) (.succ .zero))
  VEnv.IsDefEq.appDF h3 (VEnv.IsDefEq.appDF (ty_succ hS _)
    (VEnv.IsDefEq.bvar (Γ := [natTy, sTy, zTy, mTy u]) .zero))

/-- the recursive call `[n, s, z, motive] ⊢ Nat.rec.{u} motive z s n : motive n` -/
theorem ty_recCall {E : VEnv} {U : Nat} {u : VLevel} (hu : u.WF U)
    (hR : E.constants ``Nat.rec = some recCI) :
    E.HasType U [natTy, sTy, zTy, mTy u] (recAppU u (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
      (.app (.bvar 3) (.bvar 0)) :=
  have h1 := VEnv.IsDefEq.appDF (ty_rec hu hR _)
    (VEnv.IsDefEq.bvar (Γ := [natTy, sTy, zTy, mTy u]) (.succ (.succ (.succ .zero))))
  have h2 := VEnv.IsDefEq.appDF h1
    (VEnv.IsDefEq.bvar (Γ := [natTy, sTy, zTy, mTy u]) (.succ (.succ .zero)))
  have h3 := VEnv.IsDefEq.appDF h2 (VEnv.IsDefEq.bvar (Γ := [natTy, sTy, zTy, mTy u]) (.succ .zero))
  VEnv.IsDefEq.appDF h3 (VEnv.IsDefEq.bvar (Γ := [natTy, sTy, zTy, mTy u]) .zero)

/-- succ rule, open RHS: `[n, s, z, motive] ⊢ s n (Nat.rec.{u} motive z s n) : motive (succ n)` -/
theorem ty_succR {E : VEnv} {U : Nat} {u : VLevel} (hu : u.WF U)
    (hR : E.constants ``Nat.rec = some recCI) :
    E.HasType U [natTy, sTy, zTy, mTy u]
      (.app (.app (.bvar 1) (.bvar 0)) (recAppU u (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)))
      (.app (.bvar 3) (.app (.const ``Nat.succ []) (.bvar 0))) :=
  have h1 := VEnv.IsDefEq.appDF (VEnv.IsDefEq.bvar (Γ := [natTy, sTy, zTy, mTy u]) (.succ .zero))
    (VEnv.IsDefEq.bvar (Γ := [natTy, sTy, zTy, mTy u]) .zero)
  VEnv.IsDefEq.appDF h1 (ty_recCall hu hR)

/-- succ rule, self-abstracted RHS (`pat_typed`, D4's table row):
`[self : rec.type, n, s, z, motive] ⊢ s n (self motive z s n) : motive (succ n)`, with no
`Nat.rec` constant (so it lives in the rank prefix below `Nat.rec`). -/
theorem ty_succAbs {E : VEnv} {U : Nat} {u : VLevel} :
    E.HasType U [recTyU u, natTy, sTy, zTy, mTy u]
      (.app (.app (.bvar 2) (.bvar 1))
        (.app (.app (.app (.app (.bvar 0) (.bvar 4)) (.bvar 3)) (.bvar 2)) (.bvar 1)))
      (.app (.bvar 4) (.app (.const ``Nat.succ []) (.bvar 1))) :=
  have h1 := VEnv.IsDefEq.appDF (VEnv.IsDefEq.bvar (Γ := [recTyU u, natTy, sTy, zTy, mTy u]) .zero)
    (VEnv.IsDefEq.bvar (Γ := [recTyU u, natTy, sTy, zTy, mTy u])
      (.succ (.succ (.succ (.succ .zero)))))
  have h2 := VEnv.IsDefEq.appDF h1
    (VEnv.IsDefEq.bvar (Γ := [recTyU u, natTy, sTy, zTy, mTy u]) (.succ (.succ (.succ .zero))))
  have h3 := VEnv.IsDefEq.appDF h2
    (VEnv.IsDefEq.bvar (Γ := [recTyU u, natTy, sTy, zTy, mTy u]) (.succ (.succ .zero)))
  have h4 := VEnv.IsDefEq.appDF h3
    (VEnv.IsDefEq.bvar (Γ := [recTyU u, natTy, sTy, zTy, mTy u]) (.succ .zero))
  have h5 := VEnv.IsDefEq.appDF
    (VEnv.IsDefEq.bvar (Γ := [recTyU u, natTy, sTy, zTy, mTy u]) (.succ (.succ .zero)))
    (VEnv.IsDefEq.bvar (Γ := [recTyU u, natTy, sTy, zTy, mTy u]) (.succ .zero))
  VEnv.IsDefEq.appDF h5 h4

/-! ## Opening a λ-telescope of a defeq (generic)

`lam_open`: from `Γ ⊢ λA.e₁ ≡ λA.e₂ : ΠA.B` and the typings of the two bodies, the open
equation `A :: Γ ⊢ e₁ ≡ e₂ : B`: weaken by one, apply both sides to `bvar 0` (`appDF`), and
β-reduce each side (`beta`, `inst_liftN_bvar`). `lam_open_tel` iterates it over a telescope;
`lamDF_tel` closes an open typing up (`lamDF`). No inversion is used. -/

theorem lam_open {E : VEnv} (henv : E.Ordered) {U : Nat} {Γ : List VExpr} {A e1 e2 B : VExpr}
    (H : E.IsDefEq U Γ (.lam A e1) (.lam A e2) (.forallE A B))
    (h1 : E.HasType U (A :: Γ) e1 B) (h2 : E.HasType U (A :: Γ) e2 B) :
    E.IsDefEq U (A :: Γ) e1 e2 B := by
  have hb : E.HasType U (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have H' : E.IsDefEq U (A :: Γ) (.lam A.lift (e1.liftN 1 1)) (.lam A.lift (e2.liftN 1 1))
      (.forallE A.lift (B.liftN 1 1)) := H.weak henv
  have W : Ctx.LiftN 1 1 (A :: Γ) (A.lift :: A :: Γ) := .succ (.zero [A])
  have b1 := VEnv.IsDefEq.beta (h1.weakN henv W) hb
  have b2 := VEnv.IsDefEq.beta (h2.weakN henv W) hb
  have H2 := VEnv.IsDefEq.trans (.symm b1) (.trans (.appDF H' hb) b2)
  have k1 : (e1.liftN 1 1).inst (.bvar 0) = e1 := VExpr.inst_liftN_bvar e1 0
  have k2 : (e2.liftN 1 1).inst (.bvar 0) = e2 := VExpr.inst_liftN_bvar e2 0
  have kB : (B.liftN 1 1).inst (.bvar 0) = B := VExpr.inst_liftN_bvar B 0
  rwa [k1, k2, kB] at H2

theorem lamDF_tel {E : VEnv} {U : Nat} : ∀ (Δ : List VExpr) {Γ : List VExpr} {e T : VExpr},
    OnCtx (Δ.reverse ++ Γ) (E.IsType U) → E.HasType U (Δ.reverse ++ Γ) e T →
    E.HasType U Γ (Δ.foldr .lam e) (Δ.foldr .forallE T)
  | [], _, _, _, _, h => h
  | A :: Δ, Γ, e, T, hc, h => by
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hc h
    have ih := lamDF_tel Δ hc h
    have suff : ∀ Θ : List VExpr, OnCtx (Θ ++ A :: Γ) (E.IsType U) → OnCtx (A :: Γ) (E.IsType U) := by
      intro Θ hΘ
      induction Θ with
      | nil => exact hΘ
      | cons _ Θ ihΘ => exact ihΘ hΘ.1
    obtain ⟨-, _, hA⟩ := suff _ hc
    exact .lamDF hA ih

theorem lam_open_tel {E : VEnv} (henv : E.Ordered) {U : Nat} :
    ∀ (Δ : List VExpr) {Γ : List VExpr} {L R T : VExpr},
    OnCtx (Δ.reverse ++ Γ) (E.IsType U) →
    E.HasType U (Δ.reverse ++ Γ) L T → E.HasType U (Δ.reverse ++ Γ) R T →
    E.IsDefEq U Γ (Δ.foldr .lam L) (Δ.foldr .lam R) (Δ.foldr .forallE T) →
    E.IsDefEq U (Δ.reverse ++ Γ) L R T
  | [], _, _, _, _, _, _, _, H => H
  | A :: Δ, Γ, L, R, T, hc, hL, hR, H => by
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hc hL hR ⊢
    exact lam_open_tel henv Δ hc hL hR (lam_open henv H (lamDF_tel Δ hc hL) (lamDF_tel Δ hc hR))

/-! ## `envA` is `Ordered` (the λ-wrapped rules typed, closing NatParams' two sorries) -/

theorem natCI_wf : natCI.WF ∅ := ⟨_, .sortDF trivial trivial rfl⟩
theorem zeroCI_wf : zeroCI.WF env1 := ⟨_, ty_nat rfl []⟩
theorem succCI_wf : succCI.WF env2 := ⟨_, .forallEDF (ty_nat rfl []) (ty_nat rfl _)⟩
/-- `Nat.succ`'s type needs `Nat` only: typed in `env1` (its rank prefix, `succ` has rank 1). -/
theorem succCI_wf1 : succCI.WF env1 := ⟨_, .forallEDF (ty_nat rfl []) (ty_nat rfl _)⟩
theorem recCI_wf : recCI.WF env3 := ty_recTy (u := .param 0) (by decide) rfl rfl rfl []

theorem env1_ordered : env1.Ordered := .const (n := ``Nat) .empty natCI_wf rfl
theorem env3_ordered : env3.Ordered :=
  .const (n := ``Nat.succ) (.const (n := ``Nat.zero) env1_ordered zeroCI_wf rfl) succCI_wf rfl
theorem envC_ordered : envC.Ordered := .const (n := ``Nat.rec) env3_ordered recCI_wf rfl

/-- `iotaSuccLam` typed in `envC`: both sides are `lamDF`×4 over the open typings. -/
theorem iotaSuccLam_wf : iotaSuccLam.WF envC :=
  have hc := ctx_succ (E := envC) (U := 1) (u := .param 0) (by decide) rfl rfl rfl
  ⟨lamDF_tel [mTy (.param 0), zTy, sTy, natTy] (Γ := []) hc (ty_succL (by decide) rfl rfl),
   lamDF_tel [mTy (.param 0), zTy, sTy, natTy] (Γ := []) hc (ty_succR (by decide) rfl)⟩

/-- `iotaZeroLam` typed in `envC + iotaSuccLam`: `lamDF`×3 over the open typings. -/
theorem iotaZeroLam_wf : iotaZeroLam.WF (envC.addDefEq iotaSuccLam) :=
  have hc := ctx_zero (E := envC.addDefEq iotaSuccLam) (U := 1) (u := .param 0) (by decide) rfl rfl rfl
  ⟨lamDF_tel [mTy (.param 0), zTy, sTy] (Γ := []) hc (ty_zeroL (by decide) rfl rfl),
   lamDF_tel [mTy (.param 0), zTy, sTy] (Γ := []) hc ty_zeroR⟩

theorem envA_ordered : envA.Ordered := .defeq (.defeq envC_ordered iotaSuccLam_wf) iotaZeroLam_wf

/-! ## The open typed equations of the two rules in `envA` (at any level `u`)

Derived from the rule itself (`extra` at `ls = [u]`, in context `[]`) by `lam_open_tel`: 3
binders stripped for the zero rule, 4 for the succ rule. These are `pat_defeq` (at
`u = .param 0`, `U = 1`) and the open-equation conjunct of `extra_patV` (at closed `u`, `U = 0`). -/

theorem open_zero {U : Nat} {u : VLevel} (hu : u.WF U) :
    envA.IsDefEq U [sTy, zTy, mTy u]
      (recAppU u (.bvar 2) (.bvar 1) (.bvar 0) (.const ``Nat.zero [])) (.bvar 1)
      (.app (.bvar 2) (.const ``Nat.zero [])) :=
  lam_open_tel envA_ordered [mTy u, zTy, sTy] (Γ := []) (ctx_zero hu rfl rfl rfl)
    (ty_zeroL hu rfl rfl) ty_zeroR
    (VEnv.IsDefEq.extra (df := iotaZeroLam) (ls := [u]) (.inl rfl) (by simpa using hu) rfl)

theorem open_succ {U : Nat} {u : VLevel} (hu : u.WF U) :
    envA.IsDefEq U [natTy, sTy, zTy, mTy u]
      (recAppU u (.bvar 3) (.bvar 2) (.bvar 1) (.app (.const ``Nat.succ []) (.bvar 0)))
      (.app (.app (.bvar 1) (.bvar 0)) (recAppU u (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)))
      (.app (.bvar 3) (.app (.const ``Nat.succ []) (.bvar 0))) :=
  lam_open_tel envA_ordered [mTy u, zTy, sTy, natTy] (Γ := []) (ctx_succ hu rfl rfl rfl)
    (ty_succL hu rfl rfl) (ty_succR hu rfl)
    (VEnv.IsDefEq.extra (df := iotaSuccLam) (ls := [u]) (.inr (.inl rfl)) (by simpa using hu) rfl)

/-! ## Constants and rank prefixes of `envA` -/

theorem envA_constants (c : Name) : envA.constants c =
    if ``Nat.rec = c then some recCI else if ``Nat.succ = c then some succCI else
    if ``Nat.zero = c then some zeroCI else if ``Nat = c then some natCI else none := rfl
theorem env3_constants (c : Name) : env3.constants c =
    if ``Nat.succ = c then some succCI else
    if ``Nat.zero = c then some zeroCI else if ``Nat = c then some natCI else none := rfl
theorem env1_constants (c : Name) : env1.constants c =
    if ``Nat = c then some natCI else none := rfl

theorem envA_defeqs {df : VDefEq} (h : envA.defeqs df) : df = iotaZeroLam ∨ df = iotaSuccLam := by
  rcases h with h | h | h
  · exact .inl h
  · exact .inr h
  · exact (h : False).elim

theorem constants_cases {c : Name} {ci : VConstant} (h : envA.constants c = some ci) :
    (c = ``Nat ∧ ci = natCI) ∨ (c = ``Nat.zero ∧ ci = zeroCI) ∨
    (c = ``Nat.succ ∧ ci = succCI) ∨ (c = ``Nat.rec ∧ ci = recCI) := by
  rw [envA_constants] at h
  by_cases h1 : ``Nat.rec = c
  · rw [if_pos h1] at h; cases h; exact .inr (.inr (.inr ⟨h1.symm, rfl⟩))
  rw [if_neg h1] at h
  by_cases h2 : ``Nat.succ = c
  · rw [if_pos h2] at h; cases h; exact .inr (.inr (.inl ⟨h2.symm, rfl⟩))
  rw [if_neg h2] at h
  by_cases h3 : ``Nat.zero = c
  · rw [if_pos h3] at h; cases h; exact .inr (.inl ⟨h3.symm, rfl⟩)
  rw [if_neg h3] at h
  by_cases h4 : ``Nat = c
  · rw [if_pos h4] at h; cases h; exact .inl ⟨h4.symm, rfl⟩
  rw [if_neg h4] at h; cases h

theorem rank_le_two (c : Name) : rank c ≤ 2 := by
  unfold rank; repeat' split
  all_goals omega

theorem onConsts_of_three {k : Nat} (hk : 3 ≤ k) : ∀ e : VExpr, e.OnConsts (rank · < k)
  | .bvar _ | .sort _ => trivial
  | .const c _ => by show rank c < k; have := rank_le_two c; omega
  | .app f a | .lam f a | .forallE f a => ⟨onConsts_of_three hk f, onConsts_of_three hk a⟩

/-- Both rules mention `Nat.rec` (rank 2), so neither is in a prefix `below k` with `k ≤ 2`. -/
theorem rules_not_below {k : Nat} (hk : k ≤ 2) {df : VDefEq} (h : envA.defeqs df) :
    ¬ df.OnConsts (rank · < k) := by
  rintro ⟨h1, -⟩
  rcases envA_defeqs h with rfl | rfl
  · have : rank ``Nat.rec < k := h1.2.2.2.1.1.1.1
    exact absurd this (by show ¬ 2 < k; omega)
  · have : rank ``Nat.rec < k := h1.2.2.2.2.1.1.1.1
    exact absurd this (by show ¬ 2 < k; omega)

theorem below_zero : envA.below rank 0 = ∅ := by
  apply VEnv.ext
  · funext c; simp only [VEnv.below, Nat.not_lt_zero, ↓reduceIte]; rfl
  · funext df; apply propext
    exact ⟨fun ⟨h1, h2⟩ => absurd h2 (rules_not_below (by omega) h1), fun h => (h : False).elim⟩

theorem below_one : envA.below rank 1 = env1 := by
  apply VEnv.ext
  · funext c
    by_cases hN : c = ``Nat; · subst hN; rfl
    by_cases hZ : c = ``Nat.zero; · subst hZ; rfl
    by_cases hS : c = ``Nat.succ; · subst hS; rfl
    by_cases hR : c = ``Nat.rec; · subst hR; rfl
    simp [VEnv.below, envA_constants, env1_constants, rank, hN, hZ, hS, Ne.symm hN]
  · funext df; apply propext
    exact ⟨fun ⟨h1, h2⟩ => absurd h2 (rules_not_below (by omega) h1), fun h => (h : False).elim⟩

theorem below_two : envA.below rank 2 = env3 := by
  apply VEnv.ext
  · funext c
    by_cases hN : c = ``Nat; · subst hN; rfl
    by_cases hZ : c = ``Nat.zero; · subst hZ; rfl
    by_cases hS : c = ``Nat.succ; · subst hS; rfl
    by_cases hR : c = ``Nat.rec; · subst hR; rfl
    simp [VEnv.below, envA_constants, env3_constants, rank, hN, hZ, hS, Ne.symm hN,
      Ne.symm hZ, Ne.symm hS]
  · funext df; apply propext
    exact ⟨fun ⟨h1, h2⟩ => absurd h2 (rules_not_below (by omega) h1), fun h => (h : False).elim⟩

theorem below_of_three {k : Nat} (hk : 3 ≤ k) : envA.below rank k = envA := by
  apply VEnv.ext
  · funext c
    simp only [VEnv.below]
    rw [if_pos (by have := rank_le_two c; omega)]
  · funext df; apply propext
    exact ⟨And.left, fun h => ⟨h, onConsts_of_three hk _, onConsts_of_three hk _,
      onConsts_of_three hk _⟩⟩

/-! ## The fields -/

/-- `rank_ordered`: the prefixes are `∅`, `env1`, `env3`, `envA` (extensionally). -/
theorem rank_ordered_nat : ∀ k, (envA.below rank k).Ordered
  | 0 => below_zero ▸ .empty
  | 1 => below_one ▸ env1_ordered
  | 2 => below_two ▸ env3_ordered
  | k+3 => by rw [below_of_three (by omega : 3 ≤ k + 3)]; exact envA_ordered

theorem type_below_nat {c : Name} {ci : VConstant} (h : envA.constants c = some ci) :
    (envA.below rank (rank c)).IsType ci.uvars [] ci.type := by
  rcases constants_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show (envA.below rank 0).IsType 0 [] natCI.type
    rw [below_zero]; exact natCI_wf
  · show (envA.below rank 1).IsType 0 [] zeroCI.type
    rw [below_one]; exact zeroCI_wf
  · show (envA.below rank 1).IsType 0 [] succCI.type
    rw [below_one]; exact succCI_wf1
  · show (envA.below rank 2).IsType 1 [] recCI.type
    rw [below_two]; exact recCI_wf

theorem pat_rank_nat {p : Pattern} {r : p.RHS × p.Check} {c' : Name} {us : List VLevel}
    (hP : Pat p r) (_ : VExpr.const c' us ∈ r.1.fixedLeaves) : rank c' ≤ rank p.head := by
  cases hP <;> exact rank_le_two c'

theorem pat_gen_nat {p : Pattern} {r : p.RHS × p.Check} (hP : Pat p r) :
    (Pattern.gen envA rank classify p r.1).isSome := by
  cases hP <;> rfl

theorem pat_typed_nat {p : Pattern} {r : p.RHS × p.Check} {g : PatGen} {ci : VConstant}
    (hP : Pat p r) (hg : Pattern.gen envA rank classify p r.1 = some g)
    (h1 : envA.constants p.head = some ci) :
    OnCtx (g.self ++ g.ctx) (fun Γ A => (envA.below rank (rank p.head)).IsType ci.uvars Γ A) ∧
    (envA.below rank (rank p.head)).HasType ci.uvars (g.self ++ g.ctx) g.rhsAbs
      (g.type.liftN g.self.length) := by
  cases hP
  · obtain rfl : gZero = g := Option.some.inj (gen_zero.symm.trans hg)
    obtain rfl : recCI = ci :=
      Option.some.inj ((show envA.constants ``Nat.rec = some recCI from rfl).symm.trans h1)
    -- `rank Nat.rec = 2`, and `envA.below rank 2 = env3`
    show OnCtx [sTy, zTy, motiveTy] (fun Γ A => (envA.below rank 2).IsType 1 Γ A) ∧
      (envA.below rank 2).HasType 1 [sTy, zTy, motiveTy] (.bvar 1)
        (.app (.bvar 2) (.const ``Nat.zero []))
    rw [below_two]
    exact ⟨ctx_zero (u := .param 0) (by decide) rfl rfl rfl, ty_zeroR⟩
  · obtain rfl : gSucc = g := Option.some.inj (gen_succ.symm.trans hg)
    obtain rfl : recCI = ci :=
      Option.some.inj ((show envA.constants ``Nat.rec = some recCI from rfl).symm.trans h1)
    -- D5's row: `[self : rec.type, n, s, z, motive] ⊢ s n (self motive z s n) : motive (succ n)`
    -- in `env3` (`rank Nat.rec = 2`, `envA.below rank 2 = env3`)
    show OnCtx [recCI.type, natTy, sTy, zTy, motiveTy] (fun Γ A => (envA.below rank 2).IsType 1 Γ A) ∧
      (envA.below rank 2).HasType 1 [recCI.type, natTy, sTy, zTy, motiveTy]
        (.app (.app (.bvar 2) (.bvar 1))
          (.app (.app (.app (.app (.bvar 0) (.bvar 4)) (.bvar 3)) (.bvar 2)) (.bvar 1)))
        (.app (.bvar 4) (.app (.const ``Nat.succ []) (.bvar 1)))
    rw [below_two]
    exact ⟨⟨ctx_succ (u := .param 0) (by decide) rfl rfl rfl,
      ty_recTy (u := .param 0) (by decide) rfl rfl rfl _⟩, ty_succAbs⟩

theorem pat_defeq_nat {p : Pattern} {r : p.RHS × p.Check} {g : PatGen} {ci : VConstant}
    (hP : Pat p r) (hg : Pattern.gen envA rank classify p r.1 = some g)
    (h1 : envA.constants p.head = some ci) :
    envA.IsDefEq ci.uvars g.ctx g.lhs g.rhs g.type := by
  cases hP
  · obtain rfl : gZero = g := Option.some.inj (gen_zero.symm.trans hg)
    obtain rfl : recCI = ci :=
      Option.some.inj ((show envA.constants ``Nat.rec = some recCI from rfl).symm.trans h1)
    exact open_zero (u := .param 0) (by decide)
  · obtain rfl : gSucc = g := Option.some.inj (gen_succ.symm.trans hg)
    obtain rfl : recCI = ci :=
      Option.some.inj ((show envA.constants ``Nat.rec = some recCI from rfl).symm.trans h1)
    exact open_succ (u := .param 0) (by decide)

/-- D5's λ-`extra_patV` for `envA` (`univs = 0`): strip 3 binders (zero rule), 4 (succ rule). -/
theorem extra_patV_nat {df : VDefEq} {ls : List VLevel} {Γ : List VExpr} :
    envA.defeqs df → (∀ l ∈ ls, l.WF 0) → ls.length = df.uvars →
    ∃ (Δ : List VExpr) (L R T : VExpr),
      df.lhs.instL ls = Δ.foldr .lam L ∧ df.rhs.instL ls = Δ.foldr .lam R ∧
      df.type.instL ls = Δ.foldr .forallE T ∧
      OnCtx Δ.reverse (envA.IsType 0) ∧
      envA.IsDefEq 0 Δ.reverse L R T ∧
      ∃ p r m1 m2, Pat p r ∧ p.Matches L m1 m2 ∧
        r.2.OK (envA.IsDefEqU 0 (Δ.reverse ++ Γ)) m1 m2 ∧ R = r.1.apply m1 m2 := by
  intro hdf hls hlen
  rcases envA_defeqs hdf with rfl | rfl
  · obtain ⟨u, rfl⟩ := List.length_eq_one_iff.1 hlen
    have hu : u.WF 0 := hls u (.head _)
    obtain ⟨m2, hm, hr⟩ := zero_instance u (.bvar 2) (.bvar 1) (.bvar 0)
    exact ⟨[mTy u, zTy, sTy], recAppU u (.bvar 2) (.bvar 1) (.bvar 0) (.const ``Nat.zero []),
      .bvar 1, .app (.bvar 2) (.const ``Nat.zero []), rfl, rfl, rfl, ctx_zero hu rfl rfl rfl,
      open_zero hu, zeroPat, (zeroRHS, .true), [u], m2, .zero, hm, trivial, hr.symm⟩
  · obtain ⟨u, rfl⟩ := List.length_eq_one_iff.1 hlen
    have hu : u.WF 0 := hls u (.head _)
    obtain ⟨m2, hm, hr⟩ := succ_instance u (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)
    exact ⟨[mTy u, zTy, sTy, natTy],
      recAppU u (.bvar 3) (.bvar 2) (.bvar 1) (.app (.const ``Nat.succ []) (.bvar 0)),
      .app (.app (.bvar 1) (.bvar 0)) (recAppU u (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)),
      .app (.bvar 3) (.app (.const ``Nat.succ []) (.bvar 0)), rfl, rfl, rfl,
      ctx_succ hu rfl rfl rfl, open_succ hu, succPat, (succRHS, .true), [u], m2, .succ, hm,
      trivial, hr.symm⟩

/-! ### `pat_uniq` (copied from NatParams.lean: finite check over the subpatterns) -/
section PatUniq
deriving instance DecidableEq for Pattern

def subs : Pattern → List Pattern
  | .const c => [.const c]
  | .app f a => .app f a :: (subs f ++ subs a)
  | .var f => .var f :: subs f

theorem mem_subs {p q : Pattern} : Subpattern p q → p ∈ subs q
  | .refl => by cases p <;> simp [subs]
  | .appL h => by simp [subs, mem_subs h]
  | .appR h => by simp [subs, mem_subs h]
  | .varL h => by simp [subs, mem_subs h]

theorem inter_ne_some {p q r : Pattern} (h : (p.inter q).isNone = true) : p.inter q ≠ some r := by
  intro e; rw [e] at h; cases h

theorem pat_uniq_nat : Pat p₁ r → Pat p₂ r' → Subpattern p₃ p₁ → p₂.inter p₃ = some p₄ →
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r' := by
  intro h1 h2 h3 h4
  have h3 := mem_subs h3
  cases h1 <;> cases h2 <;>
    simp only [zeroPat, succPat, SimplePattern.toPattern, Pattern.varN, subs,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at h3 <;>
    rcases h3 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact ⟨rfl, rfl, HEq.rfl⟩
    | exact absurd h4 (inter_ne_some (by decide))
end PatUniq

/-- `ctor_sort` for `ℕ` over `envA`: every derivable sort of `Nat` (resp. `Nat → Nat`) is
non-zero. -/
theorem ctor_sort_nat {c : Name} {cl : Classification} {ci : VConstant} {U : Nat}
    {vs : List VLevel} {u : VLevel} :
    (cl matches .ctor .. | .etaCtor ..) → classify c = some cl → envA.constants c = some ci →
    (∀ l ∈ vs, l.WF U) → vs.length = ci.uvars →
    envA.HasType U [] (ci.type.instL vs) (.sort u) → ∀ ns, u.eval ns ≠ 0 :=
  sorry -- SORRY(E4): blocked, as in NatParams.lean: needs `IsDefEq.uniq` + `IsDefEqU.sort_inv`
        -- (Injectivity.lean, itself `sorry`) to get `u ≈ succ zero` from
        -- `envA.HasType U [] Nat (sort u)`; then `eval ≠ 0` is `rfl`.

theorem ctor_syn_nat {c : Name} {cl : Classification} {ci : VConstant} :
    (cl matches .ctor .. | .etaCtor ..) → classify c = some cl → envA.constants c = some ci →
    ∃ (I : Name) (Ts args : List VExpr),
      Ts.length = cl.arity ∧ classify I = some (.indTy args.length) ∧
      ci.type = Ts.foldr .forallE
        (args.foldr (fun A acc => acc.app A) (.const I (VLevel.params ci.uvars))) := by
  intro hctor hcl hci
  rcases classify_cases hcl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact nomatch hctor
  · cases Option.some.inj hci; exact ⟨``Nat, [], [], rfl, rfl, rfl⟩
  · cases Option.some.inj hci; exact ⟨``Nat, [natTy], [], rfl, rfl, rfl⟩
  · exact nomatch hctor

theorem indTy_closed_nat {I : Name} {k : Nat} {ci : VConstant} :
    classify I = some (.indTy k) → envA.constants I = some ci →
    k = 0 ∧ ∃ u, ci.type = .sort u := by
  intro hI hci
  rcases classify_cases hI with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> cases h
  cases Option.some.inj hci
  exact ⟨rfl, _, rfl⟩

theorem ctor_fields_closed_nat {c : Name} {cl : Classification} {ci : VConstant} :
    (cl matches .ctor .. | .etaCtor ..) → classify c = some cl →
    envA.constants c = some ci →
    ∃ (I : Name) (Ts : List VExpr), ci.type = Ts.foldr .forallE (.const I (VLevel.params ci.uvars)) ∧
      ∀ T ∈ Ts, ∃ I' us, T = .const I' us ∧ classify I' = some (.indTy 0) := by
  intro hctor hcl hci
  rcases classify_cases hcl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact nomatch hctor
  · cases Option.some.inj hci; exact ⟨``Nat, [], rfl, nofun⟩
  · cases Option.some.inj hci
    refine ⟨``Nat, [natTy], rfl, fun T hT => ?_⟩
    rw [List.mem_singleton] at hT; subst hT
    exact ⟨``Nat, [], rfl, rfl⟩
  · exact nomatch hctor

/-! ## The instance -/

/-- `ℕ` over `envA` (the four constants and both λ-wrapped iota rules), `Pat` = the two iota
patterns, ranks Nat 0, zero 1, succ 1, rec 2. -/
def natParamsR : ParamsR where
  env := envA
  henv := envA_ordered
  univs := 0
  Pat := Pat
  classify := classify
  pat_simple := fun h => by cases h <;> exact ⟨_, rfl⟩
  pat_wf := fun h => by cases h <;> exact ⟨rfl, rfl⟩
  pat_uniq := pat_uniq_nat
  extra_patV := extra_patV_nat
  ctor_syn := ctor_syn_nat
  ctor_sort := ctor_sort_nat
  rank := rank
  rank_ordered := rank_ordered_nat
  type_below := type_below_nat
  pat_rank := pat_rank_nat
  pat_gen := pat_gen_nat
  pat_typed := pat_typed_nat
  pat_defeq := pat_defeq_nat
  pat_check := fun h => by cases h <;> rfl
  indTy_closed := indTy_closed_nat
  ctor_fields_closed := ctor_fields_closed_nat

end NatEnvA
end Lean4Lean
