import Lean4Lean.Experimental.ShapeLogRelAdequacy
-- historical: typechecked at 3c35f59, before IsDefEqStrong was indexed by an environment (docs/const-case/PLAN.md D4, landed by R4); no longer compiles.
/-! Lens 3 experiment: the measure for the `const` case of `LR.adequacy`.
Part A: rank / env prefix / proposed Params fields.  Part B: env-indexed strong judgment.
Part C: `EnvStrongR` (rank-bounded typing of constant types and rule leaves).
Part D: the `adequacy_rank` skeleton with the local induction on `hM`.
Part E: the pat-leaf reduction chain (major → extra) and the RHS-instance-as-substitution lemma.
Deliberate sorries are marked `-- SORRY(design)`. -/
namespace Lean4Lean

/-! ## Part A -/

/-- Every constant occurring in `e` satisfies `P`. -/
def VExpr.OnConsts (P : Name → Prop) : VExpr → Prop
  | .bvar _ | .sort _ => True
  | .const c _ => P c
  | .app f a | .lam f a | .forallE f a => f.OnConsts P ∧ a.OnConsts P

def VDefEq.OnConsts (P : Name → Prop) (df : VDefEq) : Prop :=
  df.lhs.OnConsts P ∧ df.rhs.OnConsts P ∧ df.type.OnConsts P

theorem VExpr.OnConsts.mono {P Q : Name → Prop} (h : ∀ c, P c → Q c) :
    ∀ {e : VExpr}, e.OnConsts P → e.OnConsts Q
  | .bvar _, _ | .sort _, _ => trivial
  | .const _ _, hc => h _ hc
  | .app .., ⟨h1, h2⟩ | .lam .., ⟨h1, h2⟩ | .forallE .., ⟨h1, h2⟩ => ⟨h1.mono h, h2.mono h⟩

/-- `1 + max rank` of the constants of `e`; a bound witnessing finiteness. -/
def VExpr.rankBound (rank : Name → Nat) : VExpr → Nat
  | .bvar _ | .sort _ => 0
  | .const c _ => rank c + 1
  | .app f a | .lam f a | .forallE f a => max (f.rankBound rank) (a.rankBound rank)

theorem VExpr.onConsts_rankBound (rank : Name → Nat) :
    ∀ e : VExpr, e.OnConsts (rank · < e.rankBound rank)
  | .bvar _ | .sort _ => trivial
  | .const _ _ => Nat.lt_succ_self _
  | .app f a | .lam f a | .forallE f a =>
    ⟨(onConsts_rankBound rank f).mono fun _ h => Nat.lt_of_lt_of_le h (Nat.le_max_left ..),
     (onConsts_rankBound rank a).mono fun _ h => Nat.lt_of_lt_of_le h (Nat.le_max_right ..)⟩

/-- The environment prefix of rank `< k`: constants of rank `< k`, and the rules all of whose
constants have rank `< k`. For Lean's kernel with `rank` = declaration index this is literally
the environment after the first `k` declarations. -/
def VEnv.below (env : VEnv) (rank : Name → Nat) (k : Nat) : VEnv where
  constants c := if rank c < k then env.constants c else none
  defeqs df := env.defeqs df ∧ df.OnConsts (rank · < k)

theorem VEnv.below_le (env : VEnv) (rank : Name → Nat) (k : Nat) : env.below rank k ≤ env := by
  refine ⟨fun h => ?_, fun h => h.1⟩
  simp only [below] at h; split at h <;> simp_all

theorem VExpr.OnConsts.mono_k {rank : Name → Nat} {k k'} (h : k ≤ k') {e : VExpr}
    (he : e.OnConsts (rank · < k)) : e.OnConsts (rank · < k') :=
  he.mono fun _ h2 => Nat.lt_of_lt_of_le h2 h

theorem VEnv.below_mono (env : VEnv) (rank : Name → Nat) {k k' : Nat} (h : k ≤ k') :
    env.below rank k ≤ env.below rank k' := by
  refine ⟨fun h1 => ?_, fun h1 => ⟨h1.1, h1.2.1.mono_k h, h1.2.2.1.mono_k h, h1.2.2.2.mono_k h⟩⟩
  simp only [below] at h1 ⊢; split at h1
  · rw [if_pos (by omega)]; exact h1
  · cases h1

theorem VEnv.below_constants_lt {env : VEnv} {rank : Name → Nat} {k c ci}
    (h : (env.below rank k).constants c = some ci) : rank c < k := by
  simp only [below] at h; split at h <;> simp_all

-- `Pattern.head` now lives in SExpr.lean (identical definition).

def Pattern.RHS.fixedLeaves {p : Pattern} : p.RHS → List VExpr
  | .fixed e _ => [e]
  | .var _ => []
  | .app f a => f.fixedLeaves ++ a.fixedLeaves

/-- The RHS as an open term over a *pattern context*: `.var path ↦ bvar (idx path)`, a closed
leaf `e` with `self e = some i` (a same-block constant occurrence) `↦ bvar i`, other leaves stay. -/
def Pattern.RHS.toVExpr {p : Pattern} (idx : p.Path → Nat) (self : VExpr → Option Nat) :
    p.RHS → VExpr
  | .fixed e _ => match self e with | some i => .bvar i | none => e
  | .var path => .bvar (idx path)
  | .app f a => .app (f.toVExpr idx self) (a.toVExpr idx self)

namespace SExpr
variable [Params]

/-- Proposed new `Params` fields (stated here as a separate structure; all VExpr-level). -/
structure RankParams where
  rank : Name → Nat
  /-- Same recursive block (mutual recursors). Only reflexivity/symmetry are used. -/
  Block : Name → Name → Prop
  block_refl : ∀ c, Block c c
  block_symm : ∀ {c c'}, Block c c' → Block c' c
  /-- Every rank prefix is an ordered environment. -/
  rank_ordered : ∀ k, (Params.env.below rank k).Ordered
  /-- The type of `c` is typable before every member of `c`'s block (for a recursor: before all
  the block's recursors, i.e. using only the inductive types and constructors). -/
  type_below : ∀ {c ci c'}, Params.env.constants c = some ci → Block c c' →
    (Params.env.below rank (rank c')).IsType ci.uvars [] ci.type
  /-- A closed leaf of a rule RHS is either a bare same-block constant (handled by the local
  induction on the model derivation) or typable before the block. -/
  leaf_below : ∀ {p : Pattern} {r : p.RHS × p.Check} {e ci}, Params.Pat p r → e ∈ r.1.fixedLeaves →
    Params.env.constants p.head = some ci →
    (∃ c' us, e = .const c' us ∧ Block p.head c') ∨
    (∀ c', Block p.head c' → ∃ T, (Params.env.below rank (rank c')).HasType ci.uvars [] e T)
  /-- No side conditions (excludes K-like rules). -/
  pat_check : ∀ {p : Pattern} {r : p.RHS × p.Check}, Params.Pat p r → r.2 = .true
  /-- The RHS of every rule is typable *generically*, in a pattern context `Γp`, with the
  same-block constant occurrences abstracted as variables, before the block. -/
  pat_typed : ∀ {p : Pattern} {r : p.RHS × p.Check} {ci}, Params.Pat p r → Params.env.constants p.head = some ci →
    ∃ (Γp : List VExpr) (Tp : VExpr) (idx : p.Path → Nat) (self : VExpr → Option Nat),
      (∀ e i, self e = some i → ∃ c' us, e = .const c' us ∧ Block p.head c') ∧
      ∀ c', Block p.head c' →
        OnCtx Γp (fun Γ A => (Params.env.below rank (rank c')).IsType ci.uvars Γ A) ∧
        (Params.env.below rank (rank c')).HasType ci.uvars Γp (r.1.toVExpr idx self) Tp

/-! ## Part B: the strong judgment indexed by an environment -/

section
set_option hygiene false
local notation:65 Γ " ⊢ₑ " e1 " : " A:36 => IsDefEqStrongE Γ e1 e1 A
local notation:65 Γ " ⊢ₑ " e1 " ≡ " e2 " : " A:36 => IsDefEqStrongE Γ e1 e2 A
variable (E : VEnv)
/-- `IsDefEqStrong` with the environment explicit; `IsDefEqStrong = IsDefEqStrongE Params.env`.
In the real refactor this is a new first parameter of `IsDefEqStrong`, not a copy. -/
inductive IsDefEqStrongE : List SExpr → SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ₑ A : .sort u → Γ ⊢ₑ .bvar i : A
  | symm : Γ ⊢ₑ e ≡ e' : A → Γ ⊢ₑ e' ≡ e : A
  | trans : Γ ⊢ₑ A : .sort u → Γ ⊢ₑ e₁ ≡ e₂ : A → Γ ⊢ₑ e₂ ≡ e₃ : A → Γ ⊢ₑ e₁ ≡ e₃ : A
  | trans' : Γ ⊢ₑ A ≡ B : .sort u → Γ ⊢ₑ B ≡ C : .sort v → Γ ⊢ₑ A ≡ C : .sort u
  | sort : Γ ⊢ₑ .sort l : .sort (.succ l)
  | const : E.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ₑ SExpr.mkInst ls ci.type : .sort u →
    (F : ∀ cl, CtorBundle c cl) →
    (∀ cl, Γ ⊢ₑ SExpr.mkInst ls ci.type ≡ (F cl).rhs ls : .sort (F cl).u) →
    Γ ⊢ₑ .const c ls : SExpr.mkInst ls ci.type
  | appDF : Γ ⊢ₑ A : .sort u → A::Γ ⊢ₑ B : .sort v →
    Γ ⊢ₑ f ≡ f' : .forallE A B → Γ ⊢ₑ a ≡ a' : A →
    Γ ⊢ₑ B.inst a ≡ B.inst a' : .sort v →
    Γ ⊢ₑ .app f a ≡ .app f' a' : B.inst a
  | lamDF : Γ ⊢ₑ A ≡ A' : .sort u → A::Γ ⊢ₑ B : .sort v →
    A::Γ ⊢ₑ body ≡ body' : B → A'::Γ ⊢ₑ body ≡ body' : B →
    Γ ⊢ₑ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF : Γ ⊢ₑ A ≡ A' : .sort u →
    A::Γ ⊢ₑ body ≡ body' : .sort v → A'::Γ ⊢ₑ body ≡ body' : .sort v →
    Γ ⊢ₑ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF : Γ ⊢ₑ A ≡ B : .sort u → Γ ⊢ₑ e1 ≡ e2 : A → Γ ⊢ₑ e1 ≡ e2 : B
  | beta : A::Γ ⊢ₑ e : B → Γ ⊢ₑ e' : A →
    Γ ⊢ₑ .app (.lam A e) e' : B.inst e' → Γ ⊢ₑ e.inst e' : B.inst e' →
    Γ ⊢ₑ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta : Γ ⊢ₑ e : .forallE A B → Γ ⊢ₑ .lam A (.app e.lift (.bvar 0)) : .forallE A B →
    Γ ⊢ₑ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel : Γ ⊢ₑ p : .sort .zero → Γ ⊢ₑ h : p → Γ ⊢ₑ h' : p → Γ ⊢ₑ h ≡ h' : p
  | extra : E.defeqs df → ls.length = df.uvars →
    Γ ⊢ₑ .mkInst ls df.lhs : .mkInst ls df.type →
    Γ ⊢ₑ .mkInst ls df.rhs : .mkInst ls df.type →
    Γ ⊢ₑ .mkInst ls df.lhs ≡ .mkInst ls df.rhs : .mkInst ls df.type
end

theorem IsDefEqStrongE.mono {E E' : VEnv} (hle : E ≤ E') {Γ e1 e2 A}
    (H : IsDefEqStrongE E Γ e1 e2 A) : IsDefEqStrongE E' Γ e1 e2 A := by
  induction H with
  | bvar h _ ih => exact .bvar h ih
  | symm _ ih => exact .symm ih
  | trans _ _ _ ih1 ih2 ih3 => exact .trans ih1 ih2 ih3
  | trans' _ _ ih1 ih2 => exact .trans' ih1 ih2
  | sort => exact .sort
  | const h1 h2 _ F _ ih3 ih5 => exact .const (hle.1 h1) h2 ih3 F ih5
  | appDF _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 => exact .appDF ih1 ih2 ih3 ih4 ih5
  | lamDF _ _ _ _ ih1 ih2 ih3 ih4 => exact .lamDF ih1 ih2 ih3 ih4
  | forallEDF _ _ _ ih1 ih2 ih3 => exact .forallEDF ih1 ih2 ih3
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ _ _ ih1 ih2 ih3 ih4 => exact .beta ih1 ih2 ih3 ih4
  | eta _ _ ih1 ih2 => exact .eta ih1 ih2
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 _ _ ih1 ih2 => exact .extra (hle.2 h1) h2 ih1 ih2

theorem IsDefEqStrongE.toStrong {Γ e1 e2 A}
    (H : IsDefEqStrongE Params.env Γ e1 e2 A) : IsDefEqStrong Γ e1 e2 A := by
  induction H with
  | bvar h _ ih => exact .bvar h ih
  | symm _ ih => exact .symm ih
  | trans _ _ _ ih1 ih2 ih3 => exact .trans ih1 ih2 ih3
  | trans' _ _ ih1 ih2 => exact .trans' ih1 ih2
  | sort => exact .sort
  | const h1 h2 _ F _ ih3 ih5 => exact .const h1 h2 ih3 F ih5
  | appDF _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 => exact .appDF ih1 ih2 ih3 ih4 ih5
  | lamDF _ _ _ _ ih1 ih2 ih3 ih4 => exact .lamDF ih1 ih2 ih3 ih4
  | forallEDF _ _ _ ih1 ih2 ih3 => exact .forallEDF ih1 ih2 ih3
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ _ _ ih1 ih2 ih3 ih4 => exact .beta ih1 ih2 ih3 ih4
  | eta _ _ ih1 ih2 => exact .eta ih1 ih2
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 _ _ ih1 ih2 => exact .extra h1 h2 ih1 ih2

theorem IsDefEqStrongE.toStrong' {E : VEnv} (hle : E ≤ Params.env) {Γ e1 e2 A}
    (H : IsDefEqStrongE E Γ e1 e2 A) : IsDefEqStrong Γ e1 e2 A := (H.mono hle).toStrong

/-- Same proof as `IsDefEqStrong.weak0` (via `weak'` + `closedN`), for the `E`-indexed judgment.
In the real refactor this *is* `IsDefEqStrong.weak0`. -/
theorem IsDefEqStrongE.weak0 {E : VEnv} {Γ e1 e2 A}
    (H : IsDefEqStrongE E [] e1 e2 A) : IsDefEqStrongE E Γ e1 e2 A := by
  sorry -- SORRY(mechanical): copy of IsDefEqStrong.weak0

/-- Every strong derivation lives in some rank prefix (take the max over the derivation). -/
theorem IsDefEqStrong.exists_below (rank : Name → Nat) {Γ e1 e2 A}
    (H : IsDefEqStrong Γ e1 e2 A) : ∃ k, IsDefEqStrongE (Params.env.below rank k) Γ e1 e2 A := by
  induction H with
  | bvar h _ ih => let ⟨k, ih⟩ := ih; exact ⟨k, .bvar h ih⟩
  | symm _ ih => let ⟨k, ih⟩ := ih; exact ⟨k, .symm ih⟩
  | trans _ _ _ ih1 ih2 ih3 =>
    obtain ⟨⟨k1, ih1⟩, ⟨k2, ih2⟩, ⟨k3, ih3⟩⟩ := And.intro ih1 (And.intro ih2 ih3)
    refine ⟨max k1 (max k2 k3), .trans (ih1.mono (Params.env.below_mono rank ?_))
      (ih2.mono (Params.env.below_mono rank ?_)) (ih3.mono (Params.env.below_mono rank ?_))⟩ <;> omega
  | trans' _ _ ih1 ih2 =>
    obtain ⟨⟨k1, ih1⟩, ⟨k2, ih2⟩⟩ := And.intro ih1 ih2
    refine ⟨max k1 k2, .trans' (ih1.mono (Params.env.below_mono rank ?_))
      (ih2.mono (Params.env.below_mono rank ?_))⟩ <;> omega
  | sort => exact ⟨0, .sort⟩
  | @const c ci Γ ls u h1 h2 _ F _ ih3 ih5 =>
    -- the ctor-bundle family is indexed by `cl : IsCtor c`, a subsingleton: choose per `cl`
    -- is fine but needs a uniform bound; `IsCtor c` is a Prop so the family has ≤ 1 member.
    obtain ⟨k3, ih3⟩ := ih3
    by_cases hc : CtorBundle.IsCtor c
    · obtain ⟨k5, ih5⟩ := ih5 hc
      refine ⟨max (max k3 k5) (rank c + 1), .const ?_ h2 (ih3.mono (Params.env.below_mono rank ?_)) F
        fun cl => (ih5.mono (Params.env.below_mono rank ?_))⟩
      · simp only [VEnv.below]; rw [if_pos (by omega)]; exact h1
      all_goals omega
    · refine ⟨max k3 (rank c + 1), .const ?_ h2 (ih3.mono (Params.env.below_mono rank ?_)) F
        fun cl => (hc cl).elim⟩
      · simp only [VEnv.below]; rw [if_pos (by omega)]; exact h1
      · omega
  | appDF _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    obtain ⟨⟨k1, ih1⟩, ⟨k2, ih2⟩, ⟨k3, ih3⟩, ⟨k4, ih4⟩, ⟨k5, ih5⟩⟩ :=
      And.intro ih1 (And.intro ih2 (And.intro ih3 (And.intro ih4 ih5)))
    refine ⟨max (max k1 k2) (max k3 (max k4 k5)),
      .appDF (ih1.mono (Params.env.below_mono rank ?_)) (ih2.mono (Params.env.below_mono rank ?_))
        (ih3.mono (Params.env.below_mono rank ?_)) (ih4.mono (Params.env.below_mono rank ?_))
        (ih5.mono (Params.env.below_mono rank ?_))⟩ <;> omega
  | lamDF _ _ _ _ ih1 ih2 ih3 ih4 =>
    obtain ⟨⟨k1, ih1⟩, ⟨k2, ih2⟩, ⟨k3, ih3⟩, ⟨k4, ih4⟩⟩ :=
      And.intro ih1 (And.intro ih2 (And.intro ih3 ih4))
    refine ⟨max (max k1 k2) (max k3 k4),
      .lamDF (ih1.mono (Params.env.below_mono rank ?_)) (ih2.mono (Params.env.below_mono rank ?_))
        (ih3.mono (Params.env.below_mono rank ?_)) (ih4.mono (Params.env.below_mono rank ?_))⟩ <;> omega
  | forallEDF _ _ _ ih1 ih2 ih3 =>
    obtain ⟨⟨k1, ih1⟩, ⟨k2, ih2⟩, ⟨k3, ih3⟩⟩ := And.intro ih1 (And.intro ih2 ih3)
    refine ⟨max k1 (max k2 k3), .forallEDF (ih1.mono (Params.env.below_mono rank ?_))
      (ih2.mono (Params.env.below_mono rank ?_)) (ih3.mono (Params.env.below_mono rank ?_))⟩ <;> omega
  | defeqDF _ _ ih1 ih2 =>
    obtain ⟨⟨k1, ih1⟩, ⟨k2, ih2⟩⟩ := And.intro ih1 ih2
    refine ⟨max k1 k2, .defeqDF (ih1.mono (Params.env.below_mono rank ?_))
      (ih2.mono (Params.env.below_mono rank ?_))⟩ <;> omega
  | beta _ _ _ _ ih1 ih2 ih3 ih4 =>
    obtain ⟨⟨k1, ih1⟩, ⟨k2, ih2⟩, ⟨k3, ih3⟩, ⟨k4, ih4⟩⟩ :=
      And.intro ih1 (And.intro ih2 (And.intro ih3 ih4))
    refine ⟨max (max k1 k2) (max k3 k4),
      .beta (ih1.mono (Params.env.below_mono rank ?_)) (ih2.mono (Params.env.below_mono rank ?_))
        (ih3.mono (Params.env.below_mono rank ?_)) (ih4.mono (Params.env.below_mono rank ?_))⟩ <;> omega
  | eta _ _ ih1 ih2 =>
    obtain ⟨⟨k1, ih1⟩, ⟨k2, ih2⟩⟩ := And.intro ih1 ih2
    refine ⟨max k1 k2, .eta (ih1.mono (Params.env.below_mono rank ?_))
      (ih2.mono (Params.env.below_mono rank ?_))⟩ <;> omega
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    obtain ⟨⟨k1, ih1⟩, ⟨k2, ih2⟩, ⟨k3, ih3⟩⟩ := And.intro ih1 (And.intro ih2 ih3)
    refine ⟨max k1 (max k2 k3), .proofIrrel (ih1.mono (Params.env.below_mono rank ?_))
      (ih2.mono (Params.env.below_mono rank ?_)) (ih3.mono (Params.env.below_mono rank ?_))⟩ <;> omega
  | @extra df ls Γ h1 h2 _ _ ih1 ih2 =>
    obtain ⟨⟨k1, ih1⟩, ⟨k2, ih2⟩⟩ := And.intro ih1 ih2
    let kd := max (df.lhs.rankBound rank) (max (df.rhs.rankBound rank) (df.type.rankBound rank))
    refine ⟨max (max k1 k2) kd, .extra ⟨h1, ?_, ?_, ?_⟩ h2 (ih1.mono (Params.env.below_mono rank ?_))
      (ih2.mono (Params.env.below_mono rank ?_))⟩
    · exact (df.lhs.onConsts_rankBound rank).mono_k (by omega)
    · exact (df.rhs.onConsts_rankBound rank).mono_k (by omega)
    · exact (df.type.onConsts_rankBound rank).mono_k (by omega)
    all_goals omega

/-! ## Part C: rank-bounded strong typing of the environment (replaces new `IsDefEqStrong.const`
premises). Both fields are *direct* applications of `strong ∘ instL ∘ mkS` in the prefix
environment; no rank induction is needed here because the bound sits in the type. -/

structure EnvStrongR (RP : RankParams) : Prop where
  const : ∀ {c ci ls c'}, Params.env.constants c = some ci → ls.length = ci.uvars →
    RP.Block c c' →
    ∃ u, IsDefEqStrongE (Params.env.below RP.rank (RP.rank c')) []
      (mkInst ls ci.type) (mkInst ls ci.type) (.sort u)
  leaf : ∀ {p : Pattern} {r : p.RHS × p.Check} {e ci ls c'}, Params.Pat p r →
    e ∈ r.1.fixedLeaves → Params.env.constants p.head = some ci → ls.length = ci.uvars →
    RP.Block p.head c' → (¬ ∃ c'' us, e = .const c'' us ∧ RP.Block p.head c'') →
    ∃ T, IsDefEqStrongE (Params.env.below RP.rank (RP.rank c')) [] (mkInst ls e) (mkInst ls e) T

/-- The strong-to-strong translation generalised over the source environment `E ≤ env`
(the real `mkS` with `Params.env` replaced by `E`; its `constDF` case uses `E.constants`). -/
def MkSE : Prop :=
  ∀ {E : VEnv} {Γ : List VExpr} {e₁ e₂ A : VExpr}, E ≤ Params.env →
    E.IsDefEqStrong Params.univs Γ e₁ e₂ A → OnCtx Γ (fun _ A => A.LevelWF Params.univs) →
    IsDefEqStrongE E (Γ.map mk) (mk e₁) (mk e₂) (mk A)

theorem EnvStrongR.of_params (RP : RankParams) (mkSE : MkSE) : EnvStrongR RP where
  const := fun {c ci ls c'} h1 _ hB => by
    obtain ⟨vs, hvs, rfl⟩ := SLevel.exists_map_mk ls
    have ⟨u, hu⟩ := RP.type_below h1 hB
    have hS := (VEnv.IsDefEq.strong (RP.rank_ordered _) (by trivial) hu).instL hvs
    have := mkSE (Params.env.below_le ..) hS (by trivial)
    rw [mkInst_map_mk hvs]
    exact ⟨_, this⟩
  leaf := fun {p r e ci ls c'} hP he h1 _ hB hne => by
    obtain ⟨vs, hvs, rfl⟩ := SLevel.exists_map_mk ls
    have ⟨T, hT⟩ := (RP.leaf_below hP he h1).resolve_left hne c' hB
    have hS := (VEnv.IsDefEq.strong (RP.rank_ordered _) (by trivial) hT).instL hvs
    have := mkSE (Params.env.below_le ..) hS (by trivial)
    rw [mkInst_map_mk hvs]
    exact ⟨_, this⟩

/-! ## Part D: the measure.
Outer: well-founded on the rank bound `k`. Middle: structural on `H : IsDefEqStrongE (below k)`.
Inner (const case only): structural on `hM : LE_Interp ρ mT M` with the motive restricted to
same-block constants at shapes below the recorded one. -/

/-- The local induction. `WFIH` is the outer well-founded IH (adequacy at every bound `< k`),
`hk : rank c₀ < k` comes from `(below k).constants c₀ = some _` at the outer `const` node. -/
theorem const_local (RP : RankParams) (envR : EnvStrongR RP) {Γ₀ : List SExpr} {k : Nat}
    (WFIH : ∀ k' < k, ∀ {Γ M N A} (H : IsDefEqStrongE (Params.env.below RP.rank k') Γ M N A)
      {ρ n} {m a : WShape n}, LE_Interp ρ m.T M → LE_Interp ρ a.T A → m.HasType a →
      LR.Adequate Γ₀ Γ ρ M N A m a)
    (hΓ₀ : ⊢ Γ₀) {c₀ : Name} (hk : RP.rank c₀ < k)
    {ρ mT M} (hM : LE_Interp ρ mT M) :
    ∀ c ls ci, M = .const c ls → RP.Block c₀ c → Params.env.constants c = some ci →
      ls.length = ci.uvars →
    ∀ {n} (m a : WShape n), m.T ≤ mT → LE_Interp ρ a.T (mkInst ls ci.type) → m.HasType a →
    (LR Γ₀).DefEq (.const c ls) (.const c ls) (mkInst ls ci.type) m a := by
  induction hM with
  | bot =>
    intro c ls ci _ _ _ _ n m a hle _ hmem
    cases show m = .bot from TShape.le_bot.1 (hle.trans TShape.bot_le')
    exact (LR _).bot hmem.isType
  | const h1 h2 h3 h4 h5 h6 h7 ih5 ih7 =>
    intro c ls ci eM hB h1' hlen n m a hle hA hmem
    cases eM; cases h1.symm.trans h1'
    rename_i _ c ci mT₀ m' ρ aT ls R
    -- (i) type validity of `c`'s type: a WF-IH call at bound `rank c₀ < k`, derivation from `envR`.
    obtain ⟨u, Hty₀⟩ := envR.const h1 hlen (RP.block_symm hB)
    have Hty := Hty₀.weak0 (Γ := Γ₀)
    have hcl := (Params.henv.closedC h1).mkInstS (ls := ls)
    have hA₀ : LE_Interp .nil a.T (mkInst ls ci.type) := (LE_Interp.closed_iff hcl).1 hA
    obtain ⟨n', a', s, le_n, le_a, hA', hS, hmem'⟩ :=
      (LE_Interp.soundS (Hty.toStrong' (Params.env.below_le ..)) .nil).2 hA₀ |>.out
    have tyAd := WFIH _ hk Hty hA' hS hmem'
    have tyDE := (tyAd.2 (LR.SubstWF.id hΓ₀))
    simp only [subst_id] at tyDE
    -- `tyDE : (LR Γ₀).DefEq type type (sort u) a' s`; `TyDefEq type type a` by `LR.toValTy`,
    -- exactly as in the existing cases.
    have tyV : (LR Γ₀).TyDefEq (mkInst ls ci.type) (mkInst ls ci.type) a :=
      LR.toValTy le_n le_a hmem.isType hS hmem' tyDE
    -- (ii) a same-block bare-constant leaf of a rule RHS: the LOCAL IH `ih7` at the nested
    -- premise `h7 m_e e hR`, a strict sub-derivation; no typing derivation is needed.
    have ihBlock : ∀ m_e c'' ls'' ci'' (hR : R m_e (.const c'' ls'')), RP.Block c₀ c'' →
        Params.env.constants c'' = some ci'' → ls''.length = ci''.uvars →
        ∀ {n} (m' a' : WShape n), m'.T ≤ m_e → LE_Interp ρ a'.T (mkInst ls'' ci''.type) →
        m'.HasType a' →
        (LR Γ₀).DefEq (.const c'' ls'') (.const c'' ls'') (mkInst ls'' ci''.type) m' a' :=
      fun m_e c'' ls'' ci'' hR hB' h1'' hlen' n m' a' hle' hA' hmem' =>
        ih7 m_e _ hR c'' ls'' ci'' rfl hB' h1'' hlen' m' a' hle' hA' hmem'
    -- (iii) any other closed leaf `e` of a rule headed by `c`: typing from `envR.leaf` at bound
    -- `rank c₀`, model derivation from `h7` (lowered by `LE_Interp.mono`), WF-IH at `rank c₀ < k`.
    have ihLeaf : ∀ {p : Pattern} {r : p.RHS × p.Check} {e : VExpr}, Params.Pat p r →
        e ∈ r.1.fixedLeaves → p.head = c → (¬ ∃ c'' us, e = .const c'' us ∧ RP.Block c c'') →
        ∀ m_e, R m_e (mkInst ls e) →
        ∃ T, ∀ {n} (m' a' : WShape n), m'.T ≤ m_e → LE_Interp ρ a'.T T → m'.HasType a' →
          (LR Γ₀).DefEq (mkInst ls e) (mkInst ls e) T m' a' := by
      intro p r e hP he hhead hne m_e hR
      subst hhead
      obtain ⟨T, HT₀⟩ := envR.leaf hP he h1 hlen (RP.block_symm hB) hne
      have HT := HT₀.weak0 (Γ := Γ₀)
      refine ⟨T, fun {n} m' a' hle' hA' hmem' => ?_⟩
      -- closedness of the leaf and its type, from the `[]`-derivation
      have hcl := (HT₀.toStrong' (Params.env.below_le ..)).closedN
      have hcl_e : (mkInst ls e).ClosedN := hcl.1
      have hcl_T : T.ClosedN := hcl.2.2
      have hMe : LE_Interp .nil m'.T (mkInst ls e) :=
        (LE_Interp.closed_iff hcl_e).1 ((h7 _ _ hR).mono hle')
      have hAe : LE_Interp .nil a'.T T := (LE_Interp.closed_iff hcl_T).1 hA'
      have := (WFIH _ hk HT hMe hAe hmem').2 (LR.SubstWF.id hΓ₀)
      simpa only [subst_id] using this
    -- (iv) the remaining work is the spine lemma on `h6 : Const c ls R [] m'` and the pat leaf,
    -- which consume `tyV`, `ihBlock`, `ihLeaf` (and the ctor clause). Not this lens.
    clear ih5 ih7
    sorry -- SORRY(design): spine lemma + pat leaf
  | _ => intro c ls ci eM; cases eM

/-- The outer theorem. The 13 non-`const` cases are the existing ones with `.toStrong`/`.mono`
inserted where sub-derivations are used as `⊢ₛ`; only the `const` case is shown. -/
theorem adequacy_rank (RP : RankParams) (envR : EnvStrongR RP) {Γ₀ : List SExpr} :
    ∀ k {Γ M N A} (H : IsDefEqStrongE (Params.env.below RP.rank k) Γ M N A) {ρ n} {m a : WShape n},
      LE_Interp ρ m.T M → LE_Interp ρ a.T A → m.HasType a → LR.Adequate Γ₀ Γ ρ M N A m a := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k WFIH =>
  intro Γ M N A H
  induction H with
  | @const c ci Γ ls u h1 h2 h3 F h5 ih3 ih5 =>
    intro ρ n m a hM hA hmem
    have hrk := VEnv.below_constants_lt h1
    have h1' := (Params.env.below_le ..).1 h1
    refine .refl fun σ σ' W => ?_
    rw [(Params.henv.closedC h1').mkInstS.subst_eq .zero]
    exact const_local RP envR WFIH W.wf₀ hrk hM c ls ci rfl (RP.block_refl c) h1' h2 m a .rfl hA hmem
  | _ => sorry -- SORRY(skeleton): the existing 13 cases

/-- The final theorem is recovered through `exists_below`. -/
theorem adequacy_of_rank (RP : RankParams) (envR : EnvStrongR RP) {Γ₀ : List SExpr}
    (hΓ : ⊢ Γ) (H : Γ ⊢ M ≡ N : A) {ρ n} {m a : WShape n}
    (hM : LE_Interp ρ m.T M) (hA : LE_Interp ρ a.T A) (hmem : m.HasType a) :
    LR.Adequate Γ₀ Γ ρ M N A m a :=
  let ⟨_, H'⟩ := (H.strong hΓ).exists_below RP.rank
  adequacy_rank RP envR _ H' hM hA hmem

/-! ## Part E: the pat leaf, syntactic half.
Shape-level `Matches` ⇒ (ctor clause) the major head-reduces to a syntactic ctor spine ⇒
`WHRedS.major` lifts it under the recursor prefix ⇒ `MatchesS` holds syntactically ⇒
`WHRed.extra` fires with no side conditions (`pat_check`). Everything below is sorry-free. -/

omit [Params] in
theorem _root_.Lean4Lean.Pattern.varN_var (p : Pattern) :
    ∀ n, (Pattern.var p).varN n = (p.varN n).var
  | 0 => rfl
  | n+1 => by simp only [Pattern.varN, varN_var p n]

/-- Left-nested application spine `h x₁ … xₙ`. -/
def apps (h : SExpr) : List SExpr → SExpr
  | [] => h
  | x :: xs => apps (h.app x) xs

/-- A `varN` pattern matches any spine of the right length (the arguments are unconstrained). -/
theorem _root_.Lean4Lean.Pattern.MatchesS.apps {q : Pattern} {h : SExpr} {ls} {g : q.Path → SExpr}
    (H : q.MatchesS h ls g) : ∀ xs : List SExpr,
      ∃ g', (q.varN xs.length).MatchesS (apps h xs) ls g'
  | [] => ⟨g, H⟩
  | x :: xs => by
    have ⟨g', h'⟩ := Pattern.MatchesS.apps (q := q.var) (H.var (a' := x)) xs
    revert g' h'; rw [Pattern.varN_var]
    exact fun g' h' => ⟨g', h'⟩

/-- `extra` when the rule has no side conditions. -/
theorem WHRed.extra_true {p : Pattern} {r : p.RHS × p.Check} {e m1} {m2 : p.Path → SExpr}
    (hP : Params.Pat p r) (hck : r.2 = .true) (hm : p.MatchesS e m1 m2) :
    Γ ⊢ e ⤳ r.1.applyS m1 m2 :=
  WHRed.extra hP hm (dfs := []) (by rw [hck]; rfl) nofun

/-- The reduction half of the pat leaf for an iota rule `rec x₁…xₘ (ctor z₁…zₙ)`: once the major
premise head-reduces to a syntactic constructor spine, the whole spine head-reduces to the RHS
instance. Uses `WHRedS.major` (reduction in major position) and `pat_check`. -/
theorem pat_leaf_reduce {rec ctor : Name} {m n : Nat}
    {r : (Pattern.app (.varN (.const rec) m) (.varN (.const ctor) n)).RHS ×
      (Pattern.app (.varN (.const rec) m) (.varN (.const ctor) n)).Check}
    (hP : Params.Pat (.app (.varN (.const rec) m) (.varN (.const ctor) n)) r) (hck : r.2 = .true)
    {ls ls' : List SLevel} (xs zs : List SExpr) (hxs : xs.length = m) (hzs : zs.length = n)
    {x_maj : SExpr} (hred : Γ ⊢ x_maj ⤳* apps (.const ctor ls') zs) :
    ∃ m2, Γ ⊢ (apps (.const rec ls) xs).app x_maj ⤳* r.1.applyS ls m2 := by
  subst hxs; subst hzs
  obtain ⟨g1, h1⟩ := Pattern.MatchesS.apps (q := .const rec) (.const (ls := ls)) xs
  obtain ⟨g2, h2⟩ := Pattern.MatchesS.apps (q := .const ctor) (.const (ls := ls')) zs
  have hmaj : IsMajorPremise (apps (.const rec ls) xs) := IsMajorPremise.mk hP h1
  exact ⟨_, .tail (WHRedS.major hmaj hred) (WHRed.extra_true hP hck (h1.app h2))⟩

/-- The RHS instance is the generic RHS under the pattern substitution (R2 plumbing): with
`σ (idx path) = m2 path` and `σ i = const c' us` for the abstracted same-block occurrences. -/
theorem _root_.Lean4Lean.Pattern.RHS.toVExpr_subst {p : Pattern} (idx : p.Path → Nat)
    (self : VExpr → Option Nat) (ls : List SLevel) (m2 : p.Path → SExpr) (σ : Subst)
    (hidx : ∀ path, σ (idx path) = m2 path)
    (hself : ∀ e i, self e = some i → σ i = mkInst ls e) :
    ∀ r : p.RHS, (mkInst ls (r.toVExpr idx self)).subst σ = r.applyS ls m2
  | .fixed e cl => by
    simp only [Pattern.RHS.toVExpr, Pattern.RHS.applyS]
    split
    · next i h => simp only [mkInst, SExpr.subst, hself e i h]
    · exact cl.mkInstS.subst_eq .zero
  | .var path => by simp only [Pattern.RHS.toVExpr, Pattern.RHS.applyS, mkInst, SExpr.subst, hidx]
  | .app f a => by
    simp only [Pattern.RHS.toVExpr, Pattern.RHS.applyS, mkInst, SExpr.subst,
      toVExpr_subst idx self ls m2 σ hidx hself f, toVExpr_subst idx self ls m2 σ hidx hself a]

end SExpr
end Lean4Lean
