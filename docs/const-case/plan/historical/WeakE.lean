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

-- Pattern.head now exists at HEAD (SExpr.lean); duplicate removed by the refuter.

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

/-! Audit probe: `weak'`/`closedN`/`weak0` at an arbitrary `E ≤ Params.env`.
The repo's versions (SExpr.lean:1367-1430) are stated with `⊢ₛ` (= `Params.env`) and use
`constType_closed h1` / `defeq_closed h1`, which need membership in `Params.env`; so the
E-indexed versions need the hypothesis `hE`. -/
theorem IsDefEqStrongE.closedN' {E : VEnv} (hE : E ≤ Params.env) {Γ e1 e2 A}
    (H : IsDefEqStrongE E Γ e1 e2 A) :
    ClosedN e1 Γ.length ∧ ClosedN e2 Γ.length ∧ ClosedN A Γ.length :=
  (H.toStrong' hE).closedN

theorem IsDefEqStrongE.weak' {E : VEnv} (hE : E ≤ Params.env) {ρ Γ Γ' e1 e2 A}
    (W : Ctx.Lift' ρ Γ Γ') (H : IsDefEqStrongE E Γ e1 e2 A) :
    IsDefEqStrongE E Γ' (e1.lift' ρ) (e2.lift' ρ) (A.lift' ρ) := by
  induction H generalizing ρ Γ' with
  | bvar h _ ih => exact .bvar (h.weak' W) (ih W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ _ ih1 ih2 ih3 => exact .trans (ih1 W) (ih2 W) (ih3 W)
  | trans' _ _ ih1 ih2 => exact .trans' (ih1 W) (ih2 W)
  | sort => exact .sort
  | @const c ci Γ ls u h1 h2 _ F _ ihT ihF =>
    have eT := (constType_closed (ls := ls) (hE.1 h1)).lift'_eq (ρ := ρ) .zero
    have ihT := ihT W; have ihF := fun cl => ihF cl W
    simp only [eT, lift'_sort] at ihT ihF
    rw [eT]
    refine .const h1 h2 ihT (fun cl => ((F cl).exists_lift' ρ ls).choose) fun cl => ?_
    have ⟨hu, hrhs⟩ := ((F cl).exists_lift' ρ ls).choose_spec
    rw [hu, hrhs]; exact ihF cl
  | appDF _ _ _ _ _ ihA ihB ihf iha ihBi =>
    exact lift'_inst_hi .. ▸ .appDF (ihA W) (ihB W.cons) (ihf W) (iha W)
      (lift'_inst_hi .. ▸ lift'_inst_hi .. ▸ ihBi W)
  | lamDF _ _ _ _ ihA ihB ih1 ih2 => exact .lamDF (ihA W) (ihB W.cons) (ih1 W.cons) (ih2 W.cons)
  | forallEDF _ _ _ ihA ih1 ih2 => exact .forallEDF (ihA W) (ih1 W.cons) (ih2 W.cons)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ _ _ ih1 ih2 ih3 ih4 =>
    rw [lift'_inst_hi, lift'_inst_hi]
    refine .beta (ih1 W.cons) (ih2 W) ?_ ?_
    · rw [← lift'_inst_hi]; exact ih3 W
    · rw [← lift'_inst_hi, ← lift'_inst_hi]; exact ih4 W
  | eta _ _ ih1 ih2 =>
    refine cast ?_ (IsDefEqStrongE.eta (ih1 W) (cast ?_ (ih2 W)))
    all_goals simp [lift', ← lift'_comp]
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | @extra df Γ ls h1 h2 _ _ ih1 ih2 =>
    have ⟨hA1, hA2, hA3⟩ := defeq_closed (ls := ls) (hE.2 h1)
    rw [hA1.lift'_eq .zero, hA2.lift'_eq .zero, hA3.lift'_eq .zero]
    have ih1 := ih1 W; have ih2 := ih2 W
    rw [hA1.lift'_eq .zero, hA3.lift'_eq .zero] at ih1
    rw [hA2.lift'_eq .zero, hA3.lift'_eq .zero] at ih2
    exact .extra h1 h2 ih1 ih2

theorem IsDefEqStrongE.weak0' {E : VEnv} (hE : E ≤ Params.env) {Γ e1 e2 A}
    (H : IsDefEqStrongE E [] e1 e2 A) : IsDefEqStrongE E Γ e1 e2 A := by
  have ⟨h1, h2, h3⟩ := H.closedN' hE
  have := H.weak' hE (Ctx.Lift'.nil Γ)
  rwa [h1.lift'_eq .zero, h2.lift'_eq .zero, h3.lift'_eq .zero] at this

#print axioms IsDefEqStrongE.weak'
#print axioms IsDefEqStrongE.weak0'
