import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Plan amender, round 3: copy of amend-2/PatLeafStmt2.lean (unchanged, lines 1-183 there) plus
the E6a interface: `Valuation.lowerCtx`/`Valuation.lower` (D4 step 1, ρ_low) and the statement of
`LR.rhs_lower` (D4 step 2), appended at the end. Typechecked AS STATEMENTS at /tmp/utt-snap6.
Deliberate sorries: the three theorem bodies (pat_leaf_1a, const_spine, rhs_lower; marked).
Round-2 header follows.
Plan amender, round 2: copy of amend-1/PatLeafStmt.lean with `pat_leaf_1a` taking
`hg : gen Params.env rank Params.classify p r.1 = some g` (audit round 2, #1); `gen` is a variable
standing in for R5's `Pattern.gen`. Typechecked AS STATEMENTS against HEAD 3c35f59 (/tmp/utt-snap6).
Round-1 header follows.
Plan amender, round 1: the E6 interface `LR.pat_leaf_1a` and the amended spine-lemma
statement (`LR.const_spine`), typechecked AS STATEMENTS against HEAD 3c35f59 (/tmp/utt-snap6).
Stand-ins: the repo's `LR` for E1+E2's `T.LR` (D6 keeps every name and signature used here);
`rank` a variable for the R5 field `Params.rank`; `IsDefEqStrongE` for R4's `IsDefEqStrong E`;
`PatGen` and the `pat_typed`/`pat_defeq` conclusions as explicit hypotheses (R5 / E3 drafts).
Copies: Part A/B of /tmp/utt-exp/plan/audit-complete-1/WeakE.lean.
Deliberate sorries: the two theorem bodies (marked). -/
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


structure PatGen where
  ctx : List VExpr
  self : List VExpr
  lhs : VExpr
  rhs : VExpr
  rhsAbs : VExpr
  type : VExpr

namespace SExpr
variable [Params]

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

/-- `const c ls (bvar (k-1)) … (bvar 0)` (docs/const-case/CtorClause.lean:102). -/
def openSpine (c : Name) (ls : List SLevel) (k : Nat) : SExpr :=
  spine (.const c ls) ((List.range k).reverse.map .bvar)

/-- Telescope valuation (docs/const-case/CtorClause.lean:106). -/
def Valuation.ofRargs {n} (rargs : List (WShape n)) : Valuation :=
  rargs.foldr (fun x ρ => ρ.push x.T) .nil

variable (rank : Name → Nat)

/-- The WF IH of `LR.adequacy_rank` at bound `k`. -/
def LR.WFIH (Γ₀ : List SExpr) (k : Nat) : Prop :=
  ∀ k' < k, ∀ {Γ M N A}, IsDefEqStrongE (Params.env.below rank k') Γ M N A →
    ∀ {ρ n} {m a : WShape n}, LE_Interp ρ m.T M → LE_Interp ρ a.T A → m.HasType a →
      LR.Adequate Γ₀ Γ ρ M N A m a

/-- `LR.const_local`'s conclusion (PLAN D4) for `hM : LE_Interp ρ mT (.const c ls)`. -/
def LR.ConstGoal (Γ₀ : List SExpr) (ρ : Valuation) (mT : TShape) (c : Name) (ls : List SLevel)
    (ci : VConstant) : Prop :=
  (∃ n, mT = (WShape.bot (n := n)).T) ∨
  ∃ (n : Nat) (m' a' : WShape n), mT ≤ m'.T ∧ m'.HasType a' ∧ LE_Interp ρ a'.T (mkInst ls ci.type) ∧
    ∀ {n'} (m a : WShape n'), m.T ≤ m'.T → LE_Interp ρ a.T (mkInst ls ci.type) → m.HasType a →
      (LR Γ₀).DefEq (.const c ls) (.const c ls) (mkInst ls ci.type) m a

/-- The local IH for the `R`-premise of `LE_Interp.const`: same-rank bare-constant leaves. -/
def LR.LocalIH (Γ₀ : List SExpr) (ρ₀ : Valuation) (c : Name) (R : TShape → SExpr → Prop) : Prop :=
  ∀ m e, R m e → ∀ c' ls' ci', e = .const c' ls' → rank c' = rank c →
    Params.env.constants c' = some ci' → ls'.length = ci'.uvars → LR.ConstGoal Γ₀ ρ₀ m c' ls' ci'

/-- Amended spine lemma (R9; PLAN D4 + audit round 1): induction on `Const`, at EVERY valuation
above the telescope valuation that a `SubstWF` covers, goal at every typed shape below. -/
theorem LR.const_spine {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
    (WFIH : LR.WFIH rank Γ₀ k) {c : Name} {ci : VConstant} {ls : List SLevel}
    (hc : rank c < k) (h1 : Params.env.constants c = some ci) (h2 : ls.length = ci.uvars)
    {R : TShape → SExpr → Prop} (LIH : LR.LocalIH rank Γ₀ ρ₀ c R)
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
  sorry -- SORRY(statement only)

/-- E6 interface (R10 must prove exactly this; R9 calls it at `Const.pat`). The ctor clause and
the typed `x ≡ c' Zs` are read off `W`'s major entry (`Subst1` at `ctor' c' rargs'.reverse`,
`indTy`); `tyV` is the spine lemma's semantic type validity (from the last `PiDefEq` layer), at every
`SubstWF` over `ρ`, so it also covers `σ` with the major replaced by `c' Zs` (D4 step 6).
The R5 stage-1a fields (`indTy_closed`, `ctor_fields_closed`, `type_below`, `rank_ordered`)
enter E6 as section hypotheses. -/
theorem LR.pat_leaf_1a {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
    (WFIH : LR.WFIH rank Γ₀ k) {c : Name} {ci : VConstant} {ls : List SLevel}
    (hc : rank c < k) (h1 : Params.env.constants c = some ci) (h2 : ls.length = ci.uvars)
    {R : TShape → SExpr → Prop} (LIH : LR.LocalIH rank Γ₀ ρ₀ c R)
    {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} {mC : TShape}
    (hP : Params.Pat p r) (hMt : LE_Interp.Matches p c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1) (hchk : r.2 = .true)
    -- `Pattern.gen … p r.1 = some g` and the `pat_typed` / `pat_defeq` conclusions for it
    (gen : VEnv → (Name → Nat) → (Name → Option Classification) → (p : Pattern) → p.RHS → Option PatGen)
    (g : PatGen) (hg : gen Params.env rank Params.classify p r.1 = some g)
    (hty : OnCtx (g.self ++ g.ctx) (fun Γ A => (Params.env.below rank (rank c)).IsType ci.uvars Γ A) ∧
      (Params.env.below rank (rank c)).HasType ci.uvars (g.self ++ g.ctx) g.rhsAbs
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
  sorry -- SORRY(statement only)


/-- ρ_low's pattern-context part (PLAN D4 step 1), over `.nil` (the valuation of `SubstWF.id`,
base context `Γ₀`), innermost first: the lowered field entries `fields`, then the recursor
arguments `ρ 1 … ρ m` (`ρ 0` is the major). `fields[i]` is `l_i.T` when the ctor shape's field
`l_i` is `⊥` or a ctor shape, else `⊥`; `⊥` when the field type is Prop-valued. -/
def Valuation.lowerCtx (fields : List TShape) (ρ : Valuation) (m : Nat) : Valuation :=
  fields.foldr (fun x ρ' => ρ'.push x) <|
    (List.range m).foldr (fun i ρ' => ρ'.push (ρ (i + 1))) .nil

/-- ρ_low (PLAN D4 step 1): the self entries (index `j` = `j`-th self) on top of `lowerCtx`. -/
def Valuation.lower (selfs fields : List TShape) (ρ : Valuation) (m : Nat) : Valuation :=
  selfs.foldr (fun x ρ' => ρ'.push x) (Valuation.lowerCtx fields ρ m)

/-- E6a interface (PLAN D4 step 2). Produces the self entries for `W_p` (step 1) from `LIH`, and
`LE_Interp ρ_low y' rhsAbs` at every typed `y'` below the RHS shape `mC`. `idx` stands in for
`Pattern.gen`'s path ↦ `g.ctx` index (`σ_p (idx path) = m2 path`). Typed-entry facts: `hfit`
(every `lowerCtx` entry typed, as `SubstWF.cons` needs) and `hvar` (a typed shape below a
matched path shape is below its lowered entry). -/
theorem LR.rhs_lower {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name} {ls : List SLevel}
    {R : TShape → SExpr → Prop} (LIH : LR.LocalIH rank Γ₀ ρ₀ c R)
    {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} {mC : TShape}
    (hP : Params.Pat p r) (hMt : LE_Interp.Matches p c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1)
    (gen : VEnv → (Name → Nat) → (Name → Option Classification) → (p : Pattern) → p.RHS → Option PatGen)
    (g : PatGen) (hg : gen Params.env rank Params.classify p r.1 = some g)
    (idx : p.Path → Nat)
    {fields : List TShape} {ρ : Valuation} {m : Nat} (hm : g.ctx.length = fields.length + m)
    (hfit : (Valuation.lowerCtx fields ρ m).Fits Γ₀ (g.ctx.map (SExpr.mkInst ls) ++ Γ₀))
    (hvar : ∀ path {n} {y b : WShape n}, y.T ≤ m2 path → y.HasType b →
      LE_Interp (Valuation.lowerCtx fields ρ m) b.T
        (SExpr.mkInst ls ((g.ctx.getD (idx path) (.sort .zero)).liftN (idx path + 1))) →
      y.T ≤ Valuation.lowerCtx fields ρ m (idx path)) :
    ∃ selfs : List TShape, selfs.length = g.self.length ∧
      (∀ j s, selfs[j]? = some s → ∃ (me : TShape) (c' : Name) (ls' : List SLevel) (ci' : VConstant),
        R me (.const c' ls') ∧ rank c' = rank c ∧ Params.env.constants c' = some ci' ∧
        ls'.length = ci'.uvars ∧ me ≤ s ∧
        SExpr.mkInst ls (g.self.getD j (.sort .zero)) = SExpr.mkInst ls' ci'.type ∧
        (∃ (k : Nat) (x b : WShape k), s = x.T ∧ x.HasType b ∧
          LE_Interp ρ₀ b.T (SExpr.mkInst ls' ci'.type)) ∧
        LR.ConstGoal Γ₀ ρ₀ s c' ls' ci') ∧
      ∀ {n'} {y' a' : WShape n'}, y'.T ≤ mC → y'.HasType a' →
        LE_Interp (Valuation.lower selfs fields ρ m) a'.T
          (SExpr.mkInst ls (g.type.liftN g.self.length)) →
        LE_Interp (Valuation.lower selfs fields ρ m) y'.T (SExpr.mkInst ls g.rhsAbs) := by
  sorry -- SORRY(statement only)

end SExpr
end Lean4Lean

#check @Lean4Lean.SExpr.LR.rhs_lower
