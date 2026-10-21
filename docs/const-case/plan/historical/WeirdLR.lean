import Lean4Lean.Experimental.ShapeLogRelAdequacy
-- historical: typechecked at 3c35f59, before the typed logical relation (docs/const-case/PLAN.md D6, landed by R1+R2); no longer compiles.
/-! Refuter (proof, lens clause), experiment 3.
A `LogRel Γ n` (all 19 fields proven) that is `LR0`-like at every level: non-trivial only at
`sort`, `True` at `forallE`.  For it the hypothesis `LiftHyp` that GenericSpine.lean's
`conv`/`symm`/`trans` need FAILS.  So `LiftHyp` is not a consequence of the `LogRel` fields and
cannot be discharged inside `def LRS (IH : LogRel Γ n)` as it stands: the ctor clause's
`symm`/`trans` need either an LR tower that carries the inter-level lift as data, or a clause
that avoids `conv`.  No sorries. -/
namespace Lean4Lean.SExpr
variable [Params]

def IsSortS {n} (s : WShape n) : Prop := ∃ r, s = .sort r

def WTy (Γ : List SExpr) {n} (M N : SExpr) (s : WShape n) : Prop :=
  IsSortS s → ∃ u, Γ ⊢ M ⤳* .sort u ∧ Γ ⊢ N ⤳* .sort u

def WDe (Γ : List SExpr) {n} (M N : SExpr) (m a : WShape n) : Prop :=
  IsSortS a → WTy Γ M N m

theorem bot_not_sort {n} : ¬ IsSortS (WShape.bot : WShape n) := by
  rintro ⟨r, h⟩
  have := WShape.le_sort.1 (show (WShape.bot : WShape n) ≤ .sort r from h ▸ WShape.LE.rfl)
  have h2 : (WShape.sort r : WShape n) ≤ .bot := h ▸ WShape.LE.rfl
  have := WShape.le_bot.1 h2
  have h3 := WShape.sort_le.1 (show (WShape.sort r : WShape n) ≤ .sort r from WShape.LE.rfl)
  -- sort r = bot is impossible: bot ≤ sort false but sort r ≤ bot forces sort r = bot
  cases n with
  | zero => cases this
  | succ n => cases this

theorem ex_sort_determ (h1 : Γ ⊢ M ⤳* .sort u) (h2 : Γ ⊢ M ⤳* .sort u') : u = u' := by
  cases h1.determ .sort h2 .sort; rfl

def WeirdLR (Γ : List SExpr) (n : Nat) : LogRel Γ n where
  DefEq M N _ m a := WDe Γ M N m a
  TyDefEq M N s := WTy Γ M N s
  sort_iff := ⟨fun h => h ⟨_, rfl⟩ ⟨_, rfl⟩, fun h _ _ => h⟩
  sort_iff_ty := ⟨fun h => h ⟨_, rfl⟩, fun h _ => h⟩
  bot _ := fun _ hb => (bot_not_sort hb).elim
  toType h := h ⟨_, rfl⟩
  left h ha hm := let ⟨u, h1, _⟩ := h ha hm; ⟨u, h1, h1⟩
  left_ty h hm := let ⟨u, h1, _⟩ := h hm; ⟨u, h1, h1⟩
  symm h ha hm := let ⟨u, h1, h2⟩ := h ha hm; ⟨u, h2, h1⟩
  symm_ty h hm := let ⟨u, h1, h2⟩ := h hm; ⟨u, h2, h1⟩
  trans h h' ha hm :=
    let ⟨u, h1, h2⟩ := h ha hm; let ⟨_, h2', h3⟩ := h' ha hm
    ⟨u, h1, ex_sort_determ h2 h2' ▸ h3⟩
  trans' h h' ha hm :=
    let ⟨u, h1, h2⟩ := h ha hm; let ⟨_, h2', h3⟩ := h' ⟨_, rfl⟩ hm
    ⟨u, h1, ex_sort_determ h2 h2' ▸ h3⟩
  trans_ty h h' hm :=
    let ⟨u, h1, h2⟩ := h hm; let ⟨_, h2', h3⟩ := h' hm
    ⟨u, h1, ex_sort_determ h2 h2' ▸ h3⟩
  conv _ h := h
  mono_r_2 le _ _ h := by
    rintro ⟨r, rfl⟩; exact h ⟨r, (WShape.sort_le.1 le).symm⟩
  mono_r_2_ty le _ _ h := by
    rintro ⟨r, rfl⟩; exact h ⟨r, (WShape.sort_le.1 le).symm⟩
  mono_r_1 le h1 _ _ h := by
    rintro ⟨r, rfl⟩
    rcases WShape.le_sort.1 le with rfl | rfl
    · cases h1.bot_r; intro hb; exact (bot_not_sort hb).elim
    · exact h ⟨r, rfl⟩
  mono_l le _ _ h := by
    intro ha; rintro ⟨r, rfl⟩; exact h ha ⟨r, (WShape.sort_le.1 le).symm⟩
  join_ty hC _ _ h1 h2 := by
    rintro ⟨r, hj⟩
    have ⟨l1, l2⟩ := (WShape.Join.mk hC).le
    rw [hj] at l1 l2
    rcases WShape.le_sort.1 l1 with e1 | e1
    · rcases WShape.le_sort.1 l2 with e2 | e2
      · subst e1 e2; rw [WShape.bot_join] at hj; exact (bot_not_sort ⟨r, hj⟩).elim
      · exact h2 ⟨r, e2⟩
    · exact h1 ⟨r, e1⟩
  whr hM hN := by
    constructor <;> intro h ha hm <;> obtain ⟨u, r1, r2⟩ := h ha hm
    · exact ⟨u, hM.determ_l r1 .sort, hN.determ_l r2 .sort⟩
    · exact ⟨u, .trans hM r1, .trans hN r2⟩
  whr_ty hA hB := by
    constructor <;> intro h hm <;> obtain ⟨u, r1, r2⟩ := h hm
    · exact ⟨u, hA.determ_l r1 .sort, hB.determ_l r2 .sort⟩
    · exact ⟨u, .trans hA r1, .trans hB r2⟩

/-- Same as GenericSpine.lean. -/
def LiftHyp {Γ : List SExpr} {n : Nat} (IH : LogRel Γ n) : Prop :=
  ∀ {M N : SExpr} {s : WShape n}, s.HasType .type → IH.TyDefEq M N s →
    LRS.TyDefEq IH M N (s.lift (n+1))

theorem WHNF.bvar' : WHNF Γ (.bvar i) := by
  intro _ H; cases H with
  | extra h1 h2 => obtain ⟨_|_, rfl⟩ := Params.pat_simple h1 <;> nomatch h2

/-- `LiftHyp` fails for `WeirdLR` at level 1, at `s = Π ⊥ ⊥`, `M = N = bvar 0`. -/
theorem weird_not_liftHyp : ¬ LiftHyp (WeirdLR [.sort .zero] 1) := by
  intro hl
  have hs : (WShape.forallE (n := 0) .bot .bot).HasType .type := rfl
  have hty : (WeirdLR [.sort .zero] 1).TyDefEq (.bvar 0) (.bvar 0) (WShape.forallE .bot .bot) := by
    rintro ⟨r, h⟩; cases congrArg (·.1) h
  have := hl hs hty
  rw [WShape.lift_forallE (Nat.le_succ 0)] at this
  obtain ⟨_, _, _, _, _, _, rM, -⟩ := (LRS.TyDefEq.forallE_iff (IH := WeirdLR _ 1)).1 this
  cases WHNF.bvar'.whRedS rM

end Lean4Lean.SExpr

#print axioms Lean4Lean.SExpr.WeirdLR
#print axioms Lean4Lean.SExpr.weird_not_liftHyp
