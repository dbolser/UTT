import Lean4Lean.Experimental.ShapeLogRelAdequacy
-- historical: typechecked at 3c35f59, before the stage-1a constructor clause (docs/const-case/PLAN.md D1/D2, landed by R3); no longer compiles.
namespace Lean4Lean.SExpr
variable [Params]

/-! Experiment 2: with the LR unchanged (`DefEq` is `True` at type-shape `indTy`),
`LR.SubstWF` accepts an arbitrary term `x : N` (e.g. a bare bound variable of `Γ₀`)
at a constructor-valued shape. Hence `Adequate` quantifies over instances that are
syntactically stuck at the major-premise position. -/

/-- For an inductive-type constant `N` (classified `indTy 0`), the only shapes assigned by
`Const` are `bot` (at any spine) and `indTy` (at the empty spine). -/
theorem Const.indTy_inv (hN : Params.classify N = some (.indTy 0)) {n} {rargs : List (WShape n)}
    (H : LE_Interp.Const N ls R rargs m') :
    m' ≤ TShape.bot ∨ (rargs = [] ∧ m' ≤ (WShape.indTy : WShape (n+1)).T) := by
  induction H with
  | bot => exact .inl TShape.bot_eqv.1
  | @lam f rargs m hrec hle ih =>
    refine .inl (hle.trans ?_)
    have : WShape.lam' f = .bot := by
      unfold WShape.lam'; split <;> [rename_i hnz; rfl]
      obtain ⟨⟨x, y⟩, hxy, hy⟩ := WShapeFun.NonZero.iff.1 hnz
      rcases ih x y hxy with h | ⟨h, _⟩
      · exact (hy (WShape.LE.T_iff.1 (h.trans TShape.bot_eqv.2))).elim
      · cases h
    rw [this]; exact TShape.bot_eqv.1
  | ctor h => cases hN.symm.trans h
  | indTy h hle =>
    have := Option.some.inj (hN.symm.trans h)
    injection this with hl
    have hl := List.length_eq_zero_iff.1 hl.symm
    subst hl; exact .inr ⟨rfl, hle⟩
  | pat hP hM =>
    obtain ⟨_, h⟩ := hM.head_wf (Params.pat_wf hP)
    cases hN.symm.trans h

theorem TShape.indTy_le_indTy {n} : (WShape.indTy : WShape (n+1)).T ≤ (WShape.indTy : WShape 1).T := by
  refine (TShape.LE.def (m := n+1) (Nat.le_refl _) (Nat.succ_le_succ (Nat.zero_le _))).2 ?_
  rw [WShape.lift_self, WShape.lift_indTy]; exact .rfl

theorem LE_Interp.indTy_const_inv (hN : Params.classify N = some (.indTy 0))
    (ha : LE_Interp ρ t (.const N ls)) : t ≤ TShape.bot ∨ t ≤ (WShape.indTy : WShape 1).T := by
  cases ha with
  | bot => exact .inl TShape.bot_eqv.1
  | const _ _ hle _ _ hC _ =>
    rcases Const.indTy_inv hN hC with h | ⟨-, h⟩
    · exact .inl (hle.trans h)
    · exact .inr ((hle.trans h).trans TShape.indTy_le_indTy)

/-- Every shape interpreting `const N ls` is `bot` or `indTy`; at both, `TyDefEq` and `DefEq`
are trivially true in the current LR. -/
theorem LR.trivial_at_indTy (hN : Params.classify N = some (.indTy 0)) {n} {a : WShape n}
    (ha : LE_Interp ρ a.T (.const N ls)) (A A' x x' : SExpr) :
    (LR Γ₀).TyDefEq A A' a ∧ ∀ m, (LR Γ₀).DefEq x x' A m a := by
  rcases LE_Interp.indTy_const_inv hN ha with h | h
  · have ha : a = .bot := TShape.le_bot.1 h
    subst ha; cases n <;> exact ⟨trivial, fun _ => trivial⟩
  · cases n with
    | zero =>
      obtain ⟨⟨⟩, _⟩ := a
      · exact ⟨trivial, fun _ => trivial⟩
      · exfalso
        have := (TShape.LE.def (m := 1) (Nat.zero_le _)
          (show (WShape.indTy : WShape 1).T.1 ≤ 1 from Nat.le_refl 1)).1 h
        simp only [WShape.T] at this
        cases WShape.sort_le.1 this
    | succ k =>
      have := (TShape.LE.def (m := k+1) (Nat.le_refl _)
        (show (WShape.indTy : WShape 1).T.1 ≤ k + 1 from Nat.succ_le_succ (Nat.zero_le _))).1 h
      simp only [WShape.T] at this
      rw [WShape.lift_self, WShape.lift_indTy] at this
      rcases WShape.le_indTy.1 this with rfl | rfl
      · exact ⟨trivial, fun _ => trivial⟩
      · exact ⟨trivial, fun _ => trivial⟩

/-- `SubstWF` accepts any `x : N` at any shape `xs : indTy`, e.g. a constructor shape. -/
theorem LR.SubstWF.push_any_at_ctor
    (W : LR.SubstWF Γ₀ σ σ Γ ρ) (hN : Params.classify N = some (.indTy 0))
    (hNty : Γ ⊢ .const N ls : .sort u) (hx : Γ₀ ⊢ x : .const N ls)
    (hI : LE_Interp ρ (WShape.indTy : WShape (k+1)).T (.const N ls))
    (xs : WShape (k+1)) (hxs : xs.HasType .indTy) :
    LR.SubstWF Γ₀ (σ.cons x) (σ.cons x) (.const N ls :: Γ) (ρ.push xs.T) := by
  refine .cons (σ := σ.cons x) (σ' := σ.cons x) W
    (fun ha => InterpTyped.hsort (fun h => (LE_Interp.sound W.wf hNty W.fits).2 h) ha) hI hxs.T hNty ?_
  refine ⟨hx, fun n a ha => ?_⟩
  have ha' : LE_Interp ρ a.T (.const N ls) := LE_Interp.weak_iff.1 ha
  exact ⟨fun _ => ⟨⟨_, hNty.subst W.wf₀ W.left.toSubstEq⟩, (LR.trivial_at_indTy hN ha' _ _ x x).1⟩,
    fun m _ _ => (LR.trivial_at_indTy hN ha' _ (.const N ls) x x).2 m⟩

end Lean4Lean.SExpr
