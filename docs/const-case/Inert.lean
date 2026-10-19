import Lean4Lean.Experimental.ShapeLogRelAdequacy
namespace Lean4Lean.SExpr
variable [Params]

/-! Lens 4, experiment 1: the `IsStruct`/`ctor'` collapse (ShapeLogRel.lean:815-818, 977)
is inert for every shape the model actually produces.

(a) `Const.ctor` needs `classify c = ctor _`, so `IsStruct c = false` and `ctor' c l = ctor c l _`.
(b) The ctor position of a pattern (`Matches.app`) is `.ctor`-classified under `pat_wf`, so
    the collapse never fires there either.
(c) An `etaCtor`-classified constant interprets only to `bot` (no `Const` leaf accepts it),
    so no shape `ctor S l` for a structure `S` is ever produced by `LE_Interp`. -/

/-- (a) -/
theorem Const.ctor_not_struct (h : Params.classify c = some (.ctor k)) : IsStruct c = false := by
  simp [IsStruct, h]

theorem WShape.ctor'_eq_of_not_struct (h : IsStruct c = false) (l : List (WShape n)) :
    ∃ hc, WShape.ctor' c l = WShape.ctor c l hc := by
  unfold WShape.ctor'; rw [dif_pos (fun h' => by simp [h] at h')]; exact ⟨_, rfl⟩

/-- (a) in the form used by `Const.ctor`: the leaf shape is a genuine `ctor` shape, never `bot`,
even when all fields are `bot`. -/
theorem Const.ctor_shape {rargs : List (WShape n)} (h : Params.classify c = some (.ctor rargs.length))
    (hle : m ≤ WShape.T (n := n + 1) (.ctor' c rargs.reverse)) :
    ∃ hc, m ≤ WShape.T (n := n + 1) (.ctor c rargs.reverse hc) := by
  obtain ⟨hc, e⟩ := WShape.ctor'_eq_of_not_struct (Const.ctor_not_struct h) rargs.reverse
  exact ⟨hc, e ▸ hle⟩

/-- (b) -/
theorem Matches.ctor_not_struct (H : LE_Interp.Matches (n := n) p c rargs m)
    (wf : p.WF Params.classify false k) : IsStruct c = false := by
  have ⟨_, h⟩ := H.head_wf wf; simp [IsStruct, h]

/-- (c) -/
theorem Const.etaCtor_bot (hS : Params.classify S = some (.etaCtor p a)) {n}
    {rargs : List (WShape n)} (H : LE_Interp.Const S ls R rargs m) : m ≤ TShape.bot := by
  induction H with
  | bot => exact TShape.bot_eqv.1
  | @lam f rargs m hrec hle ih =>
    refine hle.trans ?_
    have : WShape.lam' f = .bot := by
      unfold WShape.lam'; split <;> [rename_i hnz; rfl]
      obtain ⟨⟨x, y⟩, hxy, hy⟩ := WShapeFun.NonZero.iff.1 hnz
      exact (hy (WShape.LE.T_iff.1 ((ih x y hxy).trans TShape.bot_eqv.2))).elim
    rw [this]; exact TShape.bot_eqv.1
  | ctor h => cases hS.symm.trans h
  | indTy h => cases hS.symm.trans h
  | pat hP hM => obtain ⟨_, h⟩ := hM.head_wf (Params.pat_wf hP); cases hS.symm.trans h

theorem LE_Interp.etaCtor_bot (hS : Params.classify S = some (.etaCtor p a))
    (H : LE_Interp ρ m (.const S ls)) : m ≤ TShape.bot := by
  cases H with
  | bot => exact TShape.bot_eqv.1
  | const _ _ hle _ _ hC _ => exact hle.trans (Const.etaCtor_bot hS hC)

end Lean4Lean.SExpr
