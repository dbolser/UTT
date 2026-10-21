import Lean4Lean.Experimental.E6.Iota3
/-! E6, iota shape: the RHS type's interpretations at `ρ_low` are interpretations of `B` at `ρ`
(substitution inversion + the constructor-spine inversion), substitution algebra for `g.type`,
and the typing of the open recursor spine. -/
namespace Lean4Lean.SExpr
variable [Params]

theorem T.mkInst_inst (ls : List SLevel) (e a : VExpr) :
    mkInst ls (e.inst a) = (mkInst ls e).inst (mkInst ls a) := by
  obtain ⟨vs, hvs, rfl⟩ := SLevel.exists_map_mk ls
  rw [mkInst_map_mk hvs, mkInst_map_mk hvs, mkInst_map_mk hvs, VExpr.instL_instN, mk_instExpr]

theorem T.mkInst_liftN1 (ls : List SLevel) (e : VExpr) (nn : Nat) :
    mkInst ls (e.liftN nn 1) = (mkInst ls e).lift' (.consN (.skipN .refl nn) 1) := by
  rw [← VExpr.lift'_consN_skipN, mkInst_lift']

/-- Substitution inversion for the RHS type `Bmaj[c' Zs]` (D4 step 6, the `a''`-vs-`a` link):
if every interpretation of the spine `Z` is below `ρ 0` and the outer entries are below `ρ`'s,
an interpretation of the instance is one of `Bmaj` at `ρ`. -/
theorem T.type_inv {ls : List SLevel} {Bmaj Z : VExpr} {nn : Nat} {ρc ρ : Valuation} {z : TShape}
    (H : LE_Interp ρc z (mkInst ls ((Bmaj.liftN nn 1).inst Z)))
    (hZ : ∀ x, LE_Interp ρc x (mkInst ls Z) → x ≤ ρ 0)
    (hrest : ∀ i, ρc (nn + i) ≤ ρ (i+1)) :
    LE_Interp ρ z (mkInst ls Bmaj) := by
  rw [T.mkInst_inst, T.mkInst_liftN1] at H
  obtain ⟨x, hF, hx⟩ := LE_Interp.inst.1 H
  have := (LE_Interp.weak'_iff (.consN (.skipN .refl nn) 1)
    (ρ := fun i => (ρc.push x) ((Lift.consN (.skipN .refl nn) 1).liftVar i)) (fun _ => rfl)).1 hF
  refine this.mono_l fun i => ?_
  cases i with
  | zero => exact hZ x hx
  | succ j =>
    simp only [Lift.consN, Lift.liftVar, Lift.liftVar_skipN, Valuation.push]
    rw [Nat.add_comm]; exact hrest j

/-- A type shape compatible with `indTy` is below it. -/
theorem T.compat_indTy_le {n K : Nat} {a : WShape n}
    (hc : a.T.Compat (WShape.indTy (n := K)).T) : a.T ≤ (WShape.indTy (n := K)).T := by
  have le₁ := Nat.le_max_left n (K+1); have le₂ := Nat.le_max_right n (K+1)
  have hc' := (TShape.Compat.def le₁ le₂).1 hc
  obtain ⟨M, hM⟩ : ∃ M, max n (K+1) = M + 1 := ⟨max n (K+1) - 1, by omega⟩
  simp only [WShape.T] at hc'
  rw [hM, WShape.lift_indTy] at hc'
  obtain ⟨z, hz1, hz2⟩ := WShape.Compat.iff.1 hc'
  rw [WShape.indTy_le] at hz2; subst hz2
  rw [WShape.le_indTy] at hz1
  rw [TShape.LE.def le₁ le₂]
  simp only [WShape.T]; rw [hM, WShape.lift_indTy]
  rcases hz1 with h | h <;> rw [h]
  · exact WShape.bot_le
  · exact WShape.LE.rfl

/-! ### Substitutions pushed by `foldl` -/

theorem T.foldl_cons_add : ∀ (Xs : List SExpr) (τ : Subst) (i : Nat),
    (Xs.foldl (fun (τ : Subst) x => τ.cons x) τ) (Xs.length + i) = τ i
  | [], _, _ => by simp
  | X :: Xs, τ, i => by
    rw [List.foldl_cons, List.length_cons, show Xs.length + 1 + i = Xs.length + (i + 1) by omega,
      T.foldl_cons_add Xs _ (i+1)]; rfl

theorem T.foldl_cons_range : ∀ (Xs : List SExpr) (τ : Subst),
    (List.range Xs.length).reverse.map (Xs.foldl (fun (τ : Subst) x => τ.cons x) τ) = Xs
  | [], _ => rfl
  | X :: Xs, τ => by
    rw [List.length_cons, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, List.foldl_cons, T.foldl_cons_range Xs]
    have := T.foldl_cons_add Xs (τ.cons X) 0
    rw [Nat.add_zero] at this; rw [this]; rfl

/-- The strong typing of the codomain of a strongly typed telescope, in its telescope context. -/
theorem T.telStrong_body {E : VEnv} : ∀ {Γ Ts : List SExpr} {B : SExpr}, TelStrongE E Γ Ts B →
    ∃ v, IsDefEqStrong E (Ts.reverse ++ Γ) B B (.sort v)
  | _, _, _, .nil H => ⟨_, H⟩
  | _, _, _, .cons (T := T) (Ts := Ts) _ H => by
    obtain ⟨v, H'⟩ := T.telStrong_body H
    exact ⟨v, by simpa [List.reverse_cons, List.append_assoc] using H'⟩

theorem T.liftK_app (f a : SExpr) : ∀ k, liftK (.app f a) k = .app (liftK f k) (liftK a k)
  | 0 => rfl
  | k+1 => by rw [liftK, T.liftK_app f a k]; rfl

theorem T.liftK_bvar (i : Nat) : ∀ k, liftK (.bvar i) k = .bvar (i + k)
  | 0 => rfl
  | k+1 => by rw [liftK, T.liftK_bvar i k]; rfl

/-- The open spine `f (bvar (k-1)) … (bvar 0)` is typed by the telescope's codomain. -/
theorem T.openSpine_typing : ∀ {Ts : List SExpr} {Γ : List SExpr} {f B : SExpr},
    Γ ⊢ f : Ts.foldr .forallE B →
    Ts.reverse ++ Γ ⊢ spine (liftK f Ts.length) ((List.range Ts.length).reverse.map .bvar) : B
  | [], _, _, _, H => H
  | A :: Ts, Γ, f, B, H => by
    have H' : Γ ⊢ f : .forallE A (Ts.foldr .forallE B) := H
    have H1 := H'.weak' (Ctx.Lift'.one (A := A))
    simp only [SExpr.lift'] at H1
    have H2 : A :: Γ ⊢ .app f.lift (.bvar 0) : Ts.foldr .forallE B := by
      have := IsDefEq.appDF H1 (IsDefEq.bvar (Lookup.zero (ty := A) (Γ := Γ)))
      rwa [lift_cons_skip_inst_bvar0] at this
    have IH := T.openSpine_typing H2
    rw [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons]
    rw [T.liftK_app, T.liftK_bvar, liftK_lift, Nat.zero_add] at IH
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, spine_cons]
    exact IH

end Lean4Lean.SExpr
