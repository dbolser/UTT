import Lean4Lean.Experimental.E6.Iota2
/-! E6, iota shape: the recursor telescope's `SubstWF` taken apart, the major entry's
constructor clause, and the field entries of `W_p` (D4 step 1). -/
namespace Lean4Lean.SExpr
variable [Params]

/-- A `SubstWF` over `Δ ++ Γ₀` has the valuation `.nil` beyond `Δ`. -/
theorem T.substWF_nil_beyond {Γ₀ : List SExpr} {σ σ' : Subst} {ρ : Valuation} :
    ∀ {Δ : List SExpr}, LR.SubstWF Γ₀ σ σ' (Δ ++ Γ₀) ρ → ∀ i, Δ.length ≤ i → ρ i = Valuation.nil i := by
  intro Δ W
  generalize hΓ : Δ ++ Γ₀ = Γ at W
  induction W generalizing Δ with
  | id =>
    intro i _
    have : Δ = [] := List.eq_nil_of_length_eq_zero (by
      have := congrArg List.length hΓ; rw [List.length_append] at this; omega)
    rfl
  | @cons σ σ' Γ ρ A a x u W' _ _ _ _ _ ih =>
    intro i hi
    cases Δ with
    | nil =>
      have h1 := T.substWF_len W'
      have := congrArg List.length hΓ; simp at this; omega
    | cons B Δ' =>
      simp only [List.cons_append, List.cons.injEq] at hΓ
      obtain ⟨-, hΓ⟩ := hΓ
      cases i with
      | zero => simp at hi
      | succ j => exact ih hΓ j (by simpa using hi)

/-- Taking the outermost-pushed (head) entry off a `SubstWF` over `A :: (Δ ++ Γ₀)`. -/
theorem T.substWF_cons_inv {Γ₀ Δ : List SExpr} {A : SExpr} {σ σ' : Subst} {ρ : Valuation}
    (W : LR.SubstWF Γ₀ σ σ' (A :: (Δ ++ Γ₀)) ρ) :
    ∃ (ρ' : Valuation) (x a : TShape) (u : SLevel), ρ = ρ'.push x ∧
      LR.SubstWF Γ₀ σ.tail σ'.tail (Δ ++ Γ₀) ρ' ∧
      (∀ {a}, LE_Interp ρ' a A → ∃ a', a ≤ a' ∧ LE_Interp ρ' a' A ∧ a'.HasType .type) ∧
      LE_Interp ρ' a A ∧ x.HasType a ∧ (Δ ++ Γ₀) ⊢ A : .sort u ∧
      LR.Subst1 Γ₀ σ.head σ'.head A.lift (A.subst σ.tail) (A.subst σ'.tail) (ρ'.push x) := by
  generalize hΓ : A :: (Δ ++ Γ₀) = Γ at W
  cases W with
  | id =>
    have := congrArg List.length hΓ; simp at this; omega
  | cons W' h1 h2 h3 h4 h5 =>
    simp only [List.cons.injEq] at hΓ; obtain ⟨rfl, rfl⟩ := hΓ
    exact ⟨_, _, _, _, rfl, W', h1, h2, h3, h4, h5⟩

/-- `ctor' c` is `ctor c` for a non-structure constructor. -/
theorem T.ctor'_eq_ctor {c : Name} {k : Nat} (hcl : Params.classify c = some (.ctor k))
    {n : Nat} (l : List (WShape n)) :
    ∃ h, WShape.ctor' c l = WShape.ctor c l h := by
  have hs : ¬ IsStruct c = true := by simp [IsStruct, hcl]
  exact ⟨fun h => absurd h hs, by rw [WShape.ctor', dif_pos (fun h => absurd h hs)]⟩

omit [Params] in
theorem T.forall₂_getElem {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
    ∀ (i : Nat) a b, l₁[i]? = some a → l₂[i]? = some b → R a b
  | _, _, .nil, _, _, _, h, _ => by simp at h
  | _, _, .cons h1 _, 0, _, _, ha, hb => by simp at ha hb; subst ha hb; exact h1
  | _, _, .cons _ h2, i+1, _, _, ha, hb => T.forall₂_getElem h2 i _ _ (by simpa using ha) (by simpa using hb)

/-- A constructor shape is typed only at `indTy`. -/
theorem T.ctor_hasType {n : Nat} {c : Name} {l : List (WShape n)} {wf} {a : WShape (n+1)}
    (H : (WShape.ctor c l wf).HasType a) : a = .indTy := by
  cases a using WShape.casesOn' with
  | indTy => rfl
  | bot => cases congrArg (·.1) H.bot_r
  | sort => exact absurd H WShape.HasType.ctor_isType
  | forallE => exact absurd H WShape.HasType.ctor_not_forallE
  | lam => exact absurd H (by simp [WShape.HasType, WShape.ctor, WShape.lam]; exact nofun)
  | ctor => exact absurd H (by simp [WShape.HasType, WShape.ctor]; exact nofun)

/-- The major entry of the recursor telescope's `SubstWF`, at a constructor raw shape, is a
typed constructor shape `P = ctor c' l` (at a level `K+2`, fields at `K+1`) above the raw one,
and the substitution's major pair satisfies the constructor clause at `(P, indTy)`. -/
theorem T.major_ctor {Γ₀ : List SExpr} {D : SExpr} (hD : D.ClosedN) {c' : Name} {kk : Nat}
    (hcl : Params.classify c' = some (.ctor kk)) {σ σ' : Subst} {ρ' : Valuation} {x₀ a₀ : TShape}
    (hx₀ : x₀.HasType a₀) (hA₀ : LE_Interp ρ' a₀ D)
    (h0 : LR.Subst1 Γ₀ σ.head σ'.head D.lift (D.subst σ.tail) (D.subst σ'.tail) (ρ'.push x₀))
    {N : Nat} {raw : List (WShape N)} (hraw : (WShape.ctor' c' raw).T ≤ x₀) :
    ∃ (K : Nat) (l : List (WShape (K+1))) (wf : IsStruct c' = true → WShape.ListNonZero l),
      (WShape.ctor c' l wf : WShape (K+2)).T ≤ x₀ ∧ l.length = raw.length ∧
      (∀ (j : Nat) (s : WShape N) (t : WShape (K+1)), raw[j]? = some s → l[j]? = some t → s.T ≤ t.T) ∧
      LRS.CtorDefEq (LR Γ₀ (n := K+1)) (σ 0) (σ' 0) D c' l := by
  let K := max (max x₀.1 a₀.1) N
  have hk1 : x₀.1 ≤ K + 2 := by omega
  have hk2 : a₀.1 ≤ K + 2 := by omega
  have hk3 : N + 1 ≤ K + 2 := by omega
  have hPA : (x₀.2.lift (K+2)).HasType (a₀.2.lift (K+2)) := (TShape.HasType.def hk1 hk2).1 hx₀
  have hA₀' : LE_Interp (ρ'.push x₀) (a₀.2.lift (K+2)).T D.lift := (hA₀.lift hk2).weak
  have hP0 : LE_Interp (ρ'.push x₀) (x₀.2.lift (K+2)).T (.bvar 0) := .bvar (TShape.lift_eqv hk1).1
  have hDe := ((h0.2 _ hA₀').2 hP0 hPA)
  rw [hD.subst_eq .zero] at hDe
  have hle : (WShape.ctor' c' raw).lift (K+2) ≤ x₀.2.lift (K+2) := by
    have := hraw.trans (TShape.lift_eqv hk1).2
    rw [TShape.LE.def hk3 (Nat.le_refl _)] at this
    simpa [WShape.lift_self] using this
  have hPle : (x₀.2.lift (K+2)).T ≤ x₀ := (TShape.lift_eqv hk1).1
  generalize x₀.2.lift (K+2) = P at hPA hDe hle hPle
  generalize a₀.2.lift (K+2) = A₀ at hPA hDe
  rw [WShape.lift_ctor' (by omega)] at hle
  obtain ⟨h₁, he₁⟩ := T.ctor'_eq_ctor hcl (raw.map (WShape.lift (K+1)))
  rw [he₁, WShape.ctor_le] at hle
  obtain ⟨l, wf, rfl, hfa⟩ := hle
  have hA₀e : A₀ = .indTy := T.ctor_hasType hPA
  subst hA₀e
  have hDe' : LRS.CtorDefEq (LR Γ₀ (n := K+1)) (σ 0) (σ' 0) D c' l :=
    (LRS.DefEq.ctor_indTy (IH := LR Γ₀ (n := K+1)) (h := wf)).1 hDe
  have hlen := Lean4Lean.List.Forall₂.length_eq hfa
  refine ⟨K, l, wf, hPle, by simpa using hlen.symm, fun j s t hs ht => ?_, hDe'⟩
  have := T.forall₂_getElem hfa j _ t (by rw [List.getElem?_map, hs]; rfl) ht
  exact (TShape.lift_eqv (a := s.T) (show N ≤ K+1 by omega)).2.trans (WShape.LE.T this)

end Lean4Lean.SExpr

namespace Lean4Lean.SExpr
variable [Params]

/-- The constructor clause, read with `ctor_fields_closed`: the clause's field types are the
constructor's (closed) field types at the clause's levels. -/
theorem T.ctor_clause_data {Γ₀ : List SExpr} {K : Nat} {x x' D : SExpr} {c' : Name} {nn : Nat}
    {l : List (WShape (K+1))} {ci' : VConstant} {I'' : Name} {Tsc : List VExpr}
    (hcl : Params.classify c' = some (.ctor nn)) (hci' : Params.env.constants c' = some ci')
    (e4 : ci'.type = Tsc.foldr .forallE (.const I'' (VLevel.params ci'.uvars)))
    (H : LRS.CtorDefEq (LR Γ₀ (n := K+1)) x x' D c' l) :
    ∃ (ls'' : List SLevel) (Xs Ys : List SExpr),
      Params.classify I'' = some (.indTy 0) ∧ TyRedS Γ₀ D (.const I'' ls'') ∧
      TWHRedS Γ₀ x (spine (.const c' ls'') Xs) D ∧ TWHRedS Γ₀ x' (spine (.const c' ls'') Ys) D ∧
      LRS.FieldsEq (LR Γ₀ (n := K+1)) (Tsc.map (mkInst ls'')) Xs Ys l ∧ l.length = nn ∧
      (VLevel.params ci'.uvars).map (SLevel.instV ls'') = ls'' := by
  obtain ⟨I_c, ls'', ci'', Ts'', Xs, Ys, hc, hI, hci'', hty, hA, hM, hN, hF⟩ := H
  cases hci'.symm.trans hci''
  rw [e4, mkInst_foldr_forallE] at hty
  obtain ⟨h1, rfl, h3⟩ := foldr_forallE_const_inj hty
  cases hcl.symm.trans hc
  exact ⟨ls'', Xs, Ys, hI, hA, hM, hN, h1 ▸ hF, rfl, h3⟩

/-- The levels tie of the constructor clause (PLAN §4 open question 3): the clause's levels are
the major domain's. -/
theorem T.major_levels_whnf {Γ₀ : List SExpr} {I I_c : Name} {us₀ ls'' : List SLevel}
    (hI : ∀ k, Params.classify I ≠ some (.symb k))
    (hred : TyRedS Γ₀ (.const I us₀) (.const I_c ls'')) : I = I_c ∧ us₀ = ls'' := by
  have hw : WHNF Γ₀ (.const I us₀) := WHNF.of_headE hI (ls := us₀) rfl
  have := hw.whRedS hred.2
  injection this with e1 e2
  exact ⟨e1, e2⟩

/-- The field entries of `W_p`, pushed over any base `SubstWF` (D4 step 1, fields): each is the
lowered clause field `T.lowerF`, typed at `T.lowerA`, related by `FieldRel`. -/
theorem T.cons_fields {Γ₀ : List SExpr} {k : Nat} (WFIH : LR.WFIH Params.rank Γ₀ k)
    {c : Name} (hc : Params.rank c < k) {K : Nat} :
    ∀ {Fs Xs Ys : List SExpr} {l : List (WShape (K+1))},
    LRS.FieldsEq (LR Γ₀ (n := K+1)) Fs Xs Ys l →
    ∀ {Δ : List SExpr} {τ τ' : Subst} {ρb : Valuation}, LR.SubstWF Γ₀ τ τ' Δ ρb →
    (∀ (i : Nat) (F : SExpr), Fs[i]? = some F → F.ClosedN ∧
      ∃ u, IsDefEqStrong (Params.env.below Params.rank (Params.rank c))
        ((Fs.take i).reverse ++ Δ) F F (.sort u)) →
    LR.SubstWF Γ₀ (Xs.foldl (fun τ x => τ.cons x) τ) (Ys.foldl (fun τ x => τ.cons x) τ')
      (Fs.reverse ++ Δ)
      ((List.zipWith (fun F li => (T.lowerF K F li).T) Fs l).foldl (fun ρ' x => ρ'.push x) ρb) := by
  intro Fs Xs Ys l H
  induction H with
  | nil => intro Δ τ τ' ρb W _; exact W
  | @cons X Y F li Fs' Xs' Ys' l' hxy hrel _ ih =>
    intro Δ τ τ' ρb W hT
    obtain ⟨hcl, u, HA⟩ := hT 0 F rfl
    have W1 := T.cons_closed WFIH hc (by simpa using HA) hcl T.lowerF_has (T.lowerA_interp hcl)
      hxy (T.lowerF_defeq hrel) W
    have := ih W1 fun i F' hF' => by
      obtain ⟨h1, u', h2⟩ := hT (i+1) F' (by simpa using hF')
      refine ⟨h1, u', ?_⟩
      simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using h2
    simpa [List.reverse_cons, List.append_assoc] using this

end Lean4Lean.SExpr
