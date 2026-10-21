import Lean4Lean.Experimental.E6.Iota5
/-! E6, iota shape: the major-replaced `SubstWF` (D4 step 6), the levels tie, the valuation of the
recursor part, and the field-entry typings. -/
namespace Lean4Lean.SExpr
variable [Params]

/-- Replace the major's right-hand side by its typed whnf (a `SubstWF` for `(σ, σ[0 := Z])`). -/
theorem T.major_replace {Γ₀ Δ : List SExpr} {D Z : SExpr} (hD : D.ClosedN) {σ σ' : Subst}
    {ρ : Valuation} (W : LR.SubstWF Γ₀ σ σ' (D :: (Δ ++ Γ₀)) ρ)
    (hZ : TWHRedS Γ₀ (σ 0) Z D) :
    LR.SubstWF Γ₀ σ (σ.tail.cons Z) (D :: (Δ ++ Γ₀)) ρ := by
  obtain ⟨ρ', x, a, u, rfl, WH, h1, h2, h3, h4, h5⟩ := T.substWF_cons_inv W
  have e1 : D.subst σ.tail = D := hD.subst_eq .zero
  have e2 : D.subst σ'.tail = D := hD.subst_eq .zero
  have e3 : D.lift = D := hD.lift_eq
  refine .cons (σ' := σ.tail.cons Z) WH.left h1 h2 h3 h4 ⟨?_, fun n b hb => ⟨fun ht => ?_, ?_⟩⟩
  · show Γ₀ ⊢ σ 0 ≡ Z : D.subst σ.tail
    rw [e1]; exact hZ.1
  · obtain ⟨⟨u', hu⟩, hT⟩ := (h5.2 b hb).1 ht
    rw [e1, e2] at hu hT
    have e4 : D.subst (σ.tail.cons Z).tail = D := hD.subst_eq .zero
    rw [e1, e4]
    exact ⟨⟨u', hu⟩, hT⟩
  · intro mm hmm hmb
    have hd := (LR Γ₀).left ((h5.2 b hb).2 hmm hmb)
    rw [e1] at hd
    rw [e1]
    have hrefl : TWHRedS Γ₀ (σ 0) (σ 0) D := ⟨hZ.1.hasType.1, .rfl⟩
    exact ((LR Γ₀).whr hrefl hZ).1 hd

/-- The recursor part of `lowerCtx` is the base valuation of the recursor telescope's `SubstWF`. -/
theorem T.recVal_eq {ρ' : Valuation} {x₀ : TShape} {mm : Nat}
    (hnil : ∀ i, mm ≤ i → ρ' i = Valuation.nil i) :
    ρ' = (List.range mm).foldr (fun i ρ'' => ρ''.push ((ρ'.push x₀) (i + 1))) .nil := by
  funext j
  by_cases hj : j < mm
  · rw [List.range_eq_range', T.range'_foldr _ mm 0 j hj]; simp [Valuation.push]
  · have e : (List.range mm).foldr (fun i ρ'' => ρ''.push ((ρ'.push x₀) (i + 1))) Valuation.nil =
        ((List.range mm).map fun i => (ρ'.push x₀) (i + 1)).foldr (fun x ρ'' => ρ''.push x) .nil := by
      rw [List.foldr_map]
    have hl : ((List.range mm).map fun i => (ρ'.push x₀) (i + 1)).length = mm := by simp
    rw [e, hnil j (by omega)]
    conv => rhs; rw [show j = ((List.range mm).map fun i => (ρ'.push x₀) (i + 1)).length + (j - mm) by
      rw [hl]; omega]
    rw [T.foldr_push_add]; rfl

end Lean4Lean.SExpr

namespace Lean4Lean.SExpr
variable [Params]

/-- The field types' rank-bounded strong typings in their pattern-context positions, from
`EnvStrongR.ctx` (D4 step 1, `ihA`/`HA` of the field entries). -/
theorem T.fields_typing {Γ₀ : List SExpr} {p : Pattern} {r : p.RHS × p.Check} {g : PatGen}
    {ci : VConstant} {ls : List SLevel} (hP : Params.Pat p r)
    (hg : Pattern.gen Params.env Params.rank Params.classify p r.1 = some g)
    (hci : Params.env.constants p.head = some ci) {Fs Hm : List SExpr}
    (hctxM : g.ctx.map (mkInst ls) = Fs.reverse ++ Hm) (hFcl : ∀ F ∈ Fs, F.ClosedN) :
    ∀ (i : Nat) (F : SExpr), Fs[i]? = some F → F.ClosedN ∧
      ∃ u, IsDefEqStrong (Params.env.below Params.rank (Params.rank p.head))
        ((Fs.take i).reverse ++ (Hm ++ Γ₀)) F F (.sort u) := by
  intro i F hF
  have hi : i < Fs.length := (List.getElem?_eq_some_iff.1 hF).1
  refine ⟨hFcl F (List.mem_of_getElem? hF), ?_⟩
  have hj : Fs.length - 1 - i < Fs.reverse.length := by simp; omega
  have hm : (g.ctx.map (mkInst ls))[Fs.length - 1 - i]? = some F := by
    rw [hctxM, List.getElem?_append_left hj, List.getElem?_reverse (by simpa using hj)]
    rw [show Fs.length - 1 - (Fs.length - 1 - i) = i by omega]; exact hF
  rw [List.getElem?_map] at hm
  obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.1 hm
  obtain ⟨u, Hu⟩ := EnvStrongR.of_params.ctx ls hP hg hci (g.self.length + (Fs.length - 1 - i)) A
    (by rw [List.getElem?_append_right (by omega), show g.self.length + (Fs.length - 1 - i) -
      g.self.length = Fs.length - 1 - i by omega]; exact hA)
  refine ⟨u, ?_⟩
  have hctx' : ((g.self ++ g.ctx).drop (g.self.length + (Fs.length - 1 - i) + 1)).map (mkInst ls) =
      (Fs.take i).reverse ++ Hm := by
    rw [show g.self.length + (Fs.length - 1 - i) + 1 = g.self.length + (Fs.length - i) by omega,
      List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
      show g.self.length + (Fs.length - i) - g.self.length = Fs.length - i by omega,
      List.map_drop, hctxM, List.drop_append, List.drop_reverse,
      show Fs.length - (Fs.length - i) = i by omega,
      show Fs.length - i - Fs.reverse.length = 0 by simp, List.drop_zero]
  have := Hu.weak_append (Γ₀ := Γ₀)
  rw [hctx', List.append_assoc] at this
  exact this

end Lean4Lean.SExpr

namespace Lean4Lean.SExpr
variable [Params]

/-- `hvar` for an iota rule (recursor paths from `hρ`, field paths by `T.field_var_le`). -/
theorem T.hvar_iota {c c' : Name} {mm nn : Nat} {g : PatGen}
    {ls : List SLevel} {us : List VLevel} {Tsc Hs : List VExpr}
    (hctx : g.ctx = (Tsc.map (·.instL us)).reverse ++ Hs.reverse) (hTsc : Tsc.length = nn)
    (hall : ∀ T ∈ Tsc, ∃ (J : Name) (vs : List VLevel), T = .const J vs ∧
      Params.classify J = some (.indTy 0))
    {N : Nat} {rf : List (WShape (N+1))} {rargs' : List (WShape N)}
    {mf : (Pattern.varN (.const c) mm).Path → TShape}
    {ma : (Pattern.varN (.const c') nn).Path → TShape}
    (hf : LE_Interp.Matches (.varN (.const c) mm) c rf mf)
    (ha : LE_Interp.Matches (.varN (.const c') nn) c' rargs' ma)
    {ρ : Valuation} (hρ : (Valuation.ofRargs (WShape.ctor' c' rargs'.reverse :: rf)).LE ρ)
    {K : Nat} {l : List (WShape (K+1))} (hl : l.length = nn)
    (hbound : ∀ (j : Nat) (s : WShape N) (t : WShape (K+1)), rargs'.reverse[j]? = some s →
      l[j]? = some t → s.T ≤ t.T) :
    ∀ (path : (Pattern.iota c mm c' nn).Path) {n} {y b : WShape n},
      y.T ≤ (Sum.elim mf ma) path → y.HasType b →
      LE_Interp (Valuation.lowerCtx ((List.zipWith (fun F li => (T.lowerF K F li).T)
          (Tsc.map (mkInst (us.map (SLevel.instV ls)))) l).reverse) ρ mm) b.T
        (mkInst ls ((g.ctx.getD ((Pattern.iota c mm c' nn).pathIdx path) (.sort .zero)).liftN
          ((Pattern.iota c mm c' nn).pathIdx path + 1))) →
      y.T ≤ Valuation.lowerCtx ((List.zipWith (fun F li => (T.lowerF K F li).T)
          (Tsc.map (mkInst (us.map (SLevel.instV ls)))) l).reverse) ρ mm
        ((Pattern.iota c mm c' nn).pathIdx path) := by
  intro path n y b hy hyb hb
  have hfl : ((List.zipWith (fun F li => (T.lowerF K F li).T)
      (Tsc.map (mkInst (us.map (SLevel.instV ls)))) l).reverse).length = nn := by
    simp [hTsc, hl]
  cases path with
  | inl x =>
    obtain ⟨lf, hxf⟩ := T.matches_varN mm hf
    obtain ⟨s, hs, he⟩ := hxf x
    have hi : (Pattern.varN (.const c) mm).pathIdx x < mm := lf ▸ (List.getElem?_eq_some_iff.1 hs).1
    simp only [Sum.elim_inl, Pattern.pathIdx_inl, Pattern.nvars_varN, Pattern.nvars,
      Nat.zero_add] at hy ⊢
    rw [show (Pattern.varN (.const c) mm).pathIdx x + nn = _ + (Pattern.varN (.const c) mm).pathIdx x
      from (Nat.add_comm _ _).trans (congrArg (· + _) hfl.symm), T.lowerCtx_rec _ _ _ _ hi]
    have := hρ ((Pattern.varN (.const c) mm).pathIdx x + 1)
    rw [Valuation.ofRargs, List.foldr_cons, Valuation.push, ← Valuation.ofRargs,
      T.ofRargs_get hs] at this
    exact (he ▸ hy).trans this
  | inr x =>
    obtain ⟨la, hxa⟩ := T.matches_varN nn ha
    obtain ⟨s, hs, he⟩ := hxa x
    simp only [Sum.elim_inr, Pattern.pathIdx_inr] at hy hb ⊢
    obtain ⟨j, hjdef⟩ : ∃ j, (Pattern.varN (.const c') nn).pathIdx x = j := ⟨_, rfl⟩
    rw [hjdef] at hb hs ⊢
    have hj : j < nn := la ▸ (List.getElem?_eq_some_iff.1 hs).1
    have hi : nn - 1 - j < Tsc.length := by omega
    obtain ⟨J, vs, hJe, hJ⟩ := hall _ (List.getElem_mem hi)
    have hctxj : g.ctx[j]? = some ((Tsc[nn - 1 - j]).instL us) := by
      rw [hctx, List.getElem?_append_left (by simp; omega),
        List.getElem?_reverse (by simp; omega), List.getElem?_map]
      simp [hTsc, List.getElem?_eq_getElem hi]
    have hgetD : g.ctx.getD j (.sort .zero) = (Tsc[nn - 1 - j]).instL us := by
      simp [List.getD_eq_getElem?_getD, hctxj]
    rw [hgetD, hJe] at hb
    simp only [VExpr.instL, VExpr.liftN] at hb
    have hF : (Tsc.map (mkInst (us.map (SLevel.instV ls))))[nn - 1 - j]? =
        some (.const J (vs.map (SLevel.instV (us.map (SLevel.instV ls))))) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hi, hJe]; rfl
    obtain ⟨t, ht⟩ : ∃ t, l[nn - 1 - j]? = some t := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hfj : ((List.zipWith (fun F li => (T.lowerF K F li).T)
        (Tsc.map (mkInst (us.map (SLevel.instV ls)))) l).reverse)[j]? =
        some (T.lowerF K (.const J (vs.map (SLevel.instV (us.map (SLevel.instV ls))))) t).T := by
      rw [List.getElem?_reverse (by simp [hTsc, hl]; omega), List.getElem?_zipWith]
      simp only [List.length_zipWith, List.length_map, hTsc, hl, Nat.min_self]
      rw [hF, ht]
    rw [T.lowerCtx_field hfj]
    have hsr : rargs'.reverse[nn - 1 - j]? = some s := by
      rw [List.getElem?_reverse (by simp [la]; omega), la,
        show nn - 1 - (nn - 1 - j) = j by omega]; exact hs
    refine T.field_var_le (ρ' := Valuation.lowerCtx ((List.zipWith (fun F li => (T.lowerF K F li).T)
      (Tsc.map (mkInst (us.map (SLevel.instV ls)))) l).reverse) ρ mm) rfl hJ
      ((he ▸ hy).trans (hbound _ s t hsr ht)) hyb ?_
    have e : mkInst ls (.const J (vs.map (·.inst us))) =
        .const J (vs.map (SLevel.instV (us.map (SLevel.instV ls)))) := by
      have := mkInst_instL (ls := ls) (us := us) (e := .const J vs)
      simp only [VExpr.instL] at this
      rw [this]; rfl
    simpa [e] using hb

end Lean4Lean.SExpr
