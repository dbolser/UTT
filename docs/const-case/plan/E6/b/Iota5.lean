import Lean4Lean.Experimental.E6.Iota4
/-! E6, iota shape: substitution algebra for `g.type` and the typed head reduction of the goal's
sides to the RHS instance (D4 step 5). -/
namespace Lean4Lean.SExpr
variable [Params]

theorem T.liftK_subst (e : SExpr) : ∀ (j : Nat) (σ : Subst),
    (liftK e j).subst σ = e.subst (fun i => σ (i + j))
  | 0, σ => rfl
  | j+1, σ => by
    rw [liftK, lift_subst, T.liftK_subst e j]; rfl

/-- `g.type`'s instance under the pattern substitution is `B` at the substitution with the major
replaced by the constructor spine (D4 step 6). -/
theorem T.type_subst {ls : List SLevel} {Bmaj Z : VExpr} {nn : Nat} {σc τ : Subst} {Z'' : SExpr}
    (hshift : ∀ i, σc (nn + i) = τ i) (hZ : (mkInst ls Z).subst σc = Z'') :
    (mkInst ls ((Bmaj.liftN nn 1).inst Z)).subst σc = (mkInst ls Bmaj).subst (τ.cons Z'') := by
  rw [T.mkInst_inst, T.mkInst_liftN1, subst_inst, subst_lift', hZ]
  have : Subst.lift_l (.consN (.skipN .refl nn) 1) σc.lift = τ.lift := by
    funext i; cases i with
    | zero => rfl
    | succ j =>
      simp only [Subst.lift_l, Lift.consN, Lift.liftVar, Lift.liftVar_skipN, Subst.lift]
      rw [Nat.add_comm j nn, hshift]
  rw [this, inst_lift_cons]

theorem T.subst_cons_head_tail (σ : Subst) : σ.tail.cons (σ 0) = σ := by
  funext i; cases i <;> rfl

/-- The typed head reduction of one side of the goal (D4 step 5): the goal side reduces to the
recursor applied to the constructor spine (`appDF` with the clause's typed equation, untyped by
`WHRedS.major`), which reduces to the RHS instance (`pat_defeq` instantiated along the pattern
substitution, untyped by `extra`). -/
theorem T.iota_typed_red {Γ₀ : List SExpr} (hΓ₀ : ⊢ Γ₀) {c c' : Name} {mm nn : Nat}
    {r : (Pattern.iota c mm c' nn).RHS × (Pattern.iota c mm c' nn).Check} {g : PatGen}
    (hP : Params.Pat (.iota c mm c' nn) r) (hchk : r.2 = .true)
    (hg : Pattern.gen Params.env Params.rank Params.classify (.iota c mm c' nn) r.1 = some g)
    {ci : VConstant} (h1 : Params.env.constants c = some ci) {ls : List SLevel}
    (h2 : ls.length = ci.uvars) {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr}
    (hHs : Hs.length = mm) (hTc : ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj))
    (hdefS : g.ctx.map (mkInst ls) ++ Γ₀ ⊢ mkInst ls g.lhs ≡ mkInst ls g.rhs : mkInst ls g.type)
    {τ τc : Subst} {Xs : List SExpr}
    (WH : Ctx.SubstEq Γ₀ τ.tail τ.tail ((Hs.map (mkInst ls)).reverse ++ Γ₀))
    (hx : TWHRedS Γ₀ (τ 0) (spine (.const c' (us.map (SLevel.instV ls))) Xs)
      (.const I (us.map (SLevel.instV ls))))
    (Wc : Ctx.SubstEq Γ₀ τc τc (g.ctx.map (mkInst ls) ++ Γ₀))
    (hτc1 : ∀ i, τc (nn + i) = τ (i+1)) (hτc2 : (List.range nn).reverse.map τc = Xs) :
    (Γ₀ ⊢ (openSpine c ls (mm+1)).subst τ ≡
      .app (spine (.const c ls) ((List.range mm).reverse.map τ.tail))
        (spine (.const c' (us.map (SLevel.instV ls))) Xs) : (mkInst ls Bmaj).subst τ) ∧
    (Γ₀ ⊢ .app (spine (.const c ls) ((List.range mm).reverse.map τ.tail))
        (spine (.const c' (us.map (SLevel.instV ls))) Xs) ≡
      r.1.applyS ls (fun path => τc ((Pattern.iota c mm c' nn).pathIdx path)) :
      (mkInst ls Bmaj).subst (τ.tail.cons (spine (.const c' (us.map (SLevel.instV ls))) Xs))) ∧
    (Γ₀ ⊢ (openSpine c ls (mm+1)).subst τ ⤳*
      r.1.applyS ls (fun path => τc ((Pattern.iota c mm c' nn).pathIdx path))) := by
  have hDcl : (SExpr.const I (us.map (SLevel.instV ls))).ClosedN := trivial
  have hopen : (openSpine c ls (mm+1)).subst τ =
      .app (spine (.const c ls) ((List.range mm).reverse.map τ.tail)) (τ 0) := by
    rw [openSpine_subst, T.range_reverse_succ, List.map_append, List.map_map, List.map_singleton,
      spine_snoc]; rfl
  have hτc' : (fun i => τc (nn + i)) = τ.tail := funext hτc1
  -- (a) the recursor spine is typed by the major Π, then `appDF` with the clause's equation
  have hT' : mkInst ls ci.type =
      (Hs.map (mkInst ls)).foldr .forallE (.forallE (.const I (us.map (SLevel.instV ls)))
        (mkInst ls Bmaj)) := by
    rw [hTc, mkInst_foldr_forallE]; rfl
  have hconst : Γ₀ ⊢ .const c ls : mkInst ls ci.type := IsDefEq.const h1 h2
  rw [hT'] at hconst
  have hrec := T.openSpine_typing hconst
  rw [T.liftK_const, List.length_map, hHs] at hrec
  have hrecσ := IsDefEq.subst hΓ₀ WH hrec
  simp only [SExpr.subst] at hrecσ
  rw [spine_subst] at hrecσ
  simp only [List.map_map, Function.comp_def, SExpr.subst] at hrecσ
  have ha := IsDefEq.appDF hrecσ hx.1
  rw [inst_lift_cons, T.subst_cons_head_tail] at ha
  -- (b) `pat_defeq` along the pattern substitution
  have hb := IsDefEq.subst hΓ₀ Wc hdefS
  rw [Pattern.gen_lhs_subst hg h1 hHs hTc h2 τc, hτc', hτc2,
    Pattern.gen_rhs hg ls (fun path => τc ((Pattern.iota c mm c' nn).pathIdx path)) τc
      (fun _ => rfl),
    Pattern.gen_type hg h1 hHs hTc,
    T.type_subst (Z'' := spine (.const c' (us.map (SLevel.instV ls))) Xs) hτc1
      (by rw [mkInst_bvarSpine, spine_subst, ← hτc2]; simp [List.map_map,
        Function.comp_def, SExpr.subst, mkInst])] at hb
  refine ⟨?_, hb, ?_⟩
  · rw [hopen]; exact ha
  -- (c) the untyped chain
  have hM1 := T.matchesS_varN (c := c) (ls := ls) mm τ.tail
  have hM2 := T.matchesS_varN (c := c') (ls := us.map (SLevel.instV ls)) nn τc
  rw [hτc2] at hM2
  have hmaj : IsMajorPremise (spine (.const c ls) ((List.range mm).reverse.map τ.tail)) :=
    IsMajorPremise.mk hP hM1
  rw [hopen]
  refine .tail (WHRedS.major hmaj hx.2) (T.extra_true hP hchk ((hM1.app hM2).congr fun path => ?_))
  cases path with
  | inl x =>
    simp only [Sum.elim_inl, Pattern.pathIdx_inl, Pattern.nvars_varN, Pattern.nvars, Nat.zero_add]
    rw [Nat.add_comm, hτc1]; rfl
  | inr x => rfl

end Lean4Lean.SExpr
