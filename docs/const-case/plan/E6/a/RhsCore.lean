import Lean4Lean.Experimental.E6.Helpers
/-! E6: the RHS part of the pattern leaf shared by the iota and delta rules (`T.rhs_core`). -/
namespace Lean4Lean.SExpr
variable [Params]

theorem T.foldr_cons_lt {α : Type} (f : α → SExpr) (σ : Subst) :
    ∀ (xs : List α) (j : Nat) (x : α), xs[j]? = some x →
      (xs.foldr (fun e τ => τ.cons (f e)) σ) j = f x
  | [], _, _, h => by simp at h
  | y :: xs, 0, x, h => by simp at h; subst h; rfl
  | y :: xs, j+1, x, h => T.foldr_cons_lt f σ xs j x (by simpa using h)

theorem T.foldr_cons_add {α : Type} (f : α → SExpr) (σ : Subst) :
    ∀ (xs : List α) (i : Nat), (xs.foldr (fun e τ => τ.cons (f e)) σ) (xs.length + i) = σ i
  | [], i => by simp
  | y :: xs, i => by
    rw [List.length_cons, Nat.add_right_comm]; exact T.foldr_cons_add f σ xs i

theorem T.liftK_subst_foldr {α : Type} (f : α → SExpr) (σ : Subst) (e : SExpr) :
    ∀ (xs : List α), (liftK e xs.length).subst (xs.foldr (fun e τ => τ.cons (f e)) σ) = e.subst σ
  | [] => rfl
  | y :: xs => by
    rw [List.length_cons, liftK, List.foldr_cons, lift_subst_cons]
    exact T.liftK_subst_foldr f σ e xs


theorem T.le_of_eq' {a b : TShape} (h : a = b) : a ≤ b := h ▸ .rfl

/-- The shared RHS part of the pattern leaf (D4 steps 1-4): given the pattern-context part `Wc`
of `W_p` (over `lowerCtx`), push the self entries (`T.rhs_lower2`'s `selfs`), interpret the RHS
shape at `ρ_low`, take a typed pair `(y, b)` above it by soundness, and apply the WF IH to the
RHS typing (`EnvStrongR.rhs`); rewrite with (c) `gen_rhsAbs`. -/
theorem T.rhs_core {Γ₀ : List SExpr} {k : Nat} {ρ₀ : Valuation}
    (WFIH : LR.WFIH Params.rank Γ₀ k) {c : Name} {ci : VConstant} {ls : List SLevel}
    (hc : Params.rank c < k) (h1 : Params.env.constants c = some ci)
    {R : TShape → SExpr → Prop} (LIH : LR.LocalIH Params.rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e)
    {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} {mC : TShape}
    (hP : Params.Pat p r) (hMt : LE_Interp.Matches p c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1)
    (g : PatGen) (hg : Pattern.gen Params.env Params.rank Params.classify p r.1 = some g)
    {fields : List TShape} {ρ : Valuation} {mm : Nat} (hm : g.ctx.length = fields.length + mm)
    {σc σc' : Subst}
    (Wc : LR.SubstWF Γ₀ σc σc' (g.ctx.map (mkInst ls) ++ Γ₀) (Valuation.lowerCtx fields ρ mm))
    (hvar : ∀ path {n} {y b : WShape n}, y.T ≤ m2 path → y.HasType b →
      LE_Interp (Valuation.lowerCtx fields ρ mm) b.T
        (SExpr.mkInst ls ((g.ctx.getD (p.pathIdx path) (.sort .zero)).liftN (p.pathIdx path + 1))) →
      y.T ≤ Valuation.lowerCtx fields ρ mm (p.pathIdx path))
    (hhead : ∀ path, m2 path ≤ Valuation.lowerCtx fields ρ mm (p.pathIdx path) ∨
      ∃ (I' : Name) (us : List VLevel) (k : Nat), g.ctx[p.pathIdx path]? = some (.const I' us) ∧
        Params.classify I' = some (.indTy k))
    {s : TShape}
    (hroot : (s ≤ mC ∧
        ∀ path, r.1 = .var path → m2 path ≤ Valuation.lowerCtx fields ρ mm (p.pathIdx path)) ∨
      ∃ path, r.1 = .var path ∧ s ≤ Valuation.lowerCtx fields ρ mm (p.pathIdx path)) :
    ∃ (n' : Nat) (y b : WShape n'), s ≤ y.T ∧ y.HasType b ∧
      LE_Interp (Valuation.lowerCtx fields ρ mm) b.T (mkInst ls g.type) ∧
      (LR Γ₀).DefEq (r.1.applyS ls fun path => σc (p.pathIdx path))
        (r.1.applyS ls fun path => σc' (p.pathIdx path)) ((mkInst ls g.type).subst σc) y b := by
  have hhd : p.head = c := T.matches_head hMt
  have h1' : Params.env.constants p.head = some ci := hhd ▸ h1
  obtain ⟨selfs, hslen, hfacts, -, hroot'⟩ :=
    T.rhs_lower2 LIH hR hP hMt hRHS g hg hm Wc.fits hvar hhead
  have hgs := Pattern.gen_self hg
  obtain ⟨es, hes_def⟩ : ∃ es : List (SExpr × SExpr × SExpr × TShape), es =
      ((g.self.zip (r.1.selfLeaves (Pattern.sameRank Params.rank p.head))).zip selfs).map
        fun x => (mkInst ls x.1.1, mkInst ls x.1.2, mkInst ls x.1.2, x.2) := ⟨_, rfl⟩
  have hes : ∀ (j : Nat) (e : SExpr × SExpr × SExpr × TShape), es[j]? = some e →
      ∃ (S el : VExpr) (s : TShape), g.self[j]? = some S ∧
      (r.1.selfLeaves (Pattern.sameRank Params.rank p.head))[j]? = some el ∧ selfs[j]? = some s ∧
      e = (mkInst ls S, mkInst ls el, mkInst ls el, s) := by
    intro j e he
    simp only [hes_def, List.getElem?_map, List.getElem?_zip_eq_some, Option.map_eq_some_iff] at he
    obtain ⟨⟨⟨S, el⟩, s⟩, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ := he
    exact ⟨S, el, s, h1, h2, h3, rfl⟩
  have hesl : es.length = g.self.length := by
    simp only [hes_def, List.length_map, List.length_zip, hslen, ← hgs.1, Nat.min_self]
  have hes1 : es.map (·.1) = g.self.map (mkInst ls) := by
    apply List.ext_getElem (by simp [hesl])
    intro j hj1 hj2
    simp only [List.getElem_map]
    have hj : j < es.length := by simpa using hj1
    obtain ⟨S, el, s, h1, -, -, he⟩ := hes j (es[j]'hj) (List.getElem?_eq_getElem hj)
    rw [he]; dsimp only
    rw [List.getElem?_eq_getElem (by simpa using hj2)] at h1
    cases h1; rfl
  have hes4 : es.map (·.2.2.2) = selfs := by
    apply List.ext_getElem (by simp [hesl, hslen])
    intro j hj1 hj2
    simp only [List.getElem_map]
    have hj : j < es.length := by simpa using hj1
    obtain ⟨S, el, s, -, -, h3, he⟩ := hes j (es[j]'hj) (List.getElem?_eq_getElem hj)
    rw [he]; dsimp only
    rw [List.getElem?_eq_getElem hj2] at h3
    cases h3; rfl
  -- the self entries satisfy `T.substWF_push`'s conditions
  have hcond : ∀ (j : Nat) (e : SExpr × SExpr × SExpr × TShape), es[j]? = some e → e.1.ClosedN ∧
      (∃ u, IsDefEqStrong (Params.env.below Params.rank (Params.rank c))
        ((es.drop (j+1)).map (·.1) ++ (g.ctx.map (mkInst ls) ++ Γ₀)) e.1 e.1 (.sort u)) ∧
      ∃ (n : Nat) (a₁ q : WShape n), e.2.2.2 = q.T ∧ q.HasType a₁ ∧ LE_Interp .nil a₁.T e.1 ∧
        Γ₀ ⊢ e.2.1 ≡ e.2.2.1 : e.1 ∧ (LR Γ₀).DefEq e.2.1 e.2.2.1 e.1 q a₁ := by
    intro j e he
    obtain ⟨S, el, s, hS, hel, hs, rfl⟩ := hes j e he
    obtain ⟨c', us, ci', hel', -, hci', hlen', hty, ⟨kk, x, b, rfl, hxb, hb⟩, hcg, -⟩ :=
      hfacts j s hs
    cases hel.symm.trans hel'
    have hgetD : g.self.getD j (.sort .zero) = S := by simp [List.getD_eq_getElem?_getD, hS]
    rw [hgetD] at hty
    dsimp only
    have hcl : (mkInst ls S).ClosedN := hty ▸ (Params.henv.closedC hci').mkInstS
    refine ⟨hcl, ?_, ?_⟩
    · have hj : j < g.self.length := (List.getElem?_eq_some_iff.1 hS).1
      obtain ⟨u, Hu⟩ := EnvStrongR.of_params.ctx ls hP hg h1' j S
        (by rw [List.getElem?_append_left hj]; exact hS)
      refine ⟨u, ?_⟩
      have hctx : ((g.self ++ g.ctx).drop (j + 1)).map (mkInst ls) ++ Γ₀ =
          (es.drop (j+1)).map (·.1) ++ (g.ctx.map (mkInst ls) ++ Γ₀) := by
        rw [List.drop_append_of_le_length (by omega), List.map_drop, hes1]
        simp [List.map_drop]
      rw [← hctx, ← hhd]; exact Hu.weak_append
    · refine ⟨kk, b, x, rfl, hxb, ?_, ?_, ?_⟩
      · rw [hty]; exact (LE_Interp.closed_iff (Params.henv.closedC hci').mkInstS).1 hb
      · rw [hty]
        exact IsDefEq.const hci' (by simpa using hlen')
      · rw [hty]
        rcases hcg with ⟨n0, he0⟩ | ⟨n0, m', a', hle, -, -, H⟩
        · obtain ⟨rfl, hx⟩ := Sigma.mk.inj he0
          cases eq_of_heq hx
          exact (LR Γ₀).bot hxb.isType
        · exact H x b hle (by simpa using hb) hxb
  have Wp := T.substWF_push WFIH hc Wc es hcond
  rw [← List.append_assoc, hes1, ← List.map_append] at Wp
  rw [show es.foldr (fun e ρ' => Valuation.push ρ' e.2.2.2) (Valuation.lowerCtx fields ρ mm) =
      Valuation.lower selfs fields ρ mm by
    rw [Valuation.lower, ← hes4, List.foldr_map]] at Wp
  -- the RHS shape is interpreted at ρ_low; soundness gives a typed pair above it
  have hrootI : LE_Interp (Valuation.lower selfs fields ρ mm) s (mkInst ls g.rhsAbs) := by
    rcases hroot with ⟨hs, hr⟩ | ⟨path, hr, hs⟩
    · exact (hroot' hr).mono hs
    · rw [(Pattern.gen_eq_some hg).2.2.2, hr]
      refine .bvar (hs.trans (le_of_eq' ?_))
      rw [Valuation.lower, ← hslen]; exact (T.foldr_push_add _ selfs _).symm
  have Hr := (EnvStrongR.of_params.rhs ls hP hg h1').weak_append (Γ₀ := Γ₀)
  rw [hhd] at Hr
  obtain ⟨n', y, b, -, hle, hy, hb, hyb⟩ :=
    ((LE_Interp.soundSE (Params.env.below_le ..) Hr Wp.fits).2 hrootI).out
  have Ad := WFIH _ hc Hr hy hb hyb
  have D := (Ad.1 Wp).1
  -- rewrite with (c) `gen_rhsAbs` and the self/lift bookkeeping
  have hself : ∀ (σ0 : Subst) (j : Nat) (e : VExpr),
      (r.1.selfLeaves (Pattern.sameRank Params.rank p.head))[j]? = some e →
      (es.foldr (fun e τ => τ.cons e.2.1) σ0) j = mkInst ls e := by
    intro σ0 j e he
    have hj : j < es.length := by
      rw [hesl, hgs.1]; exact (List.getElem?_eq_some_iff.1 he).1
    obtain ⟨S, el, s, -, hel, -, hesj⟩ := hes j es[j] (List.getElem?_eq_getElem hj)
    rw [T.foldr_cons_lt (·.2.1) σ0 es j es[j] (List.getElem?_eq_getElem hj), hesj]
    cases hel.symm.trans he; rfl
  have hself' : ∀ (σ0 : Subst) (j : Nat) (e : VExpr),
      (r.1.selfLeaves (Pattern.sameRank Params.rank p.head))[j]? = some e →
      (es.foldr (fun e τ => τ.cons e.2.2.1) σ0) j = mkInst ls e := by
    intro σ0 j e he
    have hj : j < es.length := by
      rw [hesl, hgs.1]; exact (List.getElem?_eq_some_iff.1 he).1
    obtain ⟨S, el, s, -, hel, -, hesj⟩ := hes j es[j] (List.getElem?_eq_getElem hj)
    rw [T.foldr_cons_lt (·.2.2.1) σ0 es j es[j] (List.getElem?_eq_getElem hj), hesj]
    cases hel.symm.trans he; rfl
  rw [Pattern.gen_rhsAbs hg ls (fun path => σc (p.pathIdx path)) _ (hself σc) (fun path => by
      rw [← hesl]; exact T.foldr_cons_add (·.2.1) σc es _),
    Pattern.gen_rhsAbs hg ls (fun path => σc' (p.pathIdx path)) _ (hself' σc') (fun path => by
      rw [← hesl]; exact T.foldr_cons_add (·.2.2.1) σc' es _),
    T.mkInst_liftN, ← hesl, T.liftK_subst_foldr] at D
  refine ⟨n', y, b, hle, hyb, ?_, D⟩
  rw [T.mkInst_liftN, ← hslen] at hb
  exact (T.LE_Interp_foldr_push_liftK selfs).1 hb

end Lean4Lean.SExpr
