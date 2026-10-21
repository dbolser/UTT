import Lean4Lean.Experimental.E6.Delta
/-! E6, iota shape: syntactic plumbing (ports of `E6a/HheadSupply.lean`, with `RankParams`
replaced by the class fields), the field lowering, and the facts about constructor-field
variables (`hvar`'s field case). -/
namespace Lean4Lean.SExpr
variable [Params]

theorem T.matches_varN {h c : Name} : ∀ (j : Nat) {n : Nat} {rs : List (WShape n)}
    {mf : (Pattern.varN (.const h) j).Path → TShape},
    LE_Interp.Matches (Pattern.varN (.const h) j) c rs mf →
    rs.length = j ∧ ∀ x, ∃ s, rs[(Pattern.varN (.const h) j).pathIdx x]? = some s ∧ mf x = s.T
  | 0, n, rs, mf, H => by
    cases H with
    | const => exact ⟨rfl, fun x => x.elim⟩
  | j+1, n, rs, mf, H => by
    cases H with
    | @var _ _ _ rs' mf' a H' =>
      obtain ⟨hl, hx⟩ := T.matches_varN j H'
      refine ⟨by simp [hl], fun x => ?_⟩
      cases x with
      | none => exact ⟨a, rfl, rfl⟩
      | some y =>
        obtain ⟨s, hs, he⟩ := hx y
        refine ⟨s, ?_, he⟩
        change (a :: rs')[(Pattern.varN (.const h) j).pathIdx y + 1]? = some s
        simpa using hs

theorem T.ofRargs_get {n : Nat} : ∀ {rs : List (WShape n)} {i : Nat} {s : WShape n},
    rs[i]? = some s → Valuation.ofRargs rs i = s.T
  | _ :: _, 0, _, h => by cases h; rfl
  | _ :: rs, i+1, _, h => T.ofRargs_get (rs := rs) (i := i) (by simpa using h)

theorem T.range'_foldr (ρ : Valuation) : ∀ (m s i : Nat), i < m →
    ((List.range' s m).foldr (fun i ρ' => ρ'.push (ρ (i + 1))) Valuation.nil) i = ρ (s + i + 1)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | m+1, s, 0, _ => by simp [List.range'_succ, Valuation.push]
  | m+1, s, i+1, h => by
    rw [List.range'_succ, List.foldr_cons]
    change ((List.range' (s+1) m).foldr (fun i ρ' => Valuation.push ρ' (ρ (i + 1))) Valuation.nil) i = _
    rw [T.range'_foldr ρ m (s+1) i (by omega)]; congr 1; omega

theorem T.lowerCtx_rec (fields : List TShape) (ρ : Valuation) (m i : Nat) (hi : i < m) :
    Valuation.lowerCtx fields ρ m (fields.length + i) = ρ (i + 1) := by
  rw [Valuation.lowerCtx, T.foldr_push_add, List.range_eq_range']
  rw [T.range'_foldr ρ m 0 i hi]; congr 1; omega

theorem T.lowerCtx_field {fields : List TShape} {ρ : Valuation} {m j : Nat} {s : TShape}
    (h : fields[j]? = some s) : Valuation.lowerCtx fields ρ m j = s :=
  T.foldr_push_lt _ fields j s h

omit [Params] in
theorem T.foldr_forallE_inj' : ∀ {Ts Ts' : List VExpr} {X Y : VExpr},
    (∀ A B, X ≠ .forallE A B) → (∀ A B, Y ≠ .forallE A B) →
    Ts.foldr .forallE X = Ts'.foldr .forallE Y → Ts = Ts'
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, hX, _, h => absurd h (hX _ _)
  | _ :: _, [], _, _, _, hY, h => absurd h.symm (hY _ _)
  | _ :: _, _ :: _, _, _, hX, hY, h => by
    simp only [List.foldr_cons, VExpr.forallE.injEq] at h
    rw [h.1, T.foldr_forallE_inj' hX hY h.2]

omit [Params] in
theorem T.foldr_app_ne_forallE (I : Name) (ls : List VLevel) : ∀ (args : List VExpr) A B,
    args.foldr (fun (A acc : VExpr) => acc.app A) (.const I ls) ≠ .forallE A B
  | [], _, _, h => by cases h
  | _ :: _, _, _, h => by cases h

/-- `SExpr` telescope injectivity at equal lengths. -/
theorem T.foldr_forallE_injS : ∀ {Ts Ts' : List SExpr} {B B' : SExpr}, Ts.length = Ts'.length →
    Ts.foldr .forallE B = Ts'.foldr .forallE B' → Ts = Ts' ∧ B = B'
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | A :: Ts, A' :: Ts', _, _, hl, h => by
    simp only [List.foldr_cons, SExpr.forallE.injEq] at h
    obtain ⟨h1, h2⟩ := T.foldr_forallE_injS (by simpa using hl) h.2
    exact ⟨by rw [h.1, h1], h2⟩

/-- `hhead`, from the iota leaf's data only (`HheadSupply.lean: V.hhead_supply`). -/
theorem T.hhead_supply {rec c' : Name} {mm k : Nat}
    {r : (Pattern.iota rec mm c' k).RHS} {g : PatGen}
    (hg : Pattern.gen Params.env Params.rank Params.classify (.iota rec mm c' k) r = some g)
    {n : Nat} {rargs : List (WShape n)} {m2 : (Pattern.iota rec mm c' k).Path → TShape}
    (hMt : LE_Interp.Matches (.iota rec mm c' k) rec rargs m2)
    {ρ : Valuation} (hρ : (Valuation.ofRargs rargs).LE ρ)
    {fields : List TShape} (hm : g.ctx.length = fields.length + mm) :
    ∀ path, m2 path ≤ Valuation.lowerCtx fields ρ mm ((Pattern.iota rec mm c' k).pathIdx path) ∨
      ∃ (I' : Name) (us : List VLevel) (k' : Nat),
        g.ctx[(Pattern.iota rec mm c' k).pathIdx path]? = some (.const I' us) ∧
        Params.classify I' = some (.indTy k') := by
  obtain ⟨⟨ci, hci⟩, -⟩ := T.gen_head_ctx hg
  obtain ⟨Hs, I, us, Bmaj, hHs, -, ci', I', Ts, args, hci', hcl, hTs, -, e3, hctx⟩ :=
    Pattern.gen_head_ctor hg (by rw [← Pattern.head_varN rec mm]; exact hci)
  have hfl : fields.length = k := by
    rw [hctx] at hm; simp [hHs, hTs] at hm; omega
  intro path
  cases hMt with
  | app hf ha =>
    obtain ⟨lf, hxf⟩ := T.matches_varN mm hf
    obtain ⟨la, hxa⟩ := T.matches_varN k ha
    cases path with
    | inl x =>
      left
      obtain ⟨s, hs, he⟩ := hxf x
      have hi : (Pattern.varN (.const rec) mm).pathIdx x < mm :=
        lf ▸ (List.getElem?_eq_some_iff.1 hs).1
      simp only [Sum.elim_inl, Pattern.pathIdx_inl, Pattern.nvars_varN, Pattern.nvars]
      rw [he, Nat.zero_add, show (Pattern.varN (.const rec) mm).pathIdx x + k =
        fields.length + (Pattern.varN (.const rec) mm).pathIdx x by omega, T.lowerCtx_rec _ _ _ _ hi]
      have := hρ ((Pattern.varN (.const rec) mm).pathIdx x + 1)
      rwa [Valuation.ofRargs, List.foldr_cons, Valuation.push, ← Valuation.ofRargs,
        T.ofRargs_get hs] at this
    | inr x =>
      right
      obtain ⟨s, hs, -⟩ := hxa x
      have hi : (Pattern.varN (.const c') k).pathIdx x < k :=
        la ▸ (List.getElem?_eq_some_iff.1 hs).1
      obtain ⟨I'', Ts', e4, hall⟩ := Params.ctor_fields_closed (cl := .ctor k) rfl hcl hci'
      have hT : Ts = Ts' := T.foldr_forallE_inj' (T.foldr_app_ne_forallE _ _ args)
        (fun _ _ h => by cases h) (e3.symm.trans e4)
      subst hT
      simp only [Pattern.pathIdx_inr]
      rw [hctx, List.getElem?_append_left (by simp [hTs]; exact hi)]
      have hi' : (Pattern.varN (.const c') k).pathIdx x < Ts.length := hTs ▸ hi
      rw [List.getElem?_reverse (by simpa using hi'), List.getElem?_map]
      have hlt : Ts.length - 1 - (Pattern.varN (.const c') k).pathIdx x < Ts.length := by omega
      rw [List.getElem?_eq_getElem (by simpa using hlt)]
      obtain ⟨J, vs, hJ, hcJ⟩ := hall _ (List.getElem_mem (by simpa using hlt))
      refine ⟨J, vs.map (·.inst us), 0, ?_, hcJ⟩
      simp [hJ, VExpr.instL]

/-! ### Interpretations of a closed inductive-type constant -/

theorem T.indTy_T_le {a b : Nat} : (WShape.indTy (n := a)).T ≤ (WShape.indTy (n := b)).T := by
  show WShape.LE _ _
  simp only [WShape.T]
  rw [Nat.succ_max_succ, WShape.lift_indTy, WShape.lift_indTy]; exact WShape.LE.rfl

/-- An inductive type constant (arity 0) is interpreted below `indTy`. -/
theorem T.interp_indTy_le {ρ : Valuation} {b : TShape} {I : Name} {ls : List SLevel}
    (hI : Params.classify I = some (.indTy 0)) (H : LE_Interp ρ b (.const I ls)) :
    b ≤ (WShape.indTy (n := 0)).T := by
  generalize eC : SExpr.const I ls = M at H
  cases H with
  | bot => exact TShape.bot_le'
  | bvar | sort | app | lam | forallE => cases eC
  | const h1 h2 h3 h4 h5 h6 h7 =>
    injection eC with e1 e2; subst e1 e2
    refine h3.trans ?_
    cases h6 with
    | bot => exact TShape.bot_le'
    | @lam f _ _ he m_le =>
      by_cases hf : f.NonZero
      · obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf
        have := LE_Interp.Const.compat_mismatch (rargs2 := []) (by simp)
          (he _ t (WShapeFun.mem_val hxy)) (.inr (.inl hI))
        cases hn <| WShape.LE.T_iff.1 <| this.trans TShape.bot_eqv.2
      · have := WShape.lam'_le_lam'.2 <| NonZero.not_iff.1 hf
        exact m_le.trans <| (WShape.lam'_bot ▸ this).T.trans TShape.bot_le'
    | ctor hc => cases hI.symm.trans hc
    | indTy _ hle => exact hle.trans T.indTy_T_le
    | pat hP hM => cases hI.symm.trans (pat_arity hP hM.arity)

end Lean4Lean.SExpr

namespace Lean4Lean.SExpr
variable [Params]

/-! ### The field lowering (PLAN D4 step 1, E6a option (a)) -/

open Classical in
/-- The type shape of a lowered field entry: `indTy` when the (closed) field type admits it. -/
noncomputable def T.lowerA (K : Nat) (F : SExpr) : WShape (K+1) :=
  if LE_Interp .nil (WShape.indTy (n := K)).T F then .indTy else .bot

open Classical in
/-- The lowered field entry: the clause's field shape when it is typed at `indTy` and the
field type admits `indTy`, else `⊥`. -/
noncomputable def T.lowerF (K : Nat) (F : SExpr) (l : WShape (K+1)) : WShape (K+1) :=
  if l.HasType .indTy ∧ LE_Interp .nil (WShape.indTy (n := K)).T F then l else .bot

theorem T.lowerA_type {K : Nat} {F : SExpr} : (T.lowerA K F).HasType .type := by
  unfold T.lowerA; split
  · exact .indTy
  · exact .bot' .sort

theorem T.lowerF_has {K : Nat} {F : SExpr} {l : WShape (K+1)} :
    (T.lowerF K F l).HasType (T.lowerA K F) := by
  unfold T.lowerF T.lowerA; split
  · next h => rw [if_pos h.2]; exact h.1
  · exact .bot' T.lowerA_type

theorem T.lowerA_interp {K : Nat} {F : SExpr} (hcl : F.ClosedN) {ρ : Valuation} :
    LE_Interp ρ (T.lowerA K F).T F := by
  unfold T.lowerA; split
  · next h => exact (LE_Interp.closed_iff hcl).1 h
  · exact .bot

theorem T.lowerF_le {K : Nat} {F : SExpr} {l : WShape (K+1)} : T.lowerF K F l ≤ l := by
  unfold T.lowerF; split
  · exact WShape.LE.rfl
  · exact WShape.bot_le

theorem T.lowerF_defeq {Γ₀ : List SExpr} {K : Nat} {F X Y : SExpr} {l : WShape (K+1)}
    (H : LRS.FieldRel (LR Γ₀ (n := K+1)) X Y F l) :
    (LR Γ₀).DefEq X Y F (T.lowerF K F l) (T.lowerA K F) := by
  unfold T.lowerF T.lowerA; split
  · next h => rw [if_pos h.2]; exact H l WShape.LE.rfl h.1
  · exact (LR _).bot T.lowerA_type

theorem T.sort_not_le_indTy {r : Bool} :
    ¬(WShape.sort (n := n) r).T ≤ (WShape.indTy : WShape (n'+1)).T := by
  intro h
  rw [TShape.LE.def (Nat.le_max_left n (n'+1)) (Nat.le_max_right n (n'+1))] at h
  obtain ⟨M, hM⟩ : ∃ M, max n (n'+1) = M + 1 := ⟨max n (n'+1) - 1, by omega⟩
  simp only [WShape.T] at h
  rw [hM, WShape.lift_sort, WShape.lift_indTy, WShape.le_indTy] at h
  rcases h with h | h <;> cases congrArg (·.1) h

/-- A typed shape at an inductive type below a field shape is below its lowering. -/
theorem T.field_var_le {K : Nat} {F : SExpr} {l : WShape (K+1)} {J : Name} {vs : List SLevel}
    (hF : F = .const J vs) (hJ : Params.classify J = some (.indTy 0))
    {n : Nat} {y b : WShape n} {ρ' : Valuation}
    (hy : y.T ≤ l.T) (hyb : y.HasType b) (hb : LE_Interp ρ' b.T F) :
    y.T ≤ (T.lowerF K F l).T := by
  subst hF
  have hbI := T.interp_indTy_le hJ hb
  cases hyb.unfold with
  | bot => exact TShape.bot_le'
  | sort => exact absurd hbI T.sort_not_le_indTy
  | forallE => exact absurd hbI T.sort_not_le_indTy
  | lam => exact absurd hbI T.forallE_not_le_indTy
  | indTy => exact absurd hbI T.sort_not_le_indTy
  | @ctor n₀ c l' wf =>
    have hI : LE_Interp .nil (WShape.indTy (n := K)).T (.const J vs) :=
      ((LE_Interp.closed_iff (M := .const J vs) trivial).1 hb).mono T.indTy_T_le
    have hl : l.HasType .indTy := by
      have le₁ := Nat.le_max_left (n₀+1) (K+1); have le₂ := Nat.le_max_right (n₀+1) (K+1)
      rw [TShape.LE.def le₁ le₂] at hy
      obtain ⟨M, hM⟩ : ∃ M, max (n₀+1) (K+1) = M + 1 := ⟨max n₀ K, by omega⟩
      simp only [WShape.T] at hy
      rw [hM, WShape.lift_ctor (by omega)] at hy
      obtain ⟨l'', h'', he, -⟩ := WShape.ctor_le.1 hy
      have hv := congrArg (·.1) he
      simp only [WShape.lift_val (show K+1 ≤ M+1 by omega)] at hv
      cases l using WShape.casesOn' with
      | ctor => exact WShape.HasType.ctor
      | _ => first
        | (cases hv; done)
        | (simp [WShape.bot, WShape.sort, WShape.forallE, WShape.lam, WShape.indTy,
            WShape.ctor, Shape.lift] at hv; done)
        | (simp [WShape.bot, WShape.sort, WShape.forallE, WShape.lam, WShape.indTy,
            WShape.ctor, Shape.lift] at hv; cases hv)
    unfold T.lowerF; rw [if_pos ⟨hl, hI⟩]; exact hy

end Lean4Lean.SExpr
