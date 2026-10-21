import Lean4Lean.Experimental.E6a.FieldLower
/-! Verifier: `hhead` of `LR.rhs_lower` is supplied by the pattern leaf's own data
(`hMt`, the spine lemma's `hρ`, `hg`, `RankParams`), for every iota rule. -/
namespace Lean4Lean.SExpr
variable [Params]

theorem V.matches_varN {h c : Name} : ∀ (j : Nat) {n : Nat} {rs : List (WShape n)}
    {mf : (Pattern.varN (.const h) j).Path → TShape},
    LE_Interp.Matches (Pattern.varN (.const h) j) c rs mf →
    rs.length = j ∧ ∀ x, ∃ s, rs[(Pattern.varN (.const h) j).pathIdx x]? = some s ∧ mf x = s.T
  | 0, n, rs, mf, H => by
    cases H with
    | const => exact ⟨rfl, fun x => x.elim⟩
  | j+1, n, rs, mf, H => by
    cases H with
    | @var _ _ _ rs' mf' a H' =>
      obtain ⟨hl, hx⟩ := V.matches_varN j H'
      refine ⟨by simp [hl], fun x => ?_⟩
      cases x with
      | none => exact ⟨a, rfl, rfl⟩
      | some y =>
        obtain ⟨s, hs, he⟩ := hx y
        refine ⟨s, ?_, he⟩
        change (a :: rs')[(Pattern.varN (.const h) j).pathIdx y + 1]? = some s
        simpa using hs

theorem V.ofRargs_get {n : Nat} : ∀ {rs : List (WShape n)} {i : Nat} {s : WShape n},
    rs[i]? = some s → Valuation.ofRargs rs i = s.T
  | _ :: _, 0, _, h => by cases h; rfl
  | _ :: rs, i+1, _, h => V.ofRargs_get (rs := rs) (i := i) (by simpa using h)

theorem V.range'_foldr (ρ : Valuation) : ∀ (m s i : Nat), i < m →
    ((List.range' s m).foldr (fun i ρ' => ρ'.push (ρ (i + 1))) Valuation.nil) i = ρ (s + i + 1)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | m+1, s, 0, _ => by simp [List.range'_succ, Valuation.push]
  | m+1, s, i+1, h => by
    rw [List.range'_succ, List.foldr_cons]
    change ((List.range' (s+1) m).foldr (fun i ρ' => Valuation.push ρ' (ρ (i + 1))) Valuation.nil) i = _
    rw [V.range'_foldr ρ m (s+1) i (by omega)]; congr 1; omega

theorem V.lowerCtx_rec (fields : List TShape) (ρ : Valuation) (m i : Nat) (hi : i < m) :
    Valuation.lowerCtx fields ρ m (fields.length + i) = ρ (i + 1) := by
  rw [Valuation.lowerCtx, T.foldr_push_add, List.range_eq_range']
  rw [V.range'_foldr ρ m 0 i hi]; congr 1; omega

theorem V.foldr_forallE_inj' : ∀ {Ts Ts' : List VExpr} {X Y : VExpr},
    (∀ A B, X ≠ .forallE A B) → (∀ A B, Y ≠ .forallE A B) →
    Ts.foldr .forallE X = Ts'.foldr .forallE Y → Ts = Ts'
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, hX, _, h => absurd h (hX _ _)
  | _ :: _, [], _, _, _, hY, h => absurd h.symm (hY _ _)
  | _ :: _, _ :: _, _, _, hX, hY, h => by
    simp only [List.foldr_cons, VExpr.forallE.injEq] at h
    rw [h.1, V.foldr_forallE_inj' hX hY h.2]

theorem V.foldr_app_ne_forallE (I : Name) (ls : List VLevel) : ∀ (args : List VExpr) A B,
    args.foldr (fun (A acc : VExpr) => acc.app A) (.const I ls) ≠ .forallE A B
  | [], _, _, h => by cases h
  | _ :: _, _, _, h => by cases h

/-- `hhead`, from the iota leaf's data only. -/
theorem V.hhead_supply (RP : RankParams) {rec c' : Name} {mm k : Nat}
    {r : (Pattern.iota rec mm c' k).RHS} {g : PatGen}
    (hg : Pattern.gen Params.env RP.rank Params.classify (.iota rec mm c' k) r = some g)
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
    obtain ⟨lf, hxf⟩ := V.matches_varN mm hf
    obtain ⟨la, hxa⟩ := V.matches_varN k ha
    cases path with
    | inl x =>
      left
      obtain ⟨s, hs, he⟩ := hxf x
      have hi : (Pattern.varN (.const rec) mm).pathIdx x < mm :=
        lf ▸ (List.getElem?_eq_some_iff.1 hs).1
      simp only [Sum.elim_inl, Pattern.pathIdx_inl, Pattern.nvars_varN, Pattern.nvars]
      rw [he, Nat.zero_add, show (Pattern.varN (.const rec) mm).pathIdx x + k =
        fields.length + (Pattern.varN (.const rec) mm).pathIdx x by omega, V.lowerCtx_rec _ _ _ _ hi]
      have := hρ ((Pattern.varN (.const rec) mm).pathIdx x + 1)
      rwa [Valuation.ofRargs, List.foldr_cons, Valuation.push, ← Valuation.ofRargs,
        V.ofRargs_get hs] at this
    | inr x =>
      right
      obtain ⟨s, hs, -⟩ := hxa x
      have hi : (Pattern.varN (.const c') k).pathIdx x < k :=
        la ▸ (List.getElem?_eq_some_iff.1 hs).1
      obtain ⟨I'', Ts', e4, hall⟩ := RP.ctor_fields_closed (cl := .ctor k) rfl hcl hci'
      have hT : Ts = Ts' := V.foldr_forallE_inj' (V.foldr_app_ne_forallE _ _ args)
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

#print axioms V.hhead_supply
end Lean4Lean.SExpr
