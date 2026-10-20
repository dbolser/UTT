import Lean4Lean.Experimental.E6.Parts
/-! E6: iota-leaf data lemmas (ported from `docs/const-case/plan/E6a/HheadSupply.lean`). -/
namespace Lean4Lean.SExpr
variable [Params]

/-! From `docs/const-case/plan/E6a/HheadSupply.lean` (a's verifier), `RankParams` → the
`Params` fields, `V.` → `T.`. -/

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

theorem T.foldr_forallE_inj' : ∀ {Ts Ts' : List VExpr} {X Y : VExpr},
    (∀ A B, X ≠ .forallE A B) → (∀ A B, Y ≠ .forallE A B) →
    Ts.foldr .forallE X = Ts'.foldr .forallE Y → Ts = Ts'
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, hX, _, h => absurd h (hX _ _)
  | _ :: _, [], _, _, _, hY, h => absurd h.symm (hY _ _)
  | _ :: _, _ :: _, _, _, hX, hY, h => by
    simp only [List.foldr_cons, VExpr.forallE.injEq] at h
    rw [h.1, T.foldr_forallE_inj' hX hY h.2]

theorem T.foldr_app_ne_forallE (I : Name) (ls : List VLevel) : ∀ (args : List VExpr) A B,
    args.foldr (fun (A acc : VExpr) => acc.app A) (.const I ls) ≠ .forallE A B
  | [], _, _, h => by cases h
  | _ :: _, _, _, h => by cases h

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
        fields.length + (Pattern.varN (.const rec) mm).pathIdx x by omega,
        T.lowerCtx_rec _ _ _ _ hi]
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

theorem T.sfoldr_forallE_inj : ∀ {Hs Hs' : List SExpr} {B B' : SExpr}, Hs.length = Hs'.length →
    Hs.foldr .forallE B = Hs'.foldr .forallE B' → Hs = Hs' ∧ B = B'
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | A :: Hs, A' :: Hs', _, _, hl, h => by
    simp only [List.foldr_cons, SExpr.forallE.injEq] at h
    obtain ⟨h1, h2⟩ := T.sfoldr_forallE_inj (by simpa using hl) h.2
    exact ⟨by rw [h.1, h1], h2⟩

/-! Ported from `docs/const-case/plan/E3/Measure7-b.lean` (`genIdx` → `pathIdx`). -/

omit [Params] in
theorem T.range_reverse_succ (k : Nat) :
    (List.range (k+1)).reverse = ((List.range k).reverse.map (· + 1)) ++ [0] := by
  rw [List.range_succ_eq_map, List.reverse_cons, List.map_reverse]

/-- `varN (const c) k` matches the open spine instance `c τ(k-1) … τ 0` with
`m2 = τ ∘ pathIdx` (Measure7-b's `MatchesS.varN_genIdx`, with the repo's `pathIdx`). -/
theorem T.matchesS_varN_pathIdx {c : Name} {ls : List SLevel} :
    ∀ (k : Nat) (τ : Subst),
      (Pattern.varN (.const c) k).MatchesS (spine (.const c ls) ((List.range k).reverse.map τ)) ls
        (fun path => τ ((Pattern.varN (.const c) k).pathIdx path))
  | 0, τ => Pattern.MatchesS.congr .const nofun
  | k+1, τ => by
    rw [T.range_reverse_succ, List.map_append, List.map_map, List.map_singleton, spine_snoc]
    have := (T.matchesS_varN_pathIdx (c := c) (ls := ls) k (fun i => τ (i + 1))).var (a' := τ 0)
    refine this.congr fun path => ?_
    cases path <;> rfl

/-- (b') The instantiated LHS matches the pattern with `m2 = σ ∘ pathIdx`. -/
theorem T.gen_lhs_matches {rec c' : Name} {m n : Nat}
    {r : (Pattern.iota rec m c' n).RHS} {g : PatGen}
    (hg : Pattern.gen Params.env Params.rank Params.classify (.iota rec m c' n) r = some g)
    {ci : VConstant} (h1 : Params.env.constants rec = some ci)
    {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr} (hHs : Hs.length = m)
    (hT : ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj))
    {ls : List SLevel} (hls : ls.length = ci.uvars) (σ : Subst) :
    (Pattern.iota rec m c' n).MatchesS ((mkInst ls g.lhs).subst σ) ls
      (fun path => σ ((Pattern.iota rec m c' n).pathIdx path)) := by
  rw [Pattern.gen_lhs_subst hg h1 hHs hT hls σ]
  refine ((T.matchesS_varN_pathIdx m (fun i => σ (n + i))).app
    (T.matchesS_varN_pathIdx (ls := us.map (SLevel.instV ls)) n σ)).congr fun path => ?_
  cases path with
  | inl x => simp [Pattern.nvars_varN, Pattern.nvars, Nat.add_comm]
  | inr x => rfl

omit [Params] in
theorem T.varN_var (p : Pattern) : ∀ n, (Pattern.var p).varN n = (p.varN n).var
  | 0 => rfl
  | n+1 => by simp only [Pattern.varN, T.varN_var p n]

/-- A `varN` pattern matches any spine of the right length. -/
theorem T.matchesS_spine {q : Pattern} {h : SExpr} {ls}
    {g : q.Path → SExpr} (H : q.MatchesS h ls g) : ∀ xs : List SExpr,
      ∃ g', (q.varN xs.length).MatchesS (SExpr.spine h xs) ls g'
  | [] => ⟨g, H⟩
  | x :: xs => by
    have ⟨g', h'⟩ := T.matchesS_spine (q := q.var) (H.var (a' := x)) xs
    revert g' h'; rw [T.varN_var]
    exact fun g' h' => ⟨g', h'⟩

/-- The last binder type of a strong telescope is typed in the whole telescope. -/
theorem T.telStrong_last {E : VEnv} : ∀ {Γ Ts : List SExpr} {B : SExpr}, TelStrongE E Γ Ts B →
    ∃ v, IsDefEqStrong E (Ts.reverse ++ Γ) B B (.sort v)
  | _, [], _, .nil h => ⟨_, h⟩
  | _, _ :: _, _, .cons _ H => by
    obtain ⟨v, h⟩ := T.telStrong_last H
    exact ⟨v, by simpa using h⟩


/-- A shape compatible with `indTy` is below it. -/
theorem T.le_indTy_of_compat {N : Nat} {a : TShape} (hc : a.Compat (WShape.indTy (n := N)).T) :
    a ≤ (WShape.indTy (n := N)).T := by
  obtain ⟨z, h1, h2⟩ := TShape.Compat.def'.1 hc
  obtain ⟨nz, w⟩ := z
  rw [TShape.LE.def (Nat.le_max_left (N+1) nz) (Nat.le_max_right (N+1) nz)] at h2
  simp only [WShape.T] at h2
  obtain ⟨K, hK⟩ : ∃ K, max (N+1) nz = K + 1 := ⟨max (N+1) nz - 1, by omega⟩
  rw [hK, WShape.lift_indTy] at h2
  have hw := WShape.indTy_le.1 h2
  have := h1.trans (TShape.lift_eqv (a := ⟨nz, w⟩) (Nat.le_max_right (N+1) nz)).2
  dsimp only at this
  rw [hK, hw] at this
  exact this.trans T.indTy_T_le

/-- `indTy` interprets a non-Prop inductive-type constant. -/
theorem T.indTy_interp_const {ρ : Valuation} {I₀ : Name} {lv : List SLevel} {ciI : VConstant}
    {u : VLevel} (hI : Params.classify I₀ = some (.indTy 0))
    (hci : Params.env.constants I₀ = some ciI) (hlen : lv.length = ciI.uvars)
    (hty : ciI.type = .sort u) (hu : SLevel.instV lv u ≠ .zero) {N : Nat} :
    LE_Interp ρ (WShape.indTy (n := N)).T (.const I₀ lv) := by
  refine .const (R := fun _ _ => False) (m' := (WShape.indTy (n := N)).T)
    (a := (WShape.type (n := N+1)).T) hci hlen .rfl (WShape.HasType.T .indTy) ?_
    (LE_Interp.Const.indTy (n := N) (rargs := []) hI T.indTy_T_le) (fun _ _ h => h.elim)
  rw [hty]
  refine .sort ?_
  simp only [ne_eq, hu, not_false_eq_true, decide_true]
  exact TShape.sort_eqv.1

end Lean4Lean.SExpr
