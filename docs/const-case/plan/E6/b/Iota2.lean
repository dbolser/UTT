import Lean4Lean.Experimental.E6.Iota1
/-! E6, iota shape: the inversion of constructor-spine interpretations (every interpretation of
`c' z₁ … zₙ` is below the constructor shape of its arguments' entries). It gives the
compatibility of the goal's type shape with every interpretation of the RHS type at `ρ_low`. -/
namespace Lean4Lean.SExpr
variable [Params]

omit [Params] in
theorem T.forall₂_of_getElem {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
    (∀ (i : Nat) a b, l₁[i]? = some a → l₂[i]? = some b → R a b) → List.Forall₂ R l₁ l₂
  | [], [], _, _ => .nil
  | a :: l₁, b :: l₂, hl, h =>
    .cons (h 0 a b rfl rfl) (T.forall₂_of_getElem (by simpa using hl)
      fun i a' b' h1 h2 => h (i+1) a' b' (by simpa using h1) (by simpa using h2))
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

/-- The constructor shape is monotone across levels, entrywise. -/
theorem T.ctor'_T_le {c : Name} {K L : Nat} {rs : List (WShape K)} {l : List (WShape L)}
    (hlen : rs.length = l.length)
    (h : ∀ (j : Nat) (s : WShape K) (t : WShape L), rs[j]? = some s → l[j]? = some t → s.T ≤ t.T) :
    (WShape.ctor' c rs).T ≤ (WShape.ctor' c l).T := by
  have le₁ := Nat.le_max_left K L; have le₂ := Nat.le_max_right K L
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂)]
  simp only [WShape.T]
  rw [WShape.lift_ctor' le₁, WShape.lift_ctor' le₂]
  refine WShape.ctor'_le_ctor' (T.forall₂_of_getElem (by simpa using hlen) fun j a b ha hb => ?_)
  rw [List.getElem?_map] at ha hb
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 ha
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 hb
  exact (TShape.LE.def le₁ le₂).1 (h j s t hs ht)

/-- A constructor at full arity, interpreted through `Const`: below its constructor shape
(beyond the arity everything is `⊥`, `Const.compat_mismatch`). -/
theorem T.const_full_bound {c' : Name} {ls : List SLevel} {R : TShape → SExpr → Prop}
    {n : Nat} {rargs : List (WShape n)} {m : TShape}
    (hcl : Params.classify c' = some (.ctor rargs.length))
    (H : LE_Interp.Const c' ls R rargs m) : m ≤ (WShape.ctor' c' rargs.reverse).T := by
  cases H with
  | bot => exact TShape.bot_le'
  | @lam f _ _ he m_le =>
    by_cases hf : f.NonZero
    · obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf
      have := LE_Interp.Const.compat_mismatch (rargs2 := rargs) (by simp)
        (he _ t (WShapeFun.mem_val hxy)) (.inl hcl)
      cases hn <| WShape.LE.T_iff.1 <| this.trans TShape.bot_eqv.2
    · have := WShape.lam'_le_lam'.2 <| NonZero.not_iff.1 hf
      exact m_le.trans <| (WShape.lam'_bot ▸ this).T.trans TShape.bot_le'
  | ctor _ hle => exact hle
  | indTy h => cases hcl.symm.trans h
  | pat hP hM => cases hcl.symm.trans (pat_arity hP hM.arity)

omit [Params] in
theorem T.varN_wf {cl : Name → Option Classification} {c : Name} :
    ∀ (k : Nat) {j : Nat}, cl c = some (.ctor (j + k)) → (Pattern.varN (.const c) k).WF cl false j
  | 0, j, h => by simpa [Pattern.varN, Pattern.WF] using h
  | k+1, j, h => by
    show (Pattern.varN (.const c) k).WF cl false (j + 1)
    exact T.varN_wf k (by rw [show j + 1 + k = j + (k+1) by omega]; exact h)

omit [Params] in
theorem T.varN_path_surj {c : Name} : ∀ (k i : Nat), i < k →
    ∃ path : (Pattern.varN (.const c) k).Path, (Pattern.varN (.const c) k).pathIdx path = i
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k+1, 0, _ => ⟨(none : Option (Pattern.varN (.const c) k).Path), rfl⟩
  | k+1, i+1, h => by
    obtain ⟨path, hp⟩ := T.varN_path_surj (c := c) k i (by omega)
    exact ⟨(some path : Option (Pattern.varN (.const c) k).Path), by
      show (Pattern.varN (.const c) k).pathIdx path + 1 = i + 1; rw [hp]⟩

omit [Params] in
theorem T.range_reverse_succ (k : Nat) :
    (List.range (k+1)).reverse = ((List.range k).reverse.map (· + 1)) ++ [0] := by
  rw [List.range_succ_eq_map, List.reverse_cons, List.map_reverse]

/-- `varN (const c) k` matches `c τ(k-1) … τ 0` with `m2 = τ ∘ pathIdx`
(`Measure7-b.lean: MatchesS.varN_genIdx`, over `pathIdx`). -/
theorem T.matchesS_varN {c : Name} {ls : List SLevel} :
    ∀ (k : Nat) (τ : Subst),
      (Pattern.varN (.const c) k).MatchesS (spine (.const c ls) ((List.range k).reverse.map τ)) ls
        (fun path => τ ((Pattern.varN (.const c) k).pathIdx path))
  | 0, τ => Pattern.MatchesS.congr .const nofun
  | k+1, τ => by
    rw [T.range_reverse_succ, List.map_append, List.map_map, List.map_singleton, spine_snoc]
    have := (T.matchesS_varN (c := c) (ls := ls) k (fun i => τ (i + 1))).var (a' := τ 0)
    refine this.congr fun path => ?_
    cases path <;> rfl

/-- Inversion of an interpretation of a full-arity constructor spine. -/
theorem T.ctor_spine_interp {ρ : Valuation} {x : TShape} {c' : Name} {ls' : List SLevel}
    {k : Nat} {τ : Subst} (hcl : Params.classify c' = some (.ctor k))
    (H : LE_Interp ρ x (spine (.const c' ls') ((List.range k).reverse.map τ))) :
    ∃ (K : Nat) (rs : List (WShape K)), rs.length = k ∧
      (∀ (i : Nat) (s : WShape K), rs[i]? = some s → LE_Interp ρ s.T (τ i)) ∧
      x ≤ (WShape.ctor' c' rs.reverse).T := by
  obtain ⟨n', hn'⟩ := LE_Interp.Matches.of_matchesS (T.matchesS_varN (c := c') (ls := ls') k τ)
    (T.varN_wf k (j := 0) (by simpa using hcl)) H
  obtain ⟨c'', rs, m', m_arg, hM, hpath, hle, hC⟩ := hn' n' (Nat.le_refl _)
  cases LE_Interp.Matches.varN_const_head hM
  obtain ⟨hl, hx⟩ := T.matches_varN k hM
  refine ⟨n', rs, hl, fun i s hs => ?_, hle.trans (T.const_full_bound (hl ▸ hcl) hC)⟩
  obtain ⟨path, hp⟩ := T.varN_path_surj (c := c') k i (hl ▸ (List.getElem?_eq_some_iff.1 hs).1)
  obtain ⟨s', hs', he⟩ := hx path
  rw [hp, hs] at hs'; cases hs'
  have := hpath path
  rwa [he, hp] at this

end Lean4Lean.SExpr
