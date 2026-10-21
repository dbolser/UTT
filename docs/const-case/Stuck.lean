import Lean4Lean.Experimental.ShapeLogRelAdequacy
namespace Lean4Lean.SExpr
variable [Params]

/-! Experiment 1 (predates the `major` rule, merged in b2516c4): a recursor applied to a
NON-constructor major premise is stuck under the SExpr `WHRed`.

Originally `WHRed` had only `app`/`beta`/`extra`, and `extra` needs a *syntactic* `MatchesS`,
so `rec a₁ … aₙ x` was stuck for every non-ctor `x`, even `x = g T X` with `g` a `symb`
(the former `WHNF.rec_symb_major`). The `major` rule lets the argument in major-premise
position reduce, so now only an argument that is itself stuck keeps the recursor stuck. The
surviving witness is `WHNF.rec_bvar`: `rec a₁ … aₙ (bvar i)` is in WHNF, since no rule
reduces a `bvar`. We only assume the classification of the recursor (`pat_simple`, `pat_wf`). -/

abbrev apps (c : Name) (ls : List SLevel) (args : List SExpr) : SExpr :=
  args.foldr (fun a acc => SExpr.app acc a) (SExpr.const c ls)

/-- A `varN (const c) n` pattern only matches an `n`-fold application of `const c`. -/
theorem _root_.Lean4Lean.Pattern.MatchesS.varN_const_inv {n} : ∀ {e m1 m2},
    Pattern.MatchesS (.varN (.const c) n) e m1 m2 → ∃ args, args.length = n ∧ e = apps c m1 args := by
  induction n with
  | zero => intro e m1 m2 h; cases h; exact ⟨[], rfl, rfl⟩
  | succ n ih =>
    intro e m1 m2 h
    cases h with | var h' => ?_
    obtain ⟨args, hl, rfl⟩ := ih h'
    exact ⟨_ :: args, by simp [hl], rfl⟩

omit [Params] in
theorem Pattern.WF.varN_const {n k} : ∀ {top},
    Pattern.WF cl (.varN (.const c) n) top k →
    cl c = some (if top then .symb (n + k) else .ctor (n + k)) := by
  induction n generalizing k with
  | zero => intro top h; simpa [Pattern.varN, Pattern.WF] using h
  | succ n ih =>
    intro top h; have := ih (k := k + 1) h
    rw [show n + 1 + k = n + (k + 1) by omega]; exact this

theorem apps_inj {args args' : List SExpr} (heq : apps r ls' args = apps c ls args') :
    r = c ∧ ls' = ls ∧ args = args' := by
  induction args generalizing args' with
  | nil => cases args' <;> simp [apps, List.foldr] at heq ⊢; exact heq
  | cons b bs ih =>
    cases args' with
    | nil => simp [apps, List.foldr] at heq
    | cons b' bs' =>
      simp [apps, List.foldr] at heq
      have := ih heq.1
      exact ⟨this.1, this.2.1, this.2.2 ▸ heq.2 ▸ rfl⟩

theorem _root_.Lean4Lean.Pattern.MatchesS.varN_const_bvar
    (h : Pattern.MatchesS (.varN (.const c') k) (.bvar i) ls' m2) : False := by
  obtain ⟨as, -, heq⟩ := h.varN_const_inv
  cases as <;> cases heq

theorem WHRed.app_inv (H : Γ ⊢ .app f a ⤳ e') :
    (∃ f', Γ ⊢ f ⤳ f' ∧ e' = .app f' a) ∨ (∃ A e, f = .lam A e) ∨
    (∃ p r m1 m2, Params.Pat p r ∧ Pattern.MatchesS p (.app f a) m1 m2) ∨
    (∃ a', IsMajorPremise f ∧ Γ ⊢ a ⤳ a' ∧ e' = .app f a') := by
  cases H with
  | app h => exact .inl ⟨_, h, rfl⟩
  | major h1 h2 => exact .inr (.inr (.inr ⟨_, h1, h2, rfl⟩))
  | beta => exact .inr (.inl ⟨_, _, rfl⟩)
  | extra h1 h2 _ _ => exact .inr (.inr (.inl ⟨_, _, _, _, h1, h2⟩))

/-- A `symb (n+1)` spine sits in major-premise position only when it carries exactly `n`
arguments: the rule prefix it matches is `varN (const c) m` with `classify c = symb (m+1)`. -/
theorem IsMajorPremise.apps_length (hsym : Params.classify c = some (.symb (n + 1)))
    {args : List SExpr} (hm : IsMajorPremise (apps c ls args)) : args.length = n := by
  obtain ⟨p, ⟨r, h1⟩, p₁, p₂, h2, m1, m2, h3⟩ := hm
  obtain ⟨sp, rfl⟩ := Params.pat_simple h1
  have wf := Params.pat_wf h1
  cases sp with
  | defn d => nomatch h2
  | iota r m c' k =>
    have e := Params.simple_app h1 h2
    dsimp only [SimplePattern.toPattern] at e wf
    cases e
    obtain ⟨as, hl, heq⟩ := h3.varN_const_inv
    obtain ⟨rfl, rfl, rfl⟩ := apps_inj heq
    simp only [Pattern.WF] at wf
    have := Pattern.WF.varN_const (k := 1) wf.1
    rw [hsym] at this; simp at this; omega

/-- A symbol of arity `n+1` applied to a list of arguments: any head step is either a step in
the function part, an iota step whose last argument is a syntactic ctor application, or (via
`major`) a step in the last argument, which then sits in major-premise position
(`args'.length = n`). -/
theorem WHRed.apps_inv (hsym : Params.classify c = some (.symb (n + 1))) {args : List SExpr}
    (H : Γ ⊢ apps c ls args ⤳ e') :
    (∃ f' a args', args = a :: args' ∧ Γ ⊢ apps c ls args' ⤳ f' ∧ e' = .app f' a) ∨
    (∃ a args', args = a :: args' ∧ args'.length = n ∧
        ∃ c' k ls' m2, Pattern.MatchesS (.varN (.const c') k) a ls' m2 ∧
          Params.classify c' = some (.ctor k)) ∨
    (∃ a a' args', args = a :: args' ∧ args'.length = n ∧ Γ ⊢ a ⤳ a' ∧
        e' = .app (apps c ls args') a') := by
  cases args with
  | nil =>
    cases H with
    | extra h1 h2 h3 h4 =>
      clear h3 h4
      obtain ⟨sp, rfl⟩ := Params.pat_simple h1
      have wf := Params.pat_wf h1
      cases sp with
      | defn d =>
        dsimp only [SimplePattern.toPattern] at h2 wf
        cases h2; simp [Pattern.WF, hsym] at wf
      | iota r m c' k => dsimp only [SimplePattern.toPattern] at h2; cases h2
  | cons a args' =>
    rcases WHRed.app_inv H with
      ⟨f', h, rfl⟩ | ⟨A, e, hf⟩ | ⟨p, r, m1, m2, h1, h2⟩ | ⟨a', hm, ha, rfl⟩
    · exact .inl ⟨_, a, args', rfl, h, rfl⟩
    · cases args' <;> cases hf
    · obtain ⟨sp, rfl⟩ := Params.pat_simple h1
      have wf := Params.pat_wf h1
      cases sp with
      | defn d => dsimp only [SimplePattern.toPattern] at h2; cases h2
      | iota r m c' k =>
        dsimp only [SimplePattern.toPattern] at h2 wf
        cases h2 with | app hf' ha => ?_
        obtain ⟨args'', hl, heq⟩ := hf'.varN_const_inv
        simp only [Pattern.WF] at wf
        have h1' := Pattern.WF.varN_const (k := 1) wf.1
        have h2' := Pattern.WF.varN_const (k := 0) wf.2
        obtain ⟨rfl, rfl, rfl⟩ := apps_inj heq
        rw [hsym] at h1'; simp at h1'
        exact .inr (.inl ⟨a, _, rfl, by omega, _, _, _, _, ha, by simpa using h2'⟩)
    · exact .inr (.inr ⟨a, a', args', rfl, hm.apps_length hsym, ha, rfl⟩)

/-- A symbol of arity `n+1` applied to at most `n` arguments is in weak head normal form. -/
theorem WHNF.apps_symb (hsym : Params.classify c = some (.symb (n + 1))) :
    ∀ {args : List SExpr}, args.length ≤ n → WHNF Γ (apps c ls args) := by
  intro args
  induction args with
  | nil =>
    intro _ e' H
    rcases WHRed.apps_inv hsym H with ⟨_, _, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, h, _⟩ <;> cases h
  | cons b bs ih =>
    intro hl e' H
    rcases WHRed.apps_inv hsym H with
      ⟨f', a, args', h, hred, _⟩ | ⟨a, args', h, hl', _⟩ | ⟨a, a', args', h, hl', _, _⟩
    · cases h; exact ih (by simp at hl; omega) _ hred
    · cases h; simp at hl; omega
    · cases h; simp at hl; omega

/-- The decisive instance: a recursor of arity `n+1` applied to `n` arguments and then to a
bound variable is stuck under the SExpr `WHRed`. The `major` rule does not help, since no rule
reduces a `bvar`. -/
theorem WHNF.rec_bvar (hsym : Params.classify c = some (.symb (n + 1))) {args : List SExpr}
    (hlen : args.length = n) : WHNF Γ (.app (apps c ls args) (.bvar i)) := by
  intro e' H
  rcases WHRed.apps_inv (args := .bvar i :: args) hsym H with
    ⟨f', a, args', h, hred, _⟩ | ⟨a, args', h, hl, c', k, ls', m2, hm, _⟩ |
    ⟨a, a', args', h, _, hred, _⟩
  · cases h; exact WHNF.apps_symb hsym (Nat.le_of_eq hlen) _ hred
  · cases h; exact hm.varN_const_bvar
  · cases h; cases hred with | extra _ h2 => nomatch h2

/- `WHNF.rec_symb_major` used to live here: "a recursor applied to `g T X`, with `g` classified
`symb`, is stuck even if `g T X` is defeq to a constructor application". The `major` rule
(merged in b2516c4) makes it false by design: `apps c ls args` is a rule prefix, so
`Γ ⊢ g T X ⤳ e` yields `Γ ⊢ .app (apps c ls args) (g T X) ⤳ .app (apps c ls args) e` by
`WHRed.major`. `WHNF.rec_bvar` above is the surviving stuck-ness witness. -/

end Lean4Lean.SExpr
