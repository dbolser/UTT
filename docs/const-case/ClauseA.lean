import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Lens 1 (clause) experiment, the recommended clause of DESIGN-ctor-code-shape.md with codes as
finite data: `SpineTyped`, `SpineDefEq`, `CtorDefEq`, and the LogRel-field proofs that depend on
the clause's form (`left`, `symm`, `conv`, `trans`, `mono`, `lift_aux` both ways, `whr`).
Kept compiling against the tree: `WHNF.ctorSpine` here is renamed `WHNF.ctorApps` because
`SExpr.lean` now has a `spine`-based `WHNF.ctorSpine`. Sorry-free. -/
/-! Lens 1, experiment 2: the recommended constructor clause.

The field type-codes live in the *shape data*: a ctor shape is `ctor c l k` with `l` the field
shapes (level `n`) and `k : WShape (n+1)` a Π-code of the constructor's declared type (design A,
placement λ; `k` can be stored as its two components `(a₁ : Shape n, f : ShapeFun n)` inside
`ShapeS.ctor`, so no nested inductive is needed).  `hasType (ctor c l k) indTy := k : type ∧
SpineTyped l k`, and `ctor c l k ≤ ctor c l' k' ↔ l ≤ l' ∧ k ≤ k'`.

Here we define `SpineTyped`, the clause `SpineDefEq` (Exp2 + per-step `TyDefEq A₁ A₁ a₁`, minus
the dead `∃ w` conjunct), the head part `CtorDefEq`, and prove the field lemmas that depend on the
clause's form: `left`, `symm`, `conv`, `trans`, **`mono`** (= `mono_l`), **`lift_aux`** (both
directions, = the new case of `LR.lift_succ_aux`), and `whr`/`trans` for the head part
(`WHNF.ctorApps`, `apps_inj`).  No sorries.  The shape-algebra change itself is not in the
snapshot, so the wiring into `LRS.DefEq` is stated as a comment at the end. -/
namespace Lean4Lean.SExpr
variable [Params]

/-! ### Constructor spines are weak-head normal (ported/extended from docs/const-case/Stuck.lean) -/

/-- `c ls aₙ … a₁` (arguments in *reverse* order, so that induction on the list peels the last
argument). -/
abbrev apps (c : Name) (ls : List SLevel) (args : List SExpr) : SExpr :=
  args.foldr (fun a acc => SExpr.app acc a) (SExpr.const c ls)

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

theorem WHRed.app_inv (H : Γ ⊢ .app f a ⤳ e') :
    (∃ f', Γ ⊢ f ⤳ f' ∧ e' = .app f' a) ∨
    (IsMajorPremise f ∧ ∃ a', Γ ⊢ a ⤳ a' ∧ e' = .app f a') ∨
    (∃ A e, f = .lam A e) ∨
    (∃ p r m1 m2, Params.Pat p r ∧ Pattern.MatchesS p (.app f a) m1 m2) := by
  cases H with
  | app h => exact .inl ⟨_, h, rfl⟩
  | major h1 h2 => exact .inr (.inl ⟨h1, _, h2, rfl⟩)
  | beta => exact .inr (.inr (.inl ⟨_, _, rfl⟩))
  | extra h1 h2 _ _ => exact .inr (.inr (.inr ⟨_, _, _, _, h1, h2⟩))

/-- A `varN (const r') m` prefix of a rule's lhs has `r'` classified `symb` (`pat_wf`), so it never
matches a constructor-headed spine. -/
theorem ctor_not_matches_prefix {args : List SExpr} (hc : Params.classify c = some (.ctor k))
    (hwf : Pattern.WF Params.classify (.varN (.const r') m) true j)
    (hm : Pattern.MatchesS (.varN (.const r') m) (apps c ls args) m1 m2) : False := by
  obtain ⟨_, _, heq⟩ := hm.varN_const_inv
  obtain ⟨rfl, -, -⟩ := apps_inj heq
  have h := Pattern.WF.varN_const hwf
  rw [hc] at h; cases h

theorem WHNF.ctorApps (hc : Params.classify c = some (.ctor k)) :
    ∀ (args : List SExpr), WHNF Γ (apps c ls args) := by
  intro args
  induction args with
  | nil =>
    intro _ H; cases H with
    | extra h1 h2 =>
      obtain ⟨_|_, rfl⟩ := Params.pat_simple h1
      · nomatch h2
      · exact ctor_not_matches_prefix (m := 0) (args := []) hc (Params.pat_wf h1) h2
  | cons a args ih =>
    intro e' H
    rcases WHRed.app_inv H with ⟨f', h, -⟩ | ⟨⟨p, ⟨_, h1⟩, p₁, p₂, h2, _, _, h3⟩, -⟩ | ⟨A, e, hf⟩ |
      ⟨p, r, m1, m2, h1, h2⟩
    · exact ih _ h
    · cases Params.simple_app h1 h2
      obtain ⟨_|_, h⟩ := Params.pat_simple h1 <;> cases h
      have wf := Params.pat_wf h1; simp only [Pattern.WF] at wf
      exact ctor_not_matches_prefix hc wf.1 h3
    · cases args <;> cases hf
    · obtain ⟨_|_, rfl⟩ := Params.pat_simple h1
      · dsimp only [SimplePattern.toPattern] at h2
        cases h2 with | app h3 _ => ?_
        have wf := Params.pat_wf h1; simp only [SimplePattern.toPattern, Pattern.WF] at wf
        exact ctor_not_matches_prefix hc wf.1 h3
      · nomatch h2

/-! ### The clause -/

/-- `hasType (ctor c l k) indTy`: fields typed along the code (`k` descends by `f.app p`,
re-lifted). -/
def SpineTyped : ∀ {n}, List (WShape n) → WShape (n+1) → Prop
  | _, [], _ => True
  | n, p :: ps, k => ∃ (a₁ : WShape n) (f : WShapeFun n),
      k = .forallE a₁ f ∧ p.HasType a₁ ∧ SpineTyped ps ((f.app p).lift (n+1))

/-- Field relatedness along the code.  Per field: the current type whnf's to a Π, syntactic defeq
of the fields, validity of the domain at `a₁`, LR-relatedness at `(p, a₁)`, and the codomain's
`TyDefEq` under both instantiations (what `conv`/`symm`/`trans` need to move between the two
sides); then recurse on the instantiated codomain at the descended code. -/
def SpineDefEq (Γ : List SExpr) : ∀ {n}, List SExpr → List SExpr → SExpr →
    List (WShape n) → WShape (n+1) → Prop
  | _, [], [], _, [], _ => True
  | n, x :: xs, y :: ys, T, p :: ps, k =>
    ∀ (a₁ : WShape n) (f : WShapeFun n), k = .forallE a₁ f → p.HasType a₁ →
      ∃ A₁ A₂ u v, Γ ⊢ T ⤳* .forallE A₁ A₂ ∧ Γ ⊢ A₁ : .sort u ∧ A₁::Γ ⊢ A₂ : .sort v ∧
        Γ ⊢ x ≡ y : A₁ ∧
        (LR Γ).TyDefEq A₁ A₁ a₁ ∧
        (LR Γ).DefEq x y A₁ p a₁ ∧
        (LR Γ).TyDefEq (A₂.inst x) (A₂.inst y) (f.app p) ∧
        SpineDefEq Γ xs ys (A₂.inst x) ps ((f.app p).lift (n+1))
  | _, _, _, _, _, _ => False

/-- The `LRS.DefEq` clause at `(m, a) = (ctor c l k, indTy)`.  The ambient type `A` is not
mentioned, so `conv` is `id` and `TyDefEq` at `indTy` may stay `True`. -/
def CtorDefEq (Γ : List SExpr) {n} (M N : SExpr) (c : Name) (l : List (WShape n))
    (k : WShape (n+1)) : Prop :=
  ∃ (ls : List SLevel) (ci : VConstant) (xs ys : List SExpr),
    Params.env.constants c = some ci ∧
    Γ ⊢ M ⤳* apps c ls xs.reverse ∧ Γ ⊢ N ⤳* apps c ls ys.reverse ∧
    SpineDefEq Γ xs ys (SExpr.mkInst ls ci.type) l k

/-! ### Shape helpers -/

theorem lift_app_type {n} {f : WShapeFun n} {p : WShape n}
    (h : (f.app p).HasType .type) : ((f.app p).lift (n+1)).HasType .type := by
  have := (WShape.HasType.lift (Nat.le_succ n)).2 h; rwa [WShape.lift_sort] at this

theorem code_parts {a₁ : WShape n} {f : WShapeFun n} (hk : (WShape.forallE a₁ f).HasType .type) :
    WShape.HasTypePi f a₁ true := by
  obtain ⟨_, htpi, _⟩ := WShape.HasType.forallE_l.1 hk; exact htpi.toType

theorem code_dom {a₁ : WShape n} {f : WShapeFun n} (hk : (WShape.forallE a₁ f).HasType .type) :
    a₁.HasType .type := (WShape.HasTypePi.iff.1 (code_parts hk)).1.isType

theorem code_cod {a₁ : WShape n} {f : WShapeFun n} (hk : (WShape.forallE a₁ f).HasType .type)
    (hp : p.HasType a₁) : (f.app p).HasType .type := (WShape.HasTypePi.iff.1 (code_parts hk)).2 _ hp

theorem WShape.lift_eq_forallE {s : WShape (n+1)} (le : n ≤ m) {a' : WShape m} {f' : WShapeFun m}
    (h : s.lift (m+1) = .forallE a' f') :
    ∃ (a : WShape n) (f : WShapeFun n), s = .forallE a f ∧ a' = a.lift m ∧ f' = f.lift m := by
  cases s using WShape.casesOn' with
  | bot => rw [WShape.lift_bot] at h; cases congrArg (·.1) h
  | sort => rw [WShape.lift_sort] at h; cases congrArg (·.1) h
  | lam f hf => rw [WShape.lift_lam le] at h; cases congrArg (·.1) h
  | ctor c l hc => rw [WShape.lift_ctor le] at h; cases congrArg (·.1) h
  | indTy => rw [WShape.lift_indTy] at h; cases congrArg (·.1) h
  | forallE a f =>
    rw [WShape.lift_forallE le] at h
    obtain ⟨rfl, rfl⟩ := WShape.forallE.inj.1 h
    exact ⟨a, f, rfl, rfl, rfl⟩

/-! ### Field lemmas for `SpineDefEq` -/

theorem SpineDefEq.left {Γ : List SExpr} {xs : List SExpr} : ∀ {n} {ys : List SExpr} {T}
    {ps : List (WShape n)} {k : WShape (n+1)},
    SpineDefEq Γ xs ys T ps k → SpineDefEq Γ xs xs T ps k := by
  induction xs with
  | nil => intro n ys T ps k h; cases ys <;> cases ps <;> simp_all [SpineDefEq]
  | cons x xs ih =>
    intro n ys T ps k h
    cases ys with | nil => simp [SpineDefEq] at h | cons y ys
    cases ps with | nil => simp [SpineDefEq] at h | cons p ps
    intro a₁ f hkf hp; subst hkf
    obtain ⟨A₁, A₂, u, v, rT, hA₁, hA₂, hxy, t1, d1, d2, d4⟩ := h _ _ rfl hp
    exact ⟨A₁, A₂, u, v, rT, hA₁, hA₂, hxy.hasType.1, t1, (LR Γ).left d1, (LR Γ).left_ty d2, ih d4⟩

theorem SpineDefEq.conv {Γ : List SExpr} {xs : List SExpr} : ∀ {n} {ys : List SExpr} {T T'}
    {ps : List (WShape n)} {k : WShape (n+1)}, k.HasType .type →
    (LR Γ).TyDefEq T T' k → SpineDefEq Γ xs ys T' ps k → SpineDefEq Γ xs ys T ps k := by
  induction xs with
  | nil => intro n ys T T' ps k _ _ h; cases ys <;> cases ps <;> simp_all [SpineDefEq]
  | cons x xs ih =>
    intro n ys T T' ps k hk hTT' h
    cases ys with | nil => simp [SpineDefEq] at h | cons y ys
    cases ps with | nil => simp [SpineDefEq] at h | cons p ps
    intro a₁ f hkf hp; subst hkf
    obtain ⟨A₁, A₂, u, v, rT', hA₁, hA₂, hxy, t1, d1, d2, d4⟩ := h _ _ rfl hp
    obtain ⟨B₁, F₁, B₂, F₂, u', v', rT, rT'', hBB, hFF, hValB, hEdge⟩ :=
      (LRS.TyDefEq.forallE_iff (IH := LR Γ)).1 hTT'
    cases rT'.determ .forallE rT'' .forallE
    have hfp := code_cod hk hp
    have d1' := (LR Γ).conv ((LR Γ).symm_ty hValB) d1
    have hxB : Γ ⊢ x ≡ y : B₁ := hBB.symm.defeqDF hxy
    have piL := hEdge.1 hp hxB d1'
    have piD := hEdge.2 hp hxB.hasType.1 ((LR Γ).left d1')
    exact ⟨B₁, F₁, u', v', rT, hBB.hasType.1, hFF.hasType.1, hxB, (LR Γ).left_ty hValB, d1', piL.1,
      ih (lift_app_type hfp) ((LR.TyDefEq.lift (Nat.le_succ n) hfp).2 piD) d4⟩

theorem SpineDefEq.symm {Γ : List SExpr} {xs : List SExpr} : ∀ {n} {ys : List SExpr} {T}
    {ps : List (WShape n)} {k : WShape (n+1)}, k.HasType .type →
    SpineDefEq Γ xs ys T ps k → SpineDefEq Γ ys xs T ps k := by
  induction xs with
  | nil => intro n ys T ps k _ h; cases ys <;> cases ps <;> simp_all [SpineDefEq]
  | cons x xs ih =>
    intro n ys T ps k hk h
    cases ys with | nil => simp [SpineDefEq] at h | cons y ys
    cases ps with | nil => simp [SpineDefEq] at h | cons p ps
    intro a₁ f hkf hp; subst hkf
    obtain ⟨A₁, A₂, u, v, rT, hA₁, hA₂, hxy, t1, d1, d2, d4⟩ := h _ _ rfl hp
    have hfp := code_cod hk hp
    refine ⟨A₁, A₂, u, v, rT, hA₁, hA₂, hxy.symm, t1, (LR Γ).symm d1, (LR Γ).symm_ty d2, ?_⟩
    exact SpineDefEq.conv (lift_app_type hfp)
      ((LR.TyDefEq.lift (Nat.le_succ n) hfp).2 ((LR Γ).symm_ty d2)) (ih (lift_app_type hfp) d4)

theorem SpineDefEq.trans {Γ : List SExpr} {xs : List SExpr} : ∀ {n} {ys zs : List SExpr} {T}
    {ps : List (WShape n)} {k : WShape (n+1)}, k.HasType .type →
    SpineDefEq Γ xs ys T ps k → SpineDefEq Γ ys zs T ps k → SpineDefEq Γ xs zs T ps k := by
  induction xs with
  | nil => intro n ys zs T ps k _ h1 h2; cases ys <;> cases zs <;> cases ps <;> simp_all [SpineDefEq]
  | cons x xs ih =>
    intro n ys zs T ps k hk h1 h2
    cases ys with | nil => simp [SpineDefEq] at h1 | cons y ys
    cases zs with | nil => simp [SpineDefEq] at h2 | cons z zs
    cases ps with | nil => simp [SpineDefEq] at h1 | cons p ps
    intro a₁ f hkf hp; subst hkf
    obtain ⟨A₁, A₂, u, v, rT, hA₁, hA₂, hxy, t1, d1, d2, d4⟩ := h1 _ _ rfl hp
    obtain ⟨A₁', A₂', u', v', rT', hA₁', hA₂', hyz, -, e1, e2, e4⟩ := h2 _ _ rfl hp
    cases rT.determ .forallE rT' .forallE
    have hfp := code_cod hk hp
    refine ⟨A₁, A₂, u, v, rT, hA₁, hA₂, hxy.trans hyz, t1, (LR Γ).trans d1 e1,
      (LR Γ).trans_ty d2 e2, ?_⟩
    exact ih (lift_app_type hfp) d4
      (SpineDefEq.conv (lift_app_type hfp) ((LR.TyDefEq.lift (Nat.le_succ n) hfp).2 d2) e4)

/-- **`mono_l` at the ctor clause.**  Smaller fields along a smaller code: the field typing comes
from `SpineTyped` (i.e. from `hasType (ctor c l k) indTy`), which is why the code must be in the
shape: `p ≤ p'` alone does not give `p : a₁'`. -/
theorem SpineDefEq.mono {Γ : List SExpr} {xs : List SExpr} : ∀ {n} {ys : List SExpr} {T}
    {ps ps' : List (WShape n)} {k k' : WShape (n+1)},
    List.Forall₂ (· ≤ ·) ps ps' → k ≤ k' → k.HasType .type → k'.HasType .type →
    SpineTyped ps k → SpineTyped ps' k' →
    SpineDefEq Γ xs ys T ps' k' → SpineDefEq Γ xs ys T ps k := by
  induction xs with
  | nil =>
    intro n ys T ps ps' k k' hle _ _ _ _ _ h
    cases ys <;> cases hle <;> simp_all [SpineDefEq]
  | cons x xs ih =>
    intro n ys T ps ps' k k' hle hkk hk hk' hty hty' h
    cases ys with | nil => cases hle <;> simp [SpineDefEq] at h | cons y ys
    cases hle with | nil => simp [SpineDefEq] at h | cons hpp hle
    rename_i p p' ps ps'
    intro a₁ f hkf hp; subst hkf
    simp only [SpineTyped] at hty hty'
    obtain ⟨a₁', f', rfl, hp', hty'⟩ := hty'
    obtain ⟨a₁₀, f₀, e, -, hty⟩ := hty
    obtain ⟨rfl, rfl⟩ := WShape.forallE.inj.1 e
    have ⟨le_a, le_f⟩ := WShape.forallE_le_forallE.1 hkk
    obtain ⟨A₁, A₂, u, v, rT, hA₁, hA₂, hxy, t1, d1, d2, d4⟩ := h _ _ rfl hp'
    have ha₁ := code_dom hk; have ha₁' := code_dom hk'
    have hfp := code_cod hk hp; have hfp' := code_cod hk' hp'
    have hp_a₁' : p.HasType a₁' := WShape.HasType.mono_r le_a ha₁' hp
    have le_cod : f.app p ≤ f'.app p' := (WShapeFun.app_mono_l le_f p).trans (WShapeFun.app_mono_r hpp)
    refine ⟨A₁, A₂, u, v, rT, hA₁, hA₂, hxy, (LR Γ).mono_r_2_ty le_a ha₁ ha₁' t1,
      (LR Γ).mono_r_2 le_a hp ha₁' ((LR Γ).mono_l hpp hp_a₁' hp' d1),
      (LR Γ).mono_r_2_ty le_cod hfp hfp' d2, ?_⟩
    exact ih hle (WShape.lift_mono (Nat.le_succ n) le_cod) (lift_app_type hfp) (lift_app_type hfp')
      hty hty' d4

/-- `SpineTyped` is preserved by lifting (needed to state `lift_aux` under the typing guard). -/
theorem SpineTyped.lift {ps : List (WShape n)} : ∀ {k : WShape (n+1)} (le : n ≤ n'),
    SpineTyped (ps.map (·.lift n')) (k.lift (n'+1)) ↔ SpineTyped ps k := by
  induction ps with
  | nil => intros; simp [SpineTyped]
  | cons p ps ih =>
    intro k le
    simp only [List.map_cons, SpineTyped]
    constructor
    · rintro ⟨a₁', f', hk, hp', hty⟩
      obtain ⟨a₁, f, rfl, rfl, rfl⟩ := WShape.lift_eq_forallE le hk
      refine ⟨a₁, f, rfl, (WShape.HasType.lift le).1 hp', (ih le).1 ?_⟩
      rwa [← WShapeFun.lift_app le, WShape.lift_lift (.inl le), ← WShape.lift_lift (n₂ := n+1) (.inl (Nat.le_succ n))] at hty
    · rintro ⟨a₁, f, rfl, hp, hty⟩
      refine ⟨a₁.lift n', f.lift n', WShape.lift_forallE le, (WShape.HasType.lift le).2 hp, ?_⟩
      rw [← WShapeFun.lift_app le, WShape.lift_lift (.inl le), ← WShape.lift_lift (n₂ := n+1) (.inl (Nat.le_succ n))]
      exact (ih le).2 hty

/-- **The new case of `LR.lift_succ_aux`.**  Codes are finite data: `k.lift = forallE (a₁.lift)
(f.lift)` decomposes uniquely, so the only `∀` in the clause ranges over a determined pair and both
directions reduce to the IHs at `(p, a₁)` and `f.app p`.  No non-lift type shape ever appears —
contrast `CounterC.lean`. -/
theorem SpineDefEq.lift_aux {Γ : List SExpr} {xs : List SExpr} : ∀ {n n'} (le : n ≤ n')
    (IH1 : ∀ {M N : SExpr} {m : WShape n}, WShape.HasType m .type →
      ((LR Γ).TyDefEq M N (m.lift n') ↔ (LR Γ).TyDefEq M N m))
    (IH2 : ∀ {M N A : SExpr} {m a : WShape n}, WShape.HasType m a →
      ((LR Γ).DefEq M N A (m.lift n') (a.lift _) ↔ (LR Γ).DefEq M N A m a))
    {ys : List SExpr} {T} {ps : List (WShape n)} {k : WShape (n+1)}, k.HasType .type →
    (SpineDefEq Γ xs ys T (ps.map (·.lift n')) (k.lift (n'+1)) ↔ SpineDefEq Γ xs ys T ps k) := by
  induction xs with
  | nil =>
    intro n n' le IH1 IH2 ys T ps k hk
    cases ys <;> cases ps <;> simp [SpineDefEq]
  | cons x xs ih =>
    intro n n' le IH1 IH2 ys T ps k hk
    cases ys with | nil => cases ps <;> simp [SpineDefEq] | cons y ys
    cases ps with | nil => simp [SpineDefEq] | cons p ps
    simp only [List.map_cons]
    have lift_cod {f : WShapeFun n} :
        ((f.lift n').app (p.lift n')).lift (n'+1) = ((f.app p).lift (n+1)).lift (n'+1) := by
      rw [← WShapeFun.lift_app le, WShape.lift_lift (.inl le), WShape.lift_lift (.inl (Nat.le_succ n))]
    constructor
    · intro H a₁ f hkf hp; subst hkf
      have hk' : (WShape.forallE a₁ f).lift (n'+1) = .forallE (a₁.lift n') (f.lift n') :=
        WShape.lift_forallE le
      obtain ⟨A₁, A₂, u, v, rT, hA₁, hA₂, hxy, t1, d1, d2, d4⟩ :=
        H _ _ hk' ((WShape.HasType.lift le).2 hp)
      have hfp := code_cod hk hp
      refine ⟨A₁, A₂, u, v, rT, hA₁, hA₂, hxy, (IH1 (code_dom hk)).1 t1, (IH2 hp).1 d1,
        (IH1 hfp).1 ?_, (ih le IH1 IH2 (lift_app_type hfp)).1 ?_⟩
      · rwa [← WShapeFun.lift_app le] at d2
      · rwa [lift_cod] at d4
    · intro H a₁' f' hkf' hp'
      obtain ⟨a₁, f, rfl, rfl, rfl⟩ := WShape.lift_eq_forallE le hkf'
      have hp := (WShape.HasType.lift le).1 hp'
      obtain ⟨A₁, A₂, u, v, rT, hA₁, hA₂, hxy, t1, d1, d2, d4⟩ := H _ _ rfl hp
      have hfp := code_cod hk hp
      refine ⟨A₁, A₂, u, v, rT, hA₁, hA₂, hxy, (IH1 (code_dom hk)).2 t1, (IH2 hp).2 d1, ?_, ?_⟩
      · rw [← WShapeFun.lift_app le]; exact (IH1 hfp).2 d2
      · rw [lift_cod]; exact (ih le IH1 IH2 (lift_app_type hfp)).2 d4

/-! ### Head part: `whr`, `left`, `symm`, `trans` for `CtorDefEq` -/

theorem CtorDefEq.whr (hc : Params.classify c = some (.ctor j)) {l : List (WShape n)} {k}
    (hM : Γ ⊢ M ⤳* M') (hN : Γ ⊢ N ⤳* N') :
    CtorDefEq Γ M N c l k ↔ CtorDefEq Γ M' N' c l k := by
  constructor <;> rintro ⟨ls, ci, xs, ys, hci, rM, rN, h⟩
  · exact ⟨ls, ci, xs, ys, hci, hM.determ_l rM (WHNF.ctorApps hc _), hN.determ_l rN (WHNF.ctorApps hc _), h⟩
  · exact ⟨ls, ci, xs, ys, hci, hM.trans rM, hN.trans rN, h⟩

theorem CtorDefEq.left {l : List (WShape n)} {k} :
    CtorDefEq Γ M N c l k → CtorDefEq Γ M M c l k
  | ⟨ls, ci, xs, _, hci, rM, _, h⟩ => ⟨ls, ci, xs, xs, hci, rM, rM, h.left⟩

theorem CtorDefEq.symm {l : List (WShape n)} {k : WShape (n+1)} (hk : k.HasType .type) :
    CtorDefEq Γ M N c l k → CtorDefEq Γ N M c l k
  | ⟨ls, ci, xs, ys, hci, rM, rN, h⟩ => ⟨ls, ci, ys, xs, hci, rN, rM, h.symm hk⟩

theorem CtorDefEq.trans (hc : Params.classify c = some (.ctor j)) {l : List (WShape n)}
    {k : WShape (n+1)} (hk : k.HasType .type) :
    CtorDefEq Γ M₁ M₂ c l k → CtorDefEq Γ M₂ M₃ c l k → CtorDefEq Γ M₁ M₃ c l k
  | ⟨ls, ci, xs, ys, hci, rM₁, rM₂, h⟩, ⟨ls', ci', ys', zs, hci', rM₂', rM₃, h'⟩ => by
    have e1 := rM₂.determ (WHNF.ctorApps hc _) rM₂' (WHNF.ctorApps hc _)
    obtain ⟨-, rfl, e2⟩ := apps_inj e1
    cases List.reverse_inj.1 e2
    cases hci.symm.trans hci'
    exact ⟨ls, ci, xs, zs, hci, rM₁, rM₃, h.trans hk h'⟩

/-- `trans'` at the new clause: with the extra premise `a.HasType (.sort r)` (design A §3.3) the
`ctor` case is impossible, so no `IndTyRed`-style conjunct on the ambient type is needed. -/
theorem trans'_ctor_vacuous {c : Name} {l : List (WShape n)} {h} :
    ¬ (WShape.ctor c l h).HasType (.sort r) := WShape.HasType.ctor_isType

/-! ### Wiring (not typecheckable here: needs `ShapeS.ctor` to carry the code)

```
-- ShapeLogRel.lean, LRS.DefEq (5619):
  | .indTy =>
    match hm : m.1 with
    | .bot => True
    | .ctor c l k => CtorDefEq Γ M N c ⟪l⟫ ⟪k⟫      -- ⟪·⟫ : WShape wrappers from m.2
    | _ => False
-- Shape.hasType (2486):
  | _+1, .ctor _ l k, .indTy => k.hasType .type && spineTyped l k
-- Shape.LE.def / ble: .ctor c l k ≤ .ctor c' l' k' ↔ c = c' ∧ l ≤ l' ∧ k ≤ k'
-- lift: .ctor c (l.map lift) (k.lift); Compat/join pointwise.
-- LogRel.trans' (5290) gains the premise `a.HasType (.sort r)`.
```
-/

end Lean4Lean.SExpr

#print axioms Lean4Lean.SExpr.SpineDefEq.mono
#print axioms Lean4Lean.SExpr.SpineDefEq.lift_aux
#print axioms Lean4Lean.SExpr.SpineDefEq.trans
#print axioms Lean4Lean.SExpr.SpineDefEq.conv
#print axioms Lean4Lean.SExpr.CtorDefEq.trans
#print axioms Lean4Lean.SExpr.CtorDefEq.whr
#print axioms Lean4Lean.SExpr.WHNF.ctorApps
