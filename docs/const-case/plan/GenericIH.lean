import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Refuter checks for claims C3/C4 (analyst lens `clause`), against HEAD 3c35f59 (/tmp/utt-snap6).

Part 1 (gap, code-read + this file): ClauseA.lean's `SpineDefEq` is stated over the concrete
`LR Γ` and its `conv`/`symm`/`trans` call `LR.TyDefEq.lift (Nat.le_succ n)` (level n -> n+1).
Inside `LRS (IH : LogRel Γ n)` the clause must be stated over an abstract `IH`, where no such lift
exists (no `LogRel` field mentions `LRS.TyDefEq IH`).  Part 1 shows a *two-type* variant
`SpineDefEq2` (each side keeps its own instantiated telescope) whose `left`/`symm`/`trans`/`mono`
are provable for an ABSTRACT `IH` without any lift, and whose `lift_aux` still holds for `LR`.

Part 2 (gap): ClauseA's `CtorDefEq.whr`/`.trans` take `classify c = some (.ctor j)` as a
hypothesis, but the proposed wiring `| .ctor c l k => CtorDefEq Γ M N c l k` supplies none and
`Shape.WF (.ctor c l)` does not constrain `classify c`.  `whr_fails_symb`: for a `symb` constant
with a δ-step to a constructor spine (e.g. `two ⤳ succ (succ zero)`), the `whr` field fails at the
shape `ctor c [] k`.  `CtorDefEq2` stores the classification and its `whr` needs no hypothesis.
No sorries. -/
namespace Lean4Lean.SExpr
variable [Params]

/-! ## Part 1: two-type spine clause over an abstract `IH` -/

def SpineDefEq2 {Γ : List SExpr} {n : Nat} (IH : LogRel Γ n) : List SExpr → List SExpr → SExpr → SExpr →
    List (WShape n) → WShape (n+1) → Prop
  | [], [], _, _, [], _ => True
  | x :: xs, y :: ys, T, T', p :: ps, k =>
    ∀ (a₁ : WShape n) (f : WShapeFun n), k = .forallE a₁ f → p.HasType a₁ →
      ∃ A₁ A₂ A₁' A₂' u, Γ ⊢ T ⤳* .forallE A₁ A₂ ∧ Γ ⊢ T' ⤳* .forallE A₁' A₂' ∧
        Γ ⊢ A₁ ≡ A₁' : .sort u ∧ Γ ⊢ x ≡ y : A₁ ∧
        IH.TyDefEq A₁ A₁' a₁ ∧ IH.DefEq x y A₁ p a₁ ∧
        IH.TyDefEq (A₂.inst x) (A₂'.inst y) (f.app p) ∧
        SpineDefEq2 IH xs ys (A₂.inst x) (A₂'.inst y) ps ((f.app p).lift (n+1))
  | _, _, _, _, _, _ => False

variable {Γ : List SExpr} {n : Nat} (IH : LogRel Γ n)

theorem SpineDefEq2.left : ∀ {xs ys : List SExpr} {T T'} {ps : List (WShape n)} {k : WShape (n+1)},
    SpineDefEq2 IH xs ys T T' ps k → SpineDefEq2 IH xs xs T T ps k
  | [], [], _, _, [], _, _ => trivial
  | _ :: _, _ :: _, _, _, _ :: _, _, h => fun a₁ f hkf hp => by
    obtain ⟨A₁, A₂, _, _, u, rT, _, hAA, hxy, t1, d1, d2, d4⟩ := h a₁ f hkf hp
    exact ⟨A₁, A₂, A₁, A₂, u, rT, rT, hAA.hasType.1, hxy.hasType.1, IH.left_ty t1, IH.left d1,
      IH.left_ty d2, SpineDefEq2.left d4⟩
  | [], _ :: _, _, _, _, _, h | _ :: _, [], _, _, _, _, h | [], [], _, _, _ :: _, _, h
  | _ :: _, _ :: _, _, _, [], _, h => h.elim

theorem SpineDefEq2.symm : ∀ {xs ys : List SExpr} {T T'} {ps : List (WShape n)} {k : WShape (n+1)},
    SpineDefEq2 IH xs ys T T' ps k → SpineDefEq2 IH ys xs T' T ps k
  | [], [], _, _, [], _, _ => trivial
  | _ :: _, _ :: _, _, _, _ :: _, _, h => fun a₁ f hkf hp => by
    obtain ⟨A₁, A₂, A₁', A₂', u, rT, rT', hAA, hxy, t1, d1, d2, d4⟩ := h a₁ f hkf hp
    exact ⟨A₁', A₂', A₁, A₂, u, rT', rT, hAA.symm, hAA.defeqDF hxy.symm, IH.symm_ty t1,
      IH.conv t1 (IH.symm d1), IH.symm_ty d2, SpineDefEq2.symm d4⟩
  | [], _ :: _, _, _, _, _, h | _ :: _, [], _, _, _, _, h | [], [], _, _, _ :: _, _, h
  | _ :: _, _ :: _, _, _, [], _, h => h.elim

theorem SpineDefEq2.trans : ∀ {xs ys zs : List SExpr} {T T' T''} {ps : List (WShape n)}
    {k : WShape (n+1)},
    SpineDefEq2 IH xs ys T T' ps k → SpineDefEq2 IH ys zs T' T'' ps k →
    SpineDefEq2 IH xs zs T T'' ps k
  | [], [], [], _, _, _, [], _, _, _ => trivial
  | _ :: _, _ :: _, _ :: _, _, _, _, _ :: _, _, h1, h2 => fun a₁ f hkf hp => by
    obtain ⟨A₁, A₂, A₁', A₂', u, rT, rT', hAA, hxy, t1, d1, d2, d4⟩ := h1 a₁ f hkf hp
    obtain ⟨B₁, B₂, B₁', B₂', u', sT', sT'', hBB, hyz, t1', e1, e2, e4⟩ := h2 a₁ f hkf hp
    cases rT'.determ .forallE sT' .forallE
    exact ⟨A₁, A₂, B₁', B₂', u, rT, sT'', hAA.trans' hBB, hxy.trans (hAA.symm.defeqDF hyz),
      IH.trans_ty t1 t1', IH.trans d1 (IH.conv (IH.symm_ty t1) e1), IH.trans_ty d2 e2,
      SpineDefEq2.trans d4 e4⟩
  | [], _ :: _, _, _, _, _, _, _, h, _ | _ :: _, [], _, _, _, _, _, _, h, _
  | [], [], _ :: _, _, _, _, _, _, _, h | _ :: _, _ :: _, [], _, _, _, _, _, _, h
  | [], [], [], _, _, _, _ :: _, _, h, _ | _ :: _, _ :: _, _ :: _, _, _, _, [], _, h, _ => h.elim

theorem code_parts {a₁ : WShape n} {f : WShapeFun n} (hk : (WShape.forallE a₁ f).HasType .type) :
    WShape.HasTypePi f a₁ true := by
  obtain ⟨_, htpi, _⟩ := WShape.HasType.forallE_l.1 hk; exact htpi.toType
theorem code_dom {a₁ : WShape n} {f : WShapeFun n} (hk : (WShape.forallE a₁ f).HasType .type) :
    a₁.HasType .type := (WShape.HasTypePi.iff.1 (code_parts hk)).1.isType
theorem code_cod {a₁ : WShape n} {f : WShapeFun n} (hk : (WShape.forallE a₁ f).HasType .type)
    (hp : p.HasType a₁) : (f.app p).HasType .type := (WShape.HasTypePi.iff.1 (code_parts hk)).2 _ hp
theorem lift_app_type {f : WShapeFun n} {p : WShape n}
    (h : (f.app p).HasType .type) : ((f.app p).lift (n+1)).HasType .type := by
  have := (WShape.HasType.lift (Nat.le_succ n)).2 h; rwa [WShape.lift_sort] at this

/-- `SpineTyped` exactly as in ClauseA.lean. -/
def SpineTyped : ∀ {n}, List (WShape n) → WShape (n+1) → Prop
  | _, [], _ => True
  | n, p :: ps, k => ∃ (a₁ : WShape n) (f : WShapeFun n),
      k = .forallE a₁ f ∧ p.HasType a₁ ∧ SpineTyped ps ((f.app p).lift (n+1))

/-- `mono_l` at the clause, abstract `IH`. -/
theorem SpineDefEq2.mono : ∀ {xs ys : List SExpr} {T T'} {ps ps' : List (WShape n)}
    {k k' : WShape (n+1)},
    List.Forall₂ (· ≤ ·) ps ps' → k ≤ k' → k.HasType .type → k'.HasType .type →
    SpineTyped ps k → SpineTyped ps' k' →
    SpineDefEq2 IH xs ys T T' ps' k' → SpineDefEq2 IH xs ys T T' ps k
  | [], [], _, _, _, _, _, _, hle, _, _, _, _, _, _ => by cases hle <;> trivial
  | _ :: _, _ :: _, _, _, _, _, _, _, .cons hpp hle, hkk, hk, hk', hty, hty', h => by
    intro a₁ f hkf hp; subst hkf
    simp only [SpineTyped] at hty hty'
    obtain ⟨a₁', f', rfl, hp', hty'⟩ := hty'
    obtain ⟨a₁₀, f₀, e, -, hty⟩ := hty
    obtain ⟨rfl, rfl⟩ := WShape.forallE.inj.1 e
    have ⟨le_a, le_f⟩ := WShape.forallE_le_forallE.1 hkk
    obtain ⟨A₁, A₂, A₁', A₂', u, rT, rT', hAA, hxy, t1, d1, d2, d4⟩ := h _ _ rfl hp'
    have ha₁ := code_dom hk; have ha₁' := code_dom hk'
    have hfp := code_cod hk hp; have hfp' := code_cod hk' hp'
    have hp_a₁' := WShape.HasType.mono_r le_a ha₁' hp
    have le_cod := (WShapeFun.app_mono_l le_f _).trans (WShapeFun.app_mono_r hpp)
    exact ⟨A₁, A₂, A₁', A₂', u, rT, rT', hAA, hxy, IH.mono_r_2_ty le_a ha₁ ha₁' t1,
      IH.mono_r_2 le_a hp ha₁' (IH.mono_l hpp hp_a₁' hp' d1), IH.mono_r_2_ty le_cod hfp hfp' d2,
      SpineDefEq2.mono hle (WShape.lift_mono (Nat.le_succ n) le_cod) (lift_app_type hfp)
        (lift_app_type hfp') hty hty' d4⟩
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, _, _, h | _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, h
  | _ :: _, _ :: _, _, _, _, _, _, _, .nil, _, _, _, _, _, h => h.elim


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

/-- Lift invariance of the two-type clause (the new case of `LR.lift_succ_aux`). -/
theorem SpineDefEq2.lift_aux {Γ : List SExpr} : ∀ {xs : List SExpr} {n n'} (le : n ≤ n')
    (IH1 : ∀ {M N : SExpr} {m : WShape n}, WShape.HasType m .type →
      ((LR Γ).TyDefEq M N (m.lift n') ↔ (LR Γ).TyDefEq M N m))
    (IH2 : ∀ {M N A : SExpr} {m a : WShape n}, WShape.HasType m a →
      ((LR Γ).DefEq M N A (m.lift n') (a.lift _) ↔ (LR Γ).DefEq M N A m a))
    {ys : List SExpr} {T T'} {ps : List (WShape n)} {k : WShape (n+1)}, k.HasType .type →
    (SpineDefEq2 (LR Γ) xs ys T T' (ps.map (·.lift n')) (k.lift (n'+1)) ↔
      SpineDefEq2 (LR Γ) xs ys T T' ps k)
  | [], _, _, _, _, _, ys, _, _, ps, _, _ => by cases ys <;> cases ps <;> simp [SpineDefEq2]
  | x :: xs, n, n', le, IH1, IH2, ys, T, T', ps, k, hk => by
    cases ys with | nil => cases ps <;> simp [SpineDefEq2] | cons y ys
    cases ps with | nil => simp [SpineDefEq2] | cons p ps
    simp only [List.map_cons]
    have lift_cod {f : WShapeFun n} :
        ((f.lift n').app (p.lift n')).lift (n'+1) = ((f.app p).lift (n+1)).lift (n'+1) := by
      rw [← WShapeFun.lift_app le, WShape.lift_lift (.inl le), WShape.lift_lift (.inl (Nat.le_succ n))]
    constructor
    · intro H a₁ f hkf hp; subst hkf
      obtain ⟨A₁, A₂, A₁', A₂', u, rT, rT', hAA, hxy, t1, d1, d2, d4⟩ :=
        H _ _ (WShape.lift_forallE le) ((WShape.HasType.lift le).2 hp)
      have hfp := code_cod hk hp
      refine ⟨A₁, A₂, A₁', A₂', u, rT, rT', hAA, hxy, (IH1 (code_dom hk)).1 t1, (IH2 hp).1 d1,
        (IH1 hfp).1 ?_, (SpineDefEq2.lift_aux le IH1 IH2 (lift_app_type hfp)).1 ?_⟩
      · rwa [← WShapeFun.lift_app le] at d2
      · rwa [lift_cod] at d4
    · intro H a₁' f' hkf' hp'
      obtain ⟨a₁, f, rfl, rfl, rfl⟩ := WShape.lift_eq_forallE le hkf'
      have hp := (WShape.HasType.lift le).1 hp'
      obtain ⟨A₁, A₂, A₁', A₂', u, rT, rT', hAA, hxy, t1, d1, d2, d4⟩ := H _ _ rfl hp
      have hfp := code_cod hk hp
      refine ⟨A₁, A₂, A₁', A₂', u, rT, rT', hAA, hxy, (IH1 (code_dom hk)).2 t1, (IH2 hp).2 d1, ?_, ?_⟩
      · rw [← WShapeFun.lift_app le]; exact (IH1 hfp).2 d2
      · rw [lift_cod]; exact (SpineDefEq2.lift_aux le IH1 IH2 (lift_app_type hfp)).2 d4

/-- The two-type head part.  Classification is stored, so `whr` needs no hypothesis. -/
def CtorDefEq2 (M N : SExpr) (c : Name) (l : List (WShape n)) (k : WShape (n+1)) : Prop :=
  ∃ (j : Nat) (ls : List SLevel) (ci : VConstant) (xs ys : List SExpr),
    Params.classify c = some (.ctor j) ∧ Params.env.constants c = some ci ∧
    Γ ⊢ M ⤳* spine (.const c ls) xs ∧ Γ ⊢ N ⤳* spine (.const c ls) ys ∧
    SpineDefEq2 IH xs ys (SExpr.mkInst ls ci.type) (SExpr.mkInst ls ci.type) l k

theorem CtorDefEq2.whr (hM : Γ ⊢ M ⤳* M') (hN : Γ ⊢ N ⤳* N') :
    CtorDefEq2 IH M N c l k ↔ CtorDefEq2 IH M' N' c l k := by
  constructor <;> rintro ⟨j, ls, ci, xs, ys, hc, hci, rM, rN, h⟩
  · exact ⟨j, ls, ci, xs, ys, hc, hci, hM.determ_l rM (WHNF.ctorSpine hc _),
      hN.determ_l rN (WHNF.ctorSpine hc _), h⟩
  · exact ⟨j, ls, ci, xs, ys, hc, hci, hM.trans rM, hN.trans rN, h⟩

theorem CtorDefEq2.left : CtorDefEq2 IH M N c l k → CtorDefEq2 IH M M c l k
  | ⟨j, ls, ci, xs, _, hc, hci, rM, _, h⟩ => ⟨j, ls, ci, xs, xs, hc, hci, rM, rM, h.left⟩

theorem CtorDefEq2.symm : CtorDefEq2 IH M N c l k → CtorDefEq2 IH N M c l k
  | ⟨j, ls, ci, xs, ys, hc, hci, rM, rN, h⟩ => ⟨j, ls, ci, ys, xs, hc, hci, rN, rM, h.symm⟩

theorem CtorDefEq2.trans :
    CtorDefEq2 IH M₁ M₂ c l k → CtorDefEq2 IH M₂ M₃ c l k → CtorDefEq2 IH M₁ M₃ c l k
  | ⟨j, ls, ci, xs, ys, hc, hci, rM₁, rM₂, h⟩, ⟨_, ls', ci', ys', zs, _, hci', rM₂', rM₃, h'⟩ => by
    obtain ⟨rfl, rfl⟩ := WHRedS.ctorSpine_determ hc rM₂ rM₂'
    cases hci.symm.trans hci'
    exact ⟨j, ls, ci, xs, zs, hc, hci, rM₁, rM₃, SpineDefEq2.trans IH h h'⟩

/-! ## Part 2: ClauseA's `CtorDefEq` (verbatim, renamed) violates the `whr` field at `symb` names -/

abbrev appsA (c : Name) (ls : List SLevel) (args : List SExpr) : SExpr :=
  args.foldr (fun a acc => SExpr.app acc a) (SExpr.const c ls)

def SpineDefEqA (Γ : List SExpr) : ∀ {n}, List SExpr → List SExpr → SExpr →
    List (WShape n) → WShape (n+1) → Prop
  | _, [], [], _, [], _ => True
  | n, x :: xs, y :: ys, T, p :: ps, k =>
    ∀ (a₁ : WShape n) (f : WShapeFun n), k = .forallE a₁ f → p.HasType a₁ →
      ∃ A₁ A₂ u v, Γ ⊢ T ⤳* .forallE A₁ A₂ ∧ Γ ⊢ A₁ : .sort u ∧ A₁::Γ ⊢ A₂ : .sort v ∧
        Γ ⊢ x ≡ y : A₁ ∧
        (LR Γ).TyDefEq A₁ A₁ a₁ ∧
        (LR Γ).DefEq x y A₁ p a₁ ∧
        (LR Γ).TyDefEq (A₂.inst x) (A₂.inst y) (f.app p) ∧
        SpineDefEqA Γ xs ys (A₂.inst x) ps ((f.app p).lift (n+1))
  | _, _, _, _, _, _ => False

def CtorDefEqA (Γ : List SExpr) {n} (M N : SExpr) (c : Name) (l : List (WShape n))
    (k : WShape (n+1)) : Prop :=
  ∃ (ls : List SLevel) (ci : VConstant) (xs ys : List SExpr),
    Params.env.constants c = some ci ∧
    Γ ⊢ M ⤳* appsA c ls xs.reverse ∧ Γ ⊢ N ⤳* appsA c ls ys.reverse ∧
    SpineDefEqA Γ xs ys (SExpr.mkInst ls ci.type) l k

/-- If `const c ls` takes a whnf step to a constructor spine headed by `c' ≠ c` (any δ-rule
`c := c' …` of a definition whose body is a constructor application), the `whr` field fails for
ClauseA's clause at the nullary ctor shape named `c`. -/
theorem whr_fails_symb {Γ : List SExpr} {n} {k : WShape (n+1)} {c c' : Name} {ci} {ls ls' : List SLevel}
    {v : SExpr} {Xs : List SExpr} {j : Nat}
    (hci : Params.env.constants c = some ci) (hstep : Γ ⊢ .const c ls ⤳ v)
    (hv : v = spine (.const c' ls') Xs) (hc' : Params.classify c' = some (.ctor j)) (hne : c' ≠ c) :
    ¬ (∀ {M N M' N' : SExpr}, Γ ⊢ M ⤳* M' → Γ ⊢ N ⤳* N' →
        (CtorDefEqA Γ M N c ([] : List (WShape n)) k ↔ CtorDefEqA Γ M' N' c [] k)) := by
  intro H
  have h0 : CtorDefEqA Γ (.const c ls) (.const c ls) c ([] : List (WShape n)) k :=
    ⟨ls, ci, [], [], hci, .rfl, .rfl, by simp [SpineDefEqA]⟩
  obtain ⟨ls₁, _, xs, ys, _, rM, _, hS⟩ := (H (.tail .rfl hstep) (.tail .rfl hstep)).1 h0
  cases xs with
  | cons x xs => cases ys <;> simp [SpineDefEqA] at hS
  | nil =>
    subst hv
    have e := (WHNF.ctorSpine (ls := ls') hc' Xs).whRedS rM
    have := (spine_inj (Xs' := []) (e.trans (by rfl))).1
    exact hne this

end Lean4Lean.SExpr
#print axioms Lean4Lean.SExpr.SpineDefEq2.trans
#print axioms Lean4Lean.SExpr.SpineDefEq2.symm
#print axioms Lean4Lean.SExpr.SpineDefEq2.mono
#print axioms Lean4Lean.SExpr.SpineDefEq2.lift_aux
#print axioms Lean4Lean.SExpr.CtorDefEq2.whr
#print axioms Lean4Lean.SExpr.CtorDefEq2.trans
#print axioms Lean4Lean.SExpr.whr_fails_symb
