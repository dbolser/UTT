import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Synthesizer probe for decisions D1/D2/D6 (stage 1a), against HEAD 3c35f59 (/tmp/utt-snap6).

The stage-1a `(ctor c l, indTy)` clause, stated over an ABSTRACT `IH : LogRel Γ n` (so it can be
placed inside `LRS`), with TYPED reductions (paper: "we build the conversion into the definition
because subject reduction is not yet available"; artifact `TypedWHRedS`, LogRel.lean:29) and
fields at the canonical type shape `indTy` (`FieldRel`, `∀ q ≤ p` form).  Proven here, sorry-free:
`left`, `symm`, `trans`, `mono_l` (no field-typing hypotheses needed), typed `whr` (both
directions), `conv` along the stage-1a `TyDefEq` at `indTy`, `trans'`-vacuity at a sort ambient
(no new `trans'` premise), and the new case of `LR.lift_succ_aux` (`CtorDefEq1a.lift_aux`).
The `LogRel` fields `whr`/`conv` are taken as explicit hypotheses where the clause needs them;
nothing here depends on the current (untyped) `LRS` instance. -/
namespace Lean4Lean.SExpr
variable [Params]

/-- typed type reduction at some sort -/
def TyRedS (Γ : List SExpr) (A A' : SExpr) : Prop := (∃ w, Γ ⊢ A ≡ A' : .sort w) ∧ Γ ⊢ A ⤳* A'
/-- typed term reduction at the ambient type -/
def TWHRedS (Γ : List SExpr) (M M' A : SExpr) : Prop := Γ ⊢ M ≡ M' : A ∧ Γ ⊢ M ⤳* M'

def FieldRel {Γ : List SExpr} : ∀ {n}, LogRel Γ n → SExpr → SExpr → SExpr → WShape n → Prop
  | 0, _, _, _, _, _ => True
  | _+1, IH, X, Y, T, p => ∀ q, q ≤ p → q.HasType .indTy → IH.DefEq X Y T q .indTy

inductive FieldsEq {Γ : List SExpr} {n} (IH : LogRel Γ n) :
    List SExpr → List SExpr → List SExpr → List (WShape n) → Prop
  | nil : FieldsEq IH [] [] [] []
  | cons {T X Y : SExpr} {p : WShape n} {Ts Xs Ys l} :
    Γ ⊢ X ≡ Y : T → FieldRel IH X Y T p → FieldsEq IH Ts Xs Ys l →
    FieldsEq IH (T :: Ts) (X :: Xs) (Y :: Ys) (p :: l)

/-- Stage-1a clause at `(ctor c l, indTy)`.  `Ts` are the (closed, stage-1a) field types. -/
def CtorDefEq1a {Γ : List SExpr} {n} (IH : LogRel Γ n) (M N A : SExpr) (c : Name)
    (l : List (WShape n)) : Prop :=
  ∃ (I : Name) (ls : List SLevel) (ci : VConstant) (Ts Xs Ys : List SExpr),
    Params.classify c = some (.ctor l.length) ∧ Params.classify I = some (.indTy 0) ∧
    Params.env.constants c = some ci ∧ SExpr.mkInst ls ci.type = Ts.foldr .forallE (.const I ls) ∧
    TyRedS Γ A (.const I ls) ∧
    TWHRedS Γ M (spine (.const c ls) Xs) A ∧ TWHRedS Γ N (spine (.const c ls) Ys) A ∧
    FieldsEq IH Ts Xs Ys l

/-- Stage-1a `TyDefEq` at `indTy`. -/
def IndTyEq1a (Γ : List SExpr) (M N : SExpr) : Prop :=
  ∃ (I : Name) (ls : List SLevel), Params.classify I = some (.indTy 0) ∧
    TyRedS Γ M (.const I ls) ∧ TyRedS Γ N (.const I ls)

theorem foldr_forallE_const_inj : ∀ {Ts Ts' : List SExpr} {I I' : Name} {ls ls' : List SLevel},
    Ts.foldr SExpr.forallE (SExpr.const I ls) = Ts'.foldr SExpr.forallE (SExpr.const I' ls') →
    Ts = Ts' ∧ I = I' ∧ ls = ls'
  | [], [], _, _, _, _, h => by cases h; exact ⟨rfl, rfl, rfl⟩
  | _ :: _, [], _, _, _, _, h | [], _ :: _, _, _, _, _, h => by cases h
  | _ :: _, _ :: _, _, _, _, _, h => by
    simp only [List.foldr_cons, SExpr.forallE.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := foldr_forallE_const_inj h
    exact ⟨rfl, rfl, rfl⟩

section
variable {Γ : List SExpr} {n : Nat} {IH : LogRel Γ n}

theorem FieldRel.left : ∀ {n} {IH : LogRel Γ n} {X Y T p}, FieldRel IH X Y T p → FieldRel IH X X T p
  | 0, _, _, _, _, _, _ => trivial
  | _+1, IH, _, _, _, _, h => fun q hq ht => IH.left (h q hq ht)
theorem FieldRel.symm : ∀ {n} {IH : LogRel Γ n} {X Y T p}, FieldRel IH X Y T p → FieldRel IH Y X T p
  | 0, _, _, _, _, _, _ => trivial
  | _+1, IH, _, _, _, _, h => fun q hq ht => IH.symm (h q hq ht)
theorem FieldRel.trans : ∀ {n} {IH : LogRel Γ n} {X Y Z T p},
    FieldRel IH X Y T p → FieldRel IH Y Z T p → FieldRel IH X Z T p
  | 0, _, _, _, _, _, _, _, _ => trivial
  | _+1, IH, _, _, _, _, _, h, g => fun q hq ht => IH.trans (h q hq ht) (g q hq ht)
theorem FieldRel.mono : ∀ {n} {IH : LogRel Γ n} {X Y T} {p p' : WShape n},
    p ≤ p' → FieldRel IH X Y T p' → FieldRel IH X Y T p
  | 0, _, _, _, _, _, _, _, _ => trivial
  | _+1, _, _, _, _, _, _, le, h => fun q hq ht => h q (hq.trans le) ht

theorem FieldsEq.left : FieldsEq IH Ts Xs Ys l → FieldsEq IH Ts Xs Xs l := by
  intro H; induction H with
  | nil => exact .nil
  | cons h1 h2 _ ih => exact .cons h1.hasType.1 h2.left ih
theorem FieldsEq.symm : FieldsEq IH Ts Xs Ys l → FieldsEq IH Ts Ys Xs l := by
  intro H; induction H with
  | nil => exact .nil
  | cons h1 h2 _ ih => exact .cons h1.symm h2.symm ih
theorem FieldsEq.trans : FieldsEq IH Ts Xs Ys l → FieldsEq IH Ts Ys Zs l → FieldsEq IH Ts Xs Zs l := by
  intro H1 H2; induction H1 generalizing Zs with
  | nil => cases H2; exact .nil
  | cons h1 h2 _ ih => cases H2 with | cons g1 g2 g3 => exact .cons (h1.trans g1) (h2.trans g2) (ih g3)
theorem FieldsEq.mono : List.Forall₂ (· ≤ ·) l l' → FieldsEq IH Ts Xs Ys l' → FieldsEq IH Ts Xs Ys l := by
  intro hle H; induction H generalizing l with
  | nil => cases hle; exact .nil
  | cons h1 h2 _ ih => cases hle with | cons a b => exact .cons h1 (h2.mono a) (ih b)

theorem CtorDefEq1a.left : CtorDefEq1a IH M N A c l → CtorDefEq1a IH M M A c l
  | ⟨I, ls, ci, Ts, Xs, _, hc, hI, hci, hty, hA, hM, _, hF⟩ =>
    ⟨I, ls, ci, Ts, Xs, Xs, hc, hI, hci, hty, hA, hM, hM, hF.left⟩
theorem CtorDefEq1a.symm : CtorDefEq1a IH M N A c l → CtorDefEq1a IH N M A c l
  | ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, hA, hM, hN, hF⟩ =>
    ⟨I, ls, ci, Ts, Ys, Xs, hc, hI, hci, hty, hA, hN, hM, hF.symm⟩
theorem CtorDefEq1a.trans : CtorDefEq1a IH M₁ M₂ A c l → CtorDefEq1a IH M₂ M₃ A c l →
    CtorDefEq1a IH M₁ M₃ A c l
  | ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, hA, hM₁, hM₂, hF⟩,
    ⟨_, ls', ci', Ts', Ys', Zs, _, _, hci', hty', _, hM₂', hM₃, hF'⟩ => by
    obtain ⟨rfl, rfl⟩ := WHRedS.ctorSpine_determ hc hM₂.2 hM₂'.2
    cases hci.symm.trans hci'
    obtain ⟨rfl, rfl, -⟩ := foldr_forallE_const_inj (hty.symm.trans hty')
    exact ⟨I, ls, ci, Ts, Xs, Zs, hc, hI, hci, hty, hA, hM₁, hM₃, hF.trans hF'⟩
theorem CtorDefEq1a.mono_l (hle : List.Forall₂ (· ≤ ·) l l') :
    CtorDefEq1a IH M N A c l' → CtorDefEq1a IH M N A c l
  | ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, hA, hM, hN, hF⟩ =>
    ⟨I, ls, ci, Ts, Xs, Ys, (Lean4Lean.List.Forall₂.length_eq hle).symm ▸ hc, hI, hci, hty, hA, hM, hN, hF.mono hle⟩

/-- `whr` with TYPED reductions at the ambient type. -/
theorem CtorDefEq1a.whr (hM : TWHRedS Γ M M' A) (hN : TWHRedS Γ N N' A) :
    CtorDefEq1a IH M N A c l ↔ CtorDefEq1a IH M' N' A c l := by
  constructor
  · intro ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, hA, hMs, hNs, hF⟩
    refine ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, hA, ⟨hM.1.symm.trans hMs.1, ?_⟩,
      ⟨hN.1.symm.trans hNs.1, ?_⟩, hF⟩
    · exact hM.2.determ_l hMs.2 (WHNF.ctorSpine hc Xs)
    · exact hN.2.determ_l hNs.2 (WHNF.ctorSpine hc Ys)
  · intro ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, hA, hMs, hNs, hF⟩
    exact ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, hA, ⟨hM.1.trans hMs.1, hM.2.trans hMs.2⟩,
      ⟨hN.1.trans hNs.1, hN.2.trans hNs.2⟩, hF⟩

/-- `conv` along the stage-1a `TyDefEq` at `indTy`; the typed `A ≡ B` comes from the clause. -/
theorem CtorDefEq1a.conv (hAB : IndTyEq1a Γ A B) : CtorDefEq1a IH M N A c l → CtorDefEq1a IH M N B c l
  | ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, hA, hM, hN, hF⟩ => by
    obtain ⟨I', ls', hI', ⟨⟨w₁, eA⟩, rA⟩, ⟨⟨w₂, eB⟩, rB⟩⟩ := hAB
    have e := hA.2.determ (WHNF.indTySpine (Xs := []) hI) rA (WHNF.indTySpine (Xs := []) hI')
    cases e
    have hAB' : Γ ⊢ A ≡ B : .sort w₁ := eA.trans' eB.symm
    exact ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, ⟨⟨w₂, eB⟩, rB⟩,
      ⟨hAB'.defeqDF hM.1, hM.2⟩, ⟨hAB'.defeqDF hN.1, hN.2⟩, hF⟩

/-- `trans'` needs no new premise: a sort ambient cannot reduce to an inductive constant. -/
theorem CtorDefEq1a.not_sort : ¬ CtorDefEq1a IH M N (.sort u) c l
  | ⟨_, _, _, _, _, _, _, _, _, _, ⟨_, rA⟩, _⟩ => by cases WHNF.sort.whRedS rA

end

/-- The new case of `LR.lift_succ_aux` for the clause (both directions). -/
theorem FieldRel.lift_aux {Γ : List SExpr} {X Y T : SExpr} : ∀ {k} {p : WShape k},
    (∀ {M N A : SExpr} {m a : WShape k}, m.HasType a →
      ((LR Γ (n := k+1)).DefEq M N A (m.lift (k+1)) (a.lift (k+1)) ↔ (LR Γ (n := k)).DefEq M N A m a)) →
    (FieldRel (LR Γ (n := k+1)) X Y T (p.lift (k+1)) ↔ FieldRel (LR Γ (n := k)) X Y T p)
  | 0, p, _ => by
    refine ⟨fun _ => trivial, fun _ q hq ht => ?_⟩
    cases ht.unfold with
    | bot _ => exact (LR Γ).bot .indTy
    | @ctor _ c l wf =>
      exfalso
      obtain ⟨_, _, he, _⟩ := WShape.ctor_le.1 hq
      cases p using WShape.casesOn with
      | bot => rw [WShape.lift_bot] at he; cases congrArg (·.1) he
      | sort => rw [WShape.lift_sort] at he; cases congrArg (·.1) he
  | j+1, p, IH2 => by
    constructor
    · intro H q₀ hq₀ ht₀
      have hl : (q₀.lift (j+2)).HasType ((WShape.indTy : WShape (j+1)).lift (j+2)) :=
        (WShape.HasType.lift (Nat.le_succ _)).2 ht₀
      rw [WShape.lift_indTy] at hl
      have := H _ (WShape.lift_mono (Nat.le_succ _) hq₀) hl
      rw [← WShape.lift_indTy (n := j) (m := j+1)] at this
      exact (IH2 ht₀).1 this
    · intro H q hq ht
      cases ht.unfold with
      | bot _ => exact (LR Γ).bot .indTy
      | @ctor _ c l wf =>
        obtain ⟨l', h', he, _⟩ := WShape.ctor_le.1 hq
        have hpl : (p.lift (j+2)).HasType ((WShape.indTy : WShape (j+1)).lift (j+2)) := by
          rw [WShape.lift_indTy, he]; exact .ctor
        have hp : p.HasType .indTy := (WShape.HasType.lift (Nat.le_succ _)).1 hpl
        have d := (IH2 hp).2 (H p .rfl hp)
        rw [WShape.lift_indTy] at d hpl
        exact (LR Γ).mono_l hq ht hpl d

theorem FieldsEq.lift_aux {Γ : List SExpr} {k}
    (IH2 : ∀ {M N A : SExpr} {m a : WShape k}, m.HasType a →
      ((LR Γ (n := k+1)).DefEq M N A (m.lift (k+1)) (a.lift (k+1)) ↔ (LR Γ (n := k)).DefEq M N A m a)) :
    ∀ {Ts Xs Ys : List SExpr} {l : List (WShape k)},
    FieldsEq (LR Γ (n := k+1)) Ts Xs Ys (l.map (·.lift (k+1))) ↔ FieldsEq (LR Γ (n := k)) Ts Xs Ys l
  | [], [], [], [] => ⟨fun _ => .nil, fun _ => .nil⟩
  | T :: Ts, X :: Xs, Y :: Ys, p :: l => by
    constructor
    · intro H; cases H with
      | cons h1 h2 h3 => exact .cons h1 ((FieldRel.lift_aux IH2).1 h2) ((FieldsEq.lift_aux IH2).1 h3)
    · intro H; cases H with
      | cons h1 h2 h3 => exact .cons h1 ((FieldRel.lift_aux IH2).2 h2) ((FieldsEq.lift_aux IH2).2 h3)
  | [], _ :: _, _, _ | [], [], _ :: _, _ | [], [], [], _ :: _ => ⟨nofun, nofun⟩
  | _ :: _, [], _, _ | _ :: _, _ :: _, [], _ | _ :: _, _ :: _, _ :: _, [] => ⟨nofun, nofun⟩

theorem CtorDefEq1a.lift_aux {Γ : List SExpr} {k} {M N A : SExpr} {c : Name} {l : List (WShape k)}
    (IH2 : ∀ {M N A : SExpr} {m a : WShape k}, m.HasType a →
      ((LR Γ (n := k+1)).DefEq M N A (m.lift (k+1)) (a.lift (k+1)) ↔ (LR Γ (n := k)).DefEq M N A m a)) :
    CtorDefEq1a (LR Γ (n := k+1)) M N A c (l.map (·.lift (k+1))) ↔ CtorDefEq1a (LR Γ (n := k)) M N A c l := by
  constructor
  · intro ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, hA, hM, hN, hF⟩
    exact ⟨I, ls, ci, Ts, Xs, Ys, by simpa using hc, hI, hci, hty, hA, hM, hN, (FieldsEq.lift_aux IH2).1 hF⟩
  · intro ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, hA, hM, hN, hF⟩
    exact ⟨I, ls, ci, Ts, Xs, Ys, by simpa using hc, hI, hci, hty, hA, hM, hN, (FieldsEq.lift_aux IH2).2 hF⟩

#print axioms CtorDefEq1a.trans
#print axioms CtorDefEq1a.whr
#print axioms CtorDefEq1a.conv
#print axioms CtorDefEq1a.not_sort
#print axioms CtorDefEq1a.mono_l
#print axioms CtorDefEq1a.lift_aux
end Lean4Lean.SExpr
