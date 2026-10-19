import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Synthesizer probe for decision D1 (stage 1a), against HEAD 3c35f59 (/tmp/utt-snap6).

Stage-1a field relation: a constructor field whose declared type is a closed inductive constant
is related at the CANONICAL type shape `indTy`, at every typed element shape below the recorded
field shape (`∀ q ≤ p`).  This is the artifact's `TmEqNat` (LogRel.lean:811) generalised; the
`∀ q ≤ p` form makes `mono_l` trivial without changing `Shape.hasType` (ctor shapes stay typed
at `indTy` unconditionally).  Checked here: the one non-trivial obligation, the new case of
`LR.lift_succ_aux`, in BOTH directions, using only the level-`k` IH (`IH2`), `mono_l`, `bot`.
The proof never inspects the clause at `(q, indTy)`, so it holds for the current LR and for the
new clause alike.  No sorries. -/
namespace Lean4Lean.SExpr
variable [Params]

def FieldRel {Γ : List SExpr} : ∀ {n}, LogRel Γ n → SExpr → SExpr → SExpr → WShape n → Prop
  | 0, _, _, _, _, _ => True
  | _+1, IH, X, Y, T, p => ∀ q, q ≤ p → q.HasType .indTy → IH.DefEq X Y T q .indTy

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

#print axioms FieldRel.lift_aux
end Lean4Lean.SExpr
