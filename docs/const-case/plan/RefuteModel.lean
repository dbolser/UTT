import Lean4Lean.Experimental.ShapeLogRelAdequacy
namespace Lean4Lean.SExpr
variable [Params]

/-! Refuter (proof-theoretic) checks of /tmp/utt-exp/plan/dossier/analyze-model.json.
Checked against /tmp/utt-snap6 (HEAD 3c35f59).  No sorries in this file. -/

/-! ## §1  C3, valuation half: REFUTED.
`LE_Interp.mono_l : ρ.LE ρ' → LE_Interp ρ m M → LE_Interp ρ' m M`.  In `LogRel.mono_l` we are
GIVEN the clause at the bigger fields `l'` and must PRODUCE it at `l ≤ l'`.  The `l`-goal hands
us validity under the smaller valuation `push l`, the `l'`-hypothesis consumes validity under
`push l'`; `mono_l` goes exactly that way.  Clause = design C's `CtorArgsEq` with only the
`∀ q ≤ p` change; valuation still built from the field shapes; nothing stored. -/
inductive CtorArgsEq' (IH : LogRel Γ n) :
    List SExpr → List SExpr → List SExpr → List (WShape n) → Valuation → Subst → Subst → Prop
  | nil : CtorArgsEq' IH [] [] [] [] ρ σ σ'
  | cons {T Ts X Xs Y Ys} {p : WShape n} {l ρ σ σ'} :
    (∃ u, Γ ⊢ T.subst σ ≡ T.subst σ' : .sort u) →
    (∀ a : WShape n, LE_Interp ρ a.T T → a.HasType .type →
      IH.TyDefEq (T.subst σ) (T.subst σ') a) →
    Γ ⊢ X ≡ Y : T.subst σ →
    (∀ a : WShape n, LE_Interp ρ a.T T → ∀ q, q ≤ p → q.HasType a →
      IH.DefEq X Y (T.subst σ) q a) →
    CtorArgsEq' IH Ts Xs Ys l (ρ.push p.T) (σ.cons X) (σ'.cons Y) →
    CtorArgsEq' IH (T :: Ts) (X :: Xs) (Y :: Ys) (p :: l) ρ σ σ'

theorem CtorArgsEq'.mono_l {IH : LogRel Γ n} {l l' : List (WShape n)} {ρ ρ' : Valuation} :
    CtorArgsEq' IH Ts Xs Ys l' ρ' σ σ' → ρ.LE ρ' → List.Forall₂ (· ≤ ·) l l' →
    CtorArgsEq' IH Ts Xs Ys l ρ σ σ' := by
  intro H; induction H generalizing l ρ with
  | nil => intro _ hl; cases hl; exact .nil
  | cons h1 h2 h3 h4 _ ih =>
    intro hρ hl; cases hl with | cons hp hl =>
    exact .cons h1 (fun a ha ht => h2 a (ha.mono_l hρ) ht) h3
      (fun a ha q hq hqa => h4 a (ha.mono_l hρ) q (hq.trans hp) hqa)
      (ih (Valuation.LE.push.2 ⟨hρ, hp.T⟩) hl)

/-- The top-level form `LRS.mono_l` needs: valuation `.nil` at both ends. -/
theorem CtorArgsEq'.mono_l_nil {IH : LogRel Γ n} {l l' : List (WShape n)}
    (H : CtorArgsEq' IH Ts Xs Ys l' .nil σ σ') (hl : List.Forall₂ (· ≤ ·) l l') :
    CtorArgsEq' IH Ts Xs Ys l .nil σ σ' := H.mono_l .rfl hl

/-! ## §2  C3, HasType half: UPHELD.  `p ≤ p'`, `p : a`, `¬ p' : a` (all WF). -/
def a_ex : Shape 2 := .forallE (.sort true) [(.bot, .bot), (.sort true, .sort true)]
def p_lo : Shape 2 := .lam [(.bot, .bot), (.sort true, .sort true)]
def p_hi : Shape 2 := .lam [(.bot, .sort true)]
example : p_lo ≤ p_hi := by decide
example : Shape.hasType p_lo a_ex = true := by decide
example : Shape.hasType p_hi a_ex = false := by decide
example : Shape.WF a_ex := by simp [a_ex, Shape.WF, ShapeFun.WF, Shape.bot, Shape.sort] <;> decide
example : Shape.WF p_lo := by
  simp [p_lo, Shape.WF, ShapeFun.WF, ShapeFun.NonZero, Shape.bot, Shape.sort] <;> decide
example : Shape.WF p_hi := by
  simp [p_hi, Shape.WF, ShapeFun.WF, ShapeFun.NonZero, Shape.bot, Shape.sort] <;> decide

/-! ## §3  C4 (lift ⇐): type side.  A WF level-2 type shape (valid for `(α : Type) → α → α`
by the usual reading) that is below NO lift; `TyDefEq` is only downward closed in the type
(`mono_r_2_ty`), so `TyDefEq … a_bad` cannot be reached from any lifted level-1 fact. -/
def a_bad : Shape 2 :=
  .forallE (.sort true) [(.bot, .bot), (.sort true, .forallE (.sort true) [(.bot, .sort true)])]
example : Shape.WF a_bad := by simp [a_bad, Shape.WF, ShapeFun.WF, Shape.bot, Shape.sort] <;> decide
example : (a_bad.plift (m := 1)).2 = none := by decide
omit [Params] in
theorem a_bad_below_no_lift (t : Shape 1) : ¬ a_bad ≤ t.lift 2 := fun h => by
  obtain ⟨z, hz, -⟩ := (Shape.plift_le (Nat.le_succ 1)).2 h
  rw [show (a_bad.plift (m := 1)).2 = none by decide] at hz; cases hz

/-- The report's own example (`forallE sort [(sort, forallE sort [(bot,sort)])]`, no `(bot,_)`
point): is it `Shape.WF`?  (Checked below: it is.) -/
def a_rep : Shape 2 := .forallE (.sort true) [(.sort true, .forallE (.sort true) [(.bot, .sort true)])]
example : (a_rep.plift (m := 1)).2 = none := by decide

/-! ## §4  C4, element side: every `q ≤ p.lift` has an upper level-n approximation.
So "a level-(n+1) shape below `lift lᵢ` need not be a lift" is not by itself the obstruction:
`q.plift.2 = some z`, `z ≤ p`, and `q ≤ z.lift`.  The obstruction is the TYPE side (§3). -/
omit [Params] in
theorem below_lift_has_upper {s : Shape (n+1)} {t : Shape n} (h : s ≤ t.lift (n+1)) :
    ∃ z, s.plift.2 = some z ∧ z ≤ t ∧ s ≤ z.lift (n+1) := by
  obtain ⟨z, hz, hzt⟩ := (Shape.plift_le (Nat.le_succ n)).2 h
  exact ⟨z, hz, hzt, (Shape.plift_le (Nat.le_succ n)).1 ⟨z, hz, Shape.LE.rfl⟩⟩

/-- The earlier (dead) refuter run asserted `q_ex ≤ lift p`; it is false: `q_ex` has no upper
level-1 approximation, so it is below no lift at all. -/
def q_ex : Shape 2 := .lam [(.bot, .bot), (.sort true, .lam [(.bot, .sort true)])]
example : (q_ex.plift (m := 1)).2 = none := by decide
omit [Params] in
theorem q_ex_below_no_lift (t : Shape 1) : ¬ q_ex ≤ t.lift 2 := fun h => by
  obtain ⟨z, hz, -⟩ := (Shape.plift_le (Nat.le_succ 1)).2 h
  rw [show (q_ex.plift (m := 1)).2 = none by decide] at hz; cases hz

/-! ## §5  A4 support: `HasType` IS upward closed in the type position (given the bigger one
is a type), so A's `SpineTyped` is upward closed in the code; `join'` is same-type only. -/
#check @WShape.HasType.mono_r   -- a ≤ a' → a' : sort r → m : a → m : a'
#check @WShape.HasType.join'    -- m₁ ⊔ m₂ = m → m₁ : a → m₂ : a → m : a

/-! ## §6  The spine WHNF lemmas the report re-proved already exist at HEAD. -/
#check @WHNF.ctorSpine
#check @WHNF.indTySpine
#check @WHRedS.ctorSpine_determ
#print axioms WHNF.ctorSpine
#print axioms WHRedS.ctorSpine_determ

end Lean4Lean.SExpr
