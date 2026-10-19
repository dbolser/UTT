import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Audit (circularity/measure, round 2): the spine lemma's `lam` case when the remaining type `B`
is NOT syntactically a Π (e.g. `def f : MyFun := fun x => x` with `MyFun := Nat → Nat`).
`hT : mkInst ls ci.type = Ts.foldr .forallE B` cannot be extended, so the case must be closed
by showing every `Const` derivation at `rargs` longer than the syntactic telescope is `⊥`.
This file proves that lemma from three arity bounds (ctor / indTy / pattern arity ≤ N),
i.e. from `ctor_syn`, `indTy_closed` (stage 1a) and `pat_gen` (head type has a syntactic
telescope at least the pattern arity). Sorry-free. -/
namespace Lean4Lean.SExpr
variable [Params]

theorem Const.beyond {c : Name} {ls : List SLevel} {R : TShape → SExpr → Prop} {n N : Nat}
    (hctor : ∀ k, Params.classify c = some (.ctor k) → k ≤ N)
    (hind : ∀ k, Params.classify c = some (.indTy k) → k ≤ N)
    (hpat : ∀ {p : Pattern} {r : p.RHS × p.Check} {rargs' : List (WShape n)} {m'},
      Params.Pat p r → LE_Interp.Matches p c rargs' m' → rargs'.length ≤ N)
    {rargs : List (WShape n)} {m : TShape}
    (H : LE_Interp.Const c ls R rargs m) (hlen : N < rargs.length) : m ≤ TShape.bot := by
  induction H with
  | bot => exact TShape.bot_le'
  | @lam f rargs m _ h2 ih =>
    have hf : ¬ f.NonZero := by
      intro hnz
      obtain ⟨⟨x, y⟩, hmem, hy⟩ := WShapeFun.NonZero.iff.1 hnz
      have hy' := ih x y hmem (by simp; omega)
      exact hy (WShape.LE.of_T (hy'.trans TShape.bot_eqv.2))
    have : WShape.lam' f = .bot := by simp [WShape.lam', hf]
    rw [this] at h2; exact h2.trans TShape.bot_eqv.1
  | ctor h1 _ => have := hctor _ h1; omega
  | indTy h1 _ => have := hind _ h1; omega
  | pat h1 h2 _ => have := hpat h1 h2; omega

#print axioms Const.beyond
end Lean4Lean.SExpr
