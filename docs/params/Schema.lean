import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! The rule-format mismatch (design A, risk 4), made precise. `VDefEq` rules written with
`vdefeq(x y => lhs ≡ rhs)` are λ-closed schemas: Theory/Meta.lean:97-98 wraps both sides in
`fun $args* =>`; Theory/Quot.lean:11 (`quotDefEq`) does exactly that. `Pattern.Matches`
(Theory/Typing/Pattern.lean) has only `const`/`var`/`app` cases, and `Params.extra_patV`
demands a pattern match of every rule instance. Hence no `Params` instance can contain a
λ-headed rule. Delta rules (`VDefVal.toDefEq`, `lhs = const c _`) are unaffected.
(`Theory.Quot` itself cannot be imported in the frozen snapshot: `Batteries.Lean.Expr` is not
built there, so the instance at `quotDefEq` is by reading, the lemma is generic.) Sorry-free. -/
namespace Lean4Lean

theorem Pattern.Matches.not_lam {p : Pattern} {A b : VExpr} {m1 m2} :
    ¬ p.Matches (.lam A b) m1 m2 := nofun

/-- No `Params` environment contains a rule whose left-hand side is a lambda. -/
theorem Params.no_lam_rule [Params] {df : VDefEq} {A b : VExpr}
    (hl : df.lhs = .lam A b) (h : Params.env.defeqs df) : False := by
  obtain ⟨p, r, m1, m2, _, hm, _⟩ := Params.extra_patV (Γ := [])
    (ls := List.replicate df.uvars .zero) h
    (fun l hl => List.eq_of_mem_replicate hl ▸ trivial) (List.length_replicate ..)
  rw [hl] at hm
  exact Pattern.Matches.not_lam (by simpa only [VExpr.instL] using hm)

end Lean4Lean
