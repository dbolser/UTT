# Unique typing: status

Goal: Lean4Lean Conjecture 2.7 (Carneiro, arXiv 2403.14064). If `Γ ⊢ e : α` and
`Γ ⊢ e : β` then `Γ ⊢ α ≡ β : U`. Open as of Oct 2026.

## The route (Carneiro, May–June 2026, `Lean4Lean/Experimental/`)

1. Work over `SExpr` (universe levels quotiented semantically) and add one rule,
   `trans'`: transitivity where the middle term may live at a different sort.
2. A finitary domain model plus a logical relation (`ShapeLogRel*.lean`, after
   arXiv 2607.13662) gives Pi- and sort-injectivity for the `trans'` system.
3. With injectivity, unique typing for the `trans'` system is a plain induction
   (`UniqueTyping.lean`, `HasTypeS.uniq`). That gives `uniq_sort`, which shows
   `trans'` is admissible: `IsDefEq ↔ IsDefEq'` where `IsDefEq'` has Lean's rules only.
4. Corollary `IsDefEq'.uniq` (end of `UniqueTyping.lean`) is the theorem for `SExpr`.

## What still stands between us and a sorry-free theorem

Run `lake env lean scripts/TraceSorry.lean`. Today it reports, for `IsDefEq'.uniq`:

| gap | file | kind |
|---|---|---|
| `IsDefEq.strong` | SExpr.lean | sorry; port of `Theory/Typing/Strong.lean` to SExpr. **False as stated**: needs a well-formed-context hypothesis (proof in scratch, being integrated) |
| `IsDefEq.subst` | SExpr.lean | sorry; follows from `strong` (same hypothesis) |
| `IsDefEq.defeqDF_l'` | SExpr.lean | sorry; proven in scratch as stated |
| `LR.adequacy`, `const` case | ShapeLogRelAdequacy.lean | **the real gap**: the logical relation records nothing about terms at inductive types, so rewrite rules cannot fire inside it, and the rule's right-hand side has no induction hypothesis |

No custom axioms remain: `Params.extra_pat` and `Params.ctor_ty` are now
theorems derived from VExpr-level `Params` fields (`extra_patV`, `ctor_tyV`),
and typing of environment constants in `SExpr` (`Params.const_wf`,
`Params.defeq_wf`) is derived from `henv` through the translation.

Bridge: `SExpr.IsDefEq.mkS` translates `VEnv.IsDefEq` into `SExpr.IsDefEq`
(port of closed upstream PR #37, with the `mkInst` fix). VExpr-level sort
injectivity and sort/Pi disjointness are reflected back (`sort_invS`,
`sort_forallE_invS`); Pi injectivity reflects only to an SExpr statement so far.

## Done on this branch

- `IsDefEqStrong.defeq` proven.
- `Ctx.SubstEq` redesigned (weakening constructor); `lift`, `lookup` proven.
  The old `lift` statement was unprovable.
- `IsDefEq'.uniq` stated and derived.
- `WHRed.determ` proven (pattern determinism; only `pat_simple`/`pat_uniq` needed).
- Bridge `IsDefEq.mkS` and VExpr corollaries (branch `bridge`, merged).
- Axiom `extra_pat` and sorry `ctor_ty` replaced by `Params` fields + theorems (branch `params`, merged).
