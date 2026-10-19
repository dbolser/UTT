import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Plan amender, round 3: the E5 interface. snap6's `Params` still has the old `extra_patV`
(SExpr.lean:59-62), so D5's λ-`extra_patV` is an explicit hypothesis `ExtraPatVLam`, and the
`extra` case of `LE_Interp.strongSoundS` (ShapeLogRel.lean:5229-5260) is a standalone lemma over a
λ-rule. `strongSoundS` (5055) is outside E1's copy (5272-6117); `StrongSoundEq` (4633) does not
mention `LR`, so the lemma is stated over the repo's definitions. Typechecked AS A STATEMENT at
/tmp/utt-snap6. Deliberate sorry: the theorem body (marked). -/
namespace Lean4Lean.SExpr
variable [Params]

/-- D5's λ-`extra_patV` (PLAN §1 D5), verbatim, as a hypothesis. -/
def ExtraPatVLam : Prop :=
  ∀ {df : VDefEq} {ls : List VLevel} {Γ : List VExpr},
    Params.env.defeqs df → (∀ l ∈ ls, l.WF Params.univs) → ls.length = df.uvars →
    ∃ (Δ : List VExpr) (L R T : VExpr),
      df.lhs.instL ls = Δ.foldr .lam L ∧ df.rhs.instL ls = Δ.foldr .lam R ∧
      df.type.instL ls = Δ.foldr .forallE T ∧
      OnCtx Δ.reverse (Params.env.IsType Params.univs) ∧
      Params.env.IsDefEq Params.univs Δ.reverse L R T ∧
      ∃ p r m1 m2, Params.Pat p r ∧ p.Matches L m1 m2 ∧
        r.2.OK (Params.env.IsDefEqU Params.univs (Δ.reverse ++ Γ)) m1 m2 ∧ R = r.1.apply m1 m2

/-- The `extra` case of `LE_Interp.strongSoundS` for a λ-wrapped rule (E5). `ih1`/`ih2` are the
case's two IHs (`IsDefEqStrong.extra`'s typing premises, SExpr.lean:1075). -/
theorem strongSoundS_extra_lam (hlam : ExtraPatVLam) {df : VDefEq} {ls : List SLevel}
    {Γ : List SExpr} (h1 : Params.env.defeqs df) (h2 : ls.length = df.uvars)
    (ih1 : StrongSoundEq Γ (.mkInst ls df.lhs) (.mkInst ls df.lhs) (.mkInst ls df.type))
    (ih2 : StrongSoundEq Γ (.mkInst ls df.rhs) (.mkInst ls df.rhs) (.mkInst ls df.type)) :
    StrongSoundEq Γ (.mkInst ls df.lhs) (.mkInst ls df.rhs) (.mkInst ls df.type) := by
  sorry -- SORRY(statement only)

end Lean4Lean.SExpr
#check @Lean4Lean.SExpr.strongSoundS_extra_lam
