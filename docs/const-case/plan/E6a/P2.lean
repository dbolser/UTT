import Lean4Lean.Experimental.E6a.FieldLower
/-! Verifier: P2 without the author's side conditions. The pinned statement (text of
RhsLowerStmt.lean:208-226 with gen := Pattern.gen, idx := p.genIdx, rank := RP.rank, written out
here independently) forces EVERY rule of EVERY Params/RankParams pair to have no self occurrence:
hMt, hm, hfit, hvar are discharged here with all-⊥ shapes. -/
namespace Lean4Lean.SExpr
variable [Params]

def VPinned (RP : RankParams) : Prop :=
  ∀ {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name} {ls : List SLevel}
    {R : TShape → SExpr → Prop} (_LIH : LR.LocalIH RP.rank Γ₀ ρ₀ c R)
    {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} {mC : TShape}
    (_hP : Params.Pat p r) (_hMt : LE_Interp.Matches p c rargs m2)
    (_hRHS : LE_Interp.RHS ls m2 R mC r.1)
    (g : PatGen) (_hg : Pattern.gen Params.env RP.rank Params.classify p r.1 = some g)
    {fields : List TShape} {ρ : Valuation} {m : Nat} (_hm : g.ctx.length = fields.length + m)
    (_hfit : (Valuation.lowerCtx fields ρ m).Fits Γ₀ (g.ctx.map (SExpr.mkInst ls) ++ Γ₀))
    (_hvar : ∀ path {n} {y b : WShape n}, y.T ≤ m2 path → y.HasType b →
      LE_Interp (Valuation.lowerCtx fields ρ m) b.T
        (SExpr.mkInst ls ((g.ctx.getD (p.genIdx path) (.sort .zero)).liftN (p.genIdx path + 1))) →
      y.T ≤ Valuation.lowerCtx fields ρ m (p.genIdx path)),
    ∃ selfs : List TShape, selfs.length = g.self.length ∧
      (∀ j s, selfs[j]? = some s → ∃ (me : TShape) (c' : Name) (ls' : List SLevel) (ci' : VConstant),
        R me (.const c' ls') ∧ RP.rank c' = RP.rank c ∧ Params.env.constants c' = some ci' ∧
        ls'.length = ci'.uvars ∧ me ≤ s ∧
        SExpr.mkInst ls (g.self.getD j (.sort .zero)) = SExpr.mkInst ls' ci'.type ∧
        (∃ (k : Nat) (x b : WShape k), s = x.T ∧ x.HasType b ∧
          LE_Interp ρ₀ b.T (SExpr.mkInst ls' ci'.type)) ∧
        LR.ConstGoal Γ₀ ρ₀ s c' ls' ci') ∧
      ∀ {n'} {y' a' : WShape n'}, y'.T ≤ mC → y'.HasType a' →
        LE_Interp (Valuation.lower selfs fields ρ m) a'.T
          (SExpr.mkInst ls (g.type.liftN g.self.length)) →
        LE_Interp (Valuation.lower selfs fields ρ m) y'.T (SExpr.mkInst ls g.rhsAbs)

/-- the pinned lemma (as the author states it) has exactly this type -/
example (RP : RankParams) : VPinned RP := @LR.rhs_lower _ RP

theorem V.matches_varN_bot (c : Name) {n : Nat} : ∀ k : Nat,
    ∃ mf : (Pattern.varN (.const c) k).Path → TShape,
      LE_Interp.Matches (n := n) (.varN (.const c) k) c (List.replicate k WShape.bot) mf ∧
      ∀ x, mf x ≤ TShape.bot
  | 0 => ⟨nofun, .const, nofun⟩
  | k+1 => by
    obtain ⟨mf, h, hb⟩ := V.matches_varN_bot c (n := n) k
    refine ⟨_, .var (a := WShape.bot) h, ?_⟩
    intro x; cases x with
    | none => exact TShape.bot_eqv.1
    | some x => exact hb x

theorem V.nil_push_bot : Valuation.nil.push TShape.bot = Valuation.nil := by
  funext i; cases i <;> rfl

theorem V.fits_nil (E : VEnv) (hE : E ≤ Params.env) (ls : List SLevel) : ∀ L : List VExpr,
    (∀ (Δ : List VExpr) A Γ, L = Δ ++ A :: Γ →
      ∃ u, IsDefEqStrong E (Γ.map (mkInst ls)) (mkInst ls A) (mkInst ls A) (.sort u)) →
    Valuation.Fits [] (L.map (mkInst ls)) Valuation.nil
  | [], _ => .nil
  | A :: L, h => by
    have W := V.fits_nil E hE ls L fun Δ A' Γ e => h (A :: Δ) A' Γ (by rw [e]; rfl)
    obtain ⟨u, H⟩ := h [] A L rfl
    rw [← V.nil_push_bot]
    exact .cons W (fun h => InterpTyped.hsort (fun h => (LE_Interp.soundSE hE H W).2 h) h) .bot
      (WShape.HasType.T_iff.2 <| .bot' <| .bot' .sort)

theorem V.lowerCtx_bot (k m : Nat) :
    Valuation.lowerCtx (List.replicate k TShape.bot) Valuation.nil m = Valuation.nil := by
  unfold Valuation.lowerCtx
  have h2 : ∀ m, (List.range m).foldr (fun i (ρ' : Valuation) => ρ'.push (Valuation.nil (i + 1)))
      Valuation.nil = Valuation.nil := by
    intro m; induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.foldr_append]; simp only [List.foldr_cons, List.foldr_nil]
      have : Valuation.nil.push (Valuation.nil (m + 1)) = Valuation.nil := V.nil_push_bot
      rw [this, ih]
  rw [h2]
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.foldr_cons, ih]; exact V.nil_push_bot

/-- From the pinned statement at `R := ∅`, `hRHS := RHS.bot`. -/
theorem V.no_self_of (RP : RankParams) (H : VPinned RP) {p : Pattern} {r : p.RHS × p.Check}
    (hP : Params.Pat p r) {g : PatGen} (hg : Pattern.gen Params.env RP.rank Params.classify p r.1 = some g)
    {c : Name} {n : Nat} {rargs : List (WShape n)} {m2 : p.Path → TShape}
    (hMt : LE_Interp.Matches p c rargs m2) (hb : ∀ x, m2 x ≤ TShape.bot)
    {fields : List TShape} {m : Nat} (hm : g.ctx.length = fields.length + m)
    (hfit : (Valuation.lowerCtx fields Valuation.nil m).Fits [] (g.ctx.map (SExpr.mkInst []) ++ [])) :
    g.self = [] := by
  obtain ⟨selfs, hl, hs, -⟩ := H (Γ₀ := []) (ρ₀ := .nil) (ls := []) (R := fun _ _ => False)
    (fun _ _ h => h.elim) hP hMt
    (LE_Interp.RHS.bot : LE_Interp.RHS [] m2 (fun _ _ => False) (WShape.bot (n := 0)).T r.1)
    g hg hm hfit (fun path _ _ _ hy _ _ => (hy.trans (hb path)).trans TShape.bot_le)
  cases hgs : g.self with
  | nil => rfl
  | cons A As =>
    have : 0 < selfs.length := by rw [hl, hgs]; exact Nat.succ_pos _
    obtain ⟨_, _, _, _, h, -⟩ := hs 0 _ (List.getElem?_eq_getElem this)
    exact h.elim

/-- P2, all side conditions discharged: the pinned statement implies that no rule has a self
occurrence (for every `Params` with a `RankParams`). -/
theorem V.pinned_forces_no_self (RP : RankParams) (H : VPinned RP) {p : Pattern}
    {r : p.RHS × p.Check} (hP : Params.Pat p r) {g : PatGen}
    (hg : Pattern.gen Params.env RP.rank Params.classify p r.1 = some g) : g.self = [] := by
  obtain ⟨ci, hci⟩ := Pattern.gen_head_const hg
  have hfitL : Valuation.Fits [] (g.ctx.map (mkInst [])) Valuation.nil :=
    V.fits_nil _ (Params.env.below_le ..) [] g.ctx fun Δ A Γ e =>
      (EnvStrongR.of_params RP).pat_ctx [] hP hg hci (Δ := g.self ++ Δ) (by rw [e, List.append_assoc])
  rcases Pattern.gen_shape hg with ⟨c, rfl⟩ | ⟨rec, m', c', n', rfl⟩
  · obtain ⟨_, -, hctx, -⟩ := Pattern.gen_delta hg
    refine V.no_self_of RP H hP hg (n := 0) .const nofun (fields := []) (m := 0) (by simp [hctx]) ?_
    rw [List.append_nil]; exact hfitL
  · obtain ⟨mf, hf, hbf⟩ := V.matches_varN_bot rec (n := 1) m'
    obtain ⟨ma, ha, hba⟩ := V.matches_varN_bot c' (n := 0) n'
    refine V.no_self_of RP H hP hg (.app hf ha) (fun x => by cases x <;> simp [hbf, hba])
      (fields := List.replicate n' TShape.bot) (m := m')
      (by rw [Pattern.gen_ctx_iota hg, List.length_replicate]) ?_
    rw [V.lowerCtx_bot, List.append_nil]; exact hfitL

end Lean4Lean.SExpr

#print axioms Lean4Lean.SExpr.V.pinned_forces_no_self
#check @Lean4Lean.SExpr.V.pinned_forces_no_self
