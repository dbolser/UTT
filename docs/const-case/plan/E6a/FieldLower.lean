import Lean4Lean.Experimental.E3.Measure7
/-! E6a (docs/const-case/PLAN.md §2 row E6a, §1 D4 "RHS step" steps 1-2): the field-entry
typing for the pattern leaf, option (a). Built over E3's `Measure7.lean` (`Pattern.gen`,
`Pattern.pathIdx`, `RankParams`, `EnvStrongR`, `LR.LocalIH`, `LR.ConstGoal`); redefines nothing.

* `Valuation.lowerCtx`, `Valuation.lower`: verbatim from `historical/RhsLowerStmt.lean:195-201`.
* `LR.rhs_lower`: the lowering lemma, sorry-free. It is NOT the pinned statement
  (`RhsLowerStmt.lean:208-234`), which is false (see the last section: `T.PinnedRhsLower`,
  `T.pinned_false_const`, `T.pinned_false_iota`). Differences, each needed:
  - `gen := Pattern.gen`, `idx := Pattern.pathIdx p`, `rank := RP.rank` with `(RP : RankParams)`
    (the intended instantiation; `RP.pat_typed`/`pat_defeq` give the RHS typing, without which
    an ill-typed RHS breaks the main conjunct);
  - new `hR : ∀ m e, R m e → LE_Interp ρ₀ m e` (`LE_Interp.const`'s last premise; without it the
    non-self fixed leaves are unconstrained: `T.pinned_false_const`);
  - new `hhead`: each path is a function-position-safe variable (`m2 path ≤` its entry; the
    recursor arguments, from the spine lemma's `hρ`) or has an inductive-type constant as its
    context type (the constructor fields, from `gen_head_ctor` + `ctor_fields_closed`);
  - self clause: the `R`-witness `R me (.const c' ls') ∧ me ≤ s` is required only when `s ≠ ⊥`
    (an occurrence under an `RHS.bot` node has none: `T.pinned_false_iota`); in exchange the
    clause names the occurrence (`selfLeaves[j] = .const c' us`, `ls' = us.map (instV ls)`) and
    keeps `us.length = ci'.uvars` unconditionally (from `pat_defeq`).
  `hm` is kept for fidelity and unused.

The proof of the main conjunct is D4's argument [A]: by induction on `LE_Interp.RHS`, with the
strong typing of `rhsAbs` (from `pat_typed`) inverted along the term by `StrongSoundCore`.
Every function position is interpreted at `ρ_low` (fixed leaves by `hR`, self leaves by the
`LocalIH` bound, recursor arguments by `hhead`), so it has a typed upper bound by soundness
(`SoundTy`), whose `HasDom` collapses an untyped argument shape to a typed one below it
(`T.app_collapse`); arguments then only need the downward claim, which `hvar` gives at variables.
A constructor-field variable never sits in function position (`T.const_indTy_not_forallE`). -/
namespace Lean4Lean.SExpr
variable [Params]

/-! ## The lowered valuation (`RhsLowerStmt.lean:195-201`, verbatim) -/

/-- ρ_low's pattern-context part (PLAN D4 step 1), over `.nil` (the valuation of `SubstWF.id`,
base context `Γ₀`), innermost first: the lowered field entries `fields`, then the recursor
arguments `ρ 1 … ρ m` (`ρ 0` is the major). `fields[i]` is `l_i.T` when the ctor shape's field
`l_i` is `⊥` or a ctor shape, else `⊥`; `⊥` when the field type is Prop-valued. -/
def Valuation.lowerCtx (fields : List TShape) (ρ : Valuation) (m : Nat) : Valuation :=
  fields.foldr (fun x ρ' => ρ'.push x) <|
    (List.range m).foldr (fun i ρ' => ρ'.push (ρ (i + 1))) .nil

/-- ρ_low (PLAN D4 step 1): the self entries (index `j` = `j`-th self) on top of `lowerCtx`. -/
def Valuation.lower (selfs fields : List TShape) (ρ : Valuation) (m : Nat) : Valuation :=
  selfs.foldr (fun x ρ' => ρ'.push x) (Valuation.lowerCtx fields ρ m)

/-! ## Valuation, lifting and lookup plumbing -/
/-- Pushing a list shifts the old valuation by its length. -/
theorem T.foldr_push_add (ρ : Valuation) : ∀ (xs : List TShape) (i : Nat),
    (xs.foldr (fun x ρ' => ρ'.push x) ρ) (xs.length + i) = ρ i
  | [], i => by simp
  | x :: xs, i => by
    rw [List.length_cons, Nat.add_right_comm]
    exact T.foldr_push_add ρ xs i

/-- The pushed entries come first, `xs[0]` at index `0`. -/
theorem T.foldr_push_lt (ρ : Valuation) : ∀ (xs : List TShape) (i : Nat) (s : TShape),
    xs[i]? = some s → (xs.foldr (fun x ρ' => ρ'.push x) ρ) i = s
  | [], _, _, h => by simp at h
  | x :: xs, 0, s, h => by simpa [Valuation.push] using h
  | x :: xs, i+1, s, h => T.foldr_push_lt ρ xs i s (by simpa using h)

theorem T.liftK_add (M : SExpr) (a : Nat) : ∀ b, liftK M (a + b) = liftK (liftK M a) b
  | 0 => rfl
  | b+1 => congrArg SExpr.lift (T.liftK_add M a b)

/-- `mkInst` commutes with `VExpr.liftN k` (as `liftK`). -/
theorem T.mkInst_liftN (ls : List SLevel) (Y : VExpr) : ∀ k, mkInst ls (Y.liftN k) = liftK (mkInst ls Y) k
  | 0 => by simp [liftK]
  | k+1 => by
    rw [VExpr.liftN_succ, VExpr.lift_eq_lift', mkInst_lift', T.mkInst_liftN ls Y k]; rfl

theorem T.liftK_const (c : Name) (ls : List SLevel) : ∀ k, liftK (.const c ls) k = .const c ls
  | 0 => rfl
  | k+1 => by rw [liftK, T.liftK_const c ls k]; rfl

/-- Weakening of `LE_Interp` over a pushed list (`LE_Interp.weak_iff`, iterated). -/
theorem T.LE_Interp_foldr_push_liftK {ρ : Valuation} {m : TShape} {M : SExpr} :
    ∀ (xs : List TShape), LE_Interp (xs.foldr (fun x ρ' => ρ'.push x) ρ) m (liftK M xs.length) ↔
      LE_Interp ρ m M
  | [] => Iff.rfl
  | _ :: xs => LE_Interp.weak_iff.trans (T.LE_Interp_foldr_push_liftK xs)

/-- A lookup is the `i`-th entry lifted `i+1` times. -/
theorem T.lookup_eq : ∀ {Γ : List SExpr} {i : Nat} {A : SExpr}, Lookup Γ i A →
    ∃ B, Γ[i]? = some B ∧ A = liftK B (i+1)
  | _ :: _, 0, _, .zero => ⟨_, rfl, rfl⟩
  | _ :: _, _+1, _, .succ h => by
    obtain ⟨B, h1, rfl⟩ := T.lookup_eq h
    exact ⟨B, by simpa using h1, rfl⟩

/-! ## Shape lemmas -/

/-- The shape `Π (_ : ⊥), ⊥` interprets every Π-type. -/
theorem T.forallE_bot_interp {ρ : Valuation} {A B : SExpr} :
    LE_Interp ρ (WShape.forallE (n := 0) .bot .bot).T (.forallE A B) :=
  .forallE' .bot .bot (WShape.HasDom.bot (.bot' .sort)) fun x _ => by
    rw [WShapeFun.bot_app]; exact .bot

theorem T.forallE_not_le_indTy {a : WShape n} {f : WShapeFun n} :
    ¬(.forallE a f : WShape (n+1)).T ≤ (WShape.indTy : WShape (n'+1)).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_forallE le₁, WShape.lift_indTy, WShape.le_indTy]
  rintro (h | h) <;> cases congrArg (·.1) h

theorem T.forallE_not_le_bot {a : WShape n} {f : WShapeFun n} :
    ¬(.forallE a f : WShape (n+1)).T ≤ TShape.bot := by
  rw [TShape.le_bot]; intro h; cases congrArg (·.1) h

/-- An inductive-type constant is never interpreted by a Π-shape. -/
theorem T.const_indTy_not_forallE {ρ : Valuation} {I : Name} {ls : List SLevel} {k : Nat}
    (hI : Params.classify I = some (.indTy k)) :
    ¬LE_Interp ρ (WShape.forallE (n := 0) .bot .bot).T (.const I ls) := by
  intro h
  generalize eM : (WShape.forallE (n := 0) .bot .bot).T = mT at h
  generalize eC : SExpr.const I ls = M at h
  cases h with
  | bot =>
    injection eM with e1 e2
    subst e1
    cases congrArg (·.1) (eq_of_heq e2)
  | bvar | sort | app | lam | forallE => cases eC
  | const h1 h2 h3 h4 h5 h6 h7 =>
    injection eC with e1 e2; subst e1 e2; subst eM
    cases h6 with
      | bot => exact T.forallE_not_le_bot (h3.trans TShape.bot_eqv.1)
      | lam _ hle => exact TShape.forallE_not_le_lam' (h3.trans hle)
      | ctor hc => cases hI.symm.trans hc
      | indTy _ hle => exact T.forallE_not_le_indTy (h3.trans hle)
      | pat hP hM => cases hI.symm.trans (pat_arity hP hM.arity)

/-- The function-position collapse ([A] of PLAN D4 step 2): a typed upper bound of the
function shape has `HasDom`, so the argument shape may be replaced by a typed one below it. -/
theorem T.app_collapse {ρ : Valuation} {F X A B : SExpr} {k : Nat} {f : WShape (k+1)}
    {a : WShape k} {ms : TShape}
    (H1 : InterpTyped ρ f.T F (.forallE A B))
    (hX : ∀ {n} {y b : WShape n}, y.T ≤ a.T → y.HasType b → LE_Interp ρ b.T A →
      LE_Interp ρ y.T X)
    (hms : ms ≤ (f.app a).T) : LE_Interp ρ ms (F.app X) := by
  by_cases hm : ms ≤ .bot
  · exact TShape.le_bot'.1 hm ▸ .bot
  obtain ⟨U, u, le_f, hU, hu, hUu⟩ := H1
  have hf : ¬ U ≤ .bot := fun h => by
    rw [show f = .bot from TShape.le_bot.1 (le_f.trans h), WShape.bot_app] at hms
    exact hm (hms.trans TShape.bot_le')
  have hs : ¬ u ≤ .bot := fun h => hf (hUu.bot_r' h)
  cases hu with
  | bot => exact absurd TShape.bot_le' hs
  | forallE b1 _ _ _ b5 =>
    cases b5.le_forall with
    | bot b5 => exact absurd b5 hs
    | @forallE m₀ _ _ b'' _ b5 _ =>
      obtain c1 | ⟨n₂, g, rfl, c1⟩ := hUu.ty_forallE_inv
      · exact absurd (c1 ▸ .rfl) hf
      have hk1 : k ≤ max k (max n₂ m₀) := Nat.le_max_left ..
      have hk2 : n₂ ≤ max k (max n₂ m₀) := Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)
      have hk3 : m₀ ≤ max k (max n₂ m₀) := Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)
      have c1 := (TShape.HasTypeLam.def hk2 hk3).1 c1
      obtain ⟨x', e1, e2, e3⟩ := WShape.HasDom.iff.1 c1.2.1 (a.lift _)
      have hb : LE_Interp ρ (b''.lift (max k (max n₂ m₀))).T A := (b1.mono b5).lift hk3
      have hx' : LE_Interp ρ x'.T X := hX (e1.T.trans (TShape.lift_eqv hk1).1) e2 hb
      have hg : LE_Interp ρ (WShape.lam' (g.lift (max k (max n₂ m₀)))).T F := by
        have := hU.lift (Nat.succ_le_succ hk2)
        rwa [WShape.lift_lam' hk2] at this
      refine .mono ?_ (hg.app' hx')
      rw [WShape.lam'_app]
      refine hms.trans ((TShape.app_mono (f' := WShape.lam' (g.lift (max k (max n₂ m₀))))
        (a' := a.lift _) ?_ (TShape.lift_eqv hk1).2).trans ?_)
      · have := (TShape.lift_eqv (a := (WShape.lam' g).T) (Nat.succ_le_succ hk2)).2
        rw [WShape.lift_lam' hk2] at this
        exact le_f.trans this
      · rw [WShape.lam'_app]; exact e3.T

/-! ## `Pattern.gen` plumbing -/

/-- The head of a matched pattern is the matched constant. -/
theorem T.matches_head {p : Pattern} {c : Name} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} (H : LE_Interp.Matches p c rargs m2) : p.head = c := by
  induction H with
  | const => rfl
  | var _ ih => exact ih
  | app _ _ ih => exact ih

omit [Params] in
theorem T.pathIdx_lt : ∀ (p : Pattern) (x : p.Path), p.pathIdx x < p.nvars
  | .const _, x => x.elim
  | .app f a, .inl x => by
    have := T.pathIdx_lt f x; simp only [Pattern.pathIdx_inl, Pattern.nvars]; omega
  | .app f a, .inr x => by
    have := T.pathIdx_lt a x; simp only [Pattern.pathIdx_inr, Pattern.nvars]; omega
  | .var f, none => by simp [Pattern.nvars]
  | .var f, some x => by
    have := T.pathIdx_lt f x; simp only [Pattern.pathIdx_some, Pattern.nvars]; omega

omit [Params] in
/-- `Pattern.gen` succeeds only at a head with a declaration, and its context has one entry
per path. -/
theorem T.gen_head_ctx {env : VEnv} {rank : Name → Nat} {classify : Name → Option Classification}
    {p : Pattern} {r : p.RHS} {g : PatGen} (hg : Pattern.gen env rank classify p r = some g) :
    (∃ ci, env.constants p.head = some ci) ∧ g.ctx.length = p.nvars := by
  obtain ⟨-, h2, -⟩ := Pattern.gen_eq_some hg
  match p, h2 with
  | .const c, h2 =>
    simp only [Pattern.genCore, Option.map_eq_some_iff, Prod.mk.injEq] at h2
    obtain ⟨ci, h1, h2, -⟩ := h2
    exact ⟨⟨ci, h1⟩, by rw [← h2]; rfl⟩
  | .app f a, h2 =>
    simp only [Pattern.genCore] at h2
    split at h2
    · next rec m c' n hf ha =>
      cases Pattern.eq_varN_of_asVarN hf; cases Pattern.eq_varN_of_asVarN ha
      obtain ⟨ci, ci', Hs, I, us, Bmaj, Fs, R', h1, -, -, t4, t5, h6, -, -⟩ :=
        Pattern.genIota_eq_some h2
      obtain ⟨l4, -⟩ := VExpr.piTelescope_eq_some t4
      obtain ⟨l5, -⟩ := VExpr.piTelescope_eq_some t5
      refine ⟨⟨ci, ?_⟩, ?_⟩
      · show env.constants (Pattern.varN (.const rec) m).head = some ci
        rw [Pattern.head_varN]; exact h1
      · rw [h6, Pattern.nvars, Pattern.nvars_varN, Pattern.nvars_varN]
        simp [l4, l5, Pattern.nvars]; omega
    · cases h2
  | .var _, h2 => cases h2

/-! ## The lowering lemma -/

/-- Pushing typed entries for closed, well-typed types keeps `Fits` (`Valuation.Fits.cons`). -/
theorem T.fits_foldr_push {Γ₀ Δ : List SExpr} {ρ : Valuation} (W : Valuation.Fits Γ₀ Δ ρ) :
    ∀ (As : List SExpr) (xs : List TShape), As.length = xs.length →
    (∀ j A x, As[j]? = some A → xs[j]? = some x →
      (∃ u, StrongSound (As.drop (j+1) ++ Δ) A (.sort u)) ∧
      ∃ a, (∀ ρ', LE_Interp ρ' a A) ∧ x.HasType a) →
    Valuation.Fits Γ₀ (As ++ Δ) (xs.foldr (fun x ρ' => ρ'.push x) ρ)
  | [], [], _, _ => W
  | A :: As, x :: xs, hl, H => by
    have IH := T.fits_foldr_push W As xs (by simpa using hl) fun j A' x' h1 h2 =>
      H (j+1) A' x' (by simpa using h1) (by simpa using h2)
    obtain ⟨⟨u, hA⟩, a, ha, hx⟩ := H 0 A x rfl rfl
    exact .cons IH (InterpTyped.hsort (hA.sound IH)) (ha _) hx

/-- Inversion of an interpretation of a constant (`⊥`, or the `LE_Interp.const` data). -/
theorem T.const_inv {ρ : Valuation} {m : TShape} {c : Name} {ls : List SLevel}
    (H : LE_Interp ρ m (.const c ls)) :
    (∃ k, m = (WShape.bot (n := k)).T) ∨
      ∃ ci, Params.env.constants c = some ci ∧ ls.length = ci.uvars := by
  generalize eC : SExpr.const c ls = M at H
  cases H with
  | bot => exact .inl ⟨_, rfl⟩
  | bvar | sort | app | lam | forallE => cases eC
  | const h1 h2 => injection eC with e1 e2; subst e1 e2; exact .inr ⟨_, h1, h2⟩

/-- What the lowering induction records for the self entry `s` of the leaf occurrence `e`:
`⊥`, or `LocalIH`'s typed upper bound of an `R`-witness. -/
def T.SelfFact (Γ₀ : List SExpr) (ρ₀ : Valuation) (ls : List SLevel) (R : TShape → SExpr → Prop)
    (e : VExpr) (s : TShape) : Prop :=
  (∃ k, s = (WShape.bot (n := k)).T) ∨
  ∃ (c' : Name) (us : List VLevel) (ci' : VConstant) (me : TShape), e = .const c' us ∧
    Params.env.constants c' = some ci' ∧ us.length = ci'.uvars ∧ R me (mkInst ls e) ∧ me ≤ s ∧
    (∃ (k : Nat) (x b : WShape k), s = x.T ∧ x.HasType b ∧
      LE_Interp ρ₀ b.T (mkInst (us.map (SLevel.instV ls)) ci'.type)) ∧
    LR.ConstGoal Γ₀ ρ₀ s c' (us.map (SLevel.instV ls)) ci'

/-- A self entry for an `R`-witnessed leaf, from `hR` and `LR.LocalIH`. -/
theorem T.selfFact_exists {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name} {ls : List SLevel}
    {R : TShape → SExpr → Prop} {rank : Name → Nat} (LIH : LR.LocalIH rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e) {e : VExpr} {c' : Name} {us : List VLevel}
    (he : e = .const c' us) (hrk : rank c' = rank c) {ms : TShape} (hms : R ms (mkInst ls e)) :
    ∃ s, T.SelfFact Γ₀ ρ₀ ls R e s ∧ ms ≤ s := by
  subst he
  obtain ⟨k, rfl⟩ | ⟨ci', h1, h2⟩ := T.const_inv (hR _ _ hms)
  · exact ⟨_, .inl ⟨k, rfl⟩, .rfl⟩
  · rcases LIH _ _ hms c' _ ci' rfl hrk h1 h2 with ⟨k, rfl⟩ | ⟨n, m', a', le, ty, ha, H⟩
    · exact ⟨_, .inl ⟨k, rfl⟩, .rfl⟩
    · exact ⟨m'.T, .inr ⟨c', us, ci', _, rfl, h1, by simpa using h2, hms, le,
        ⟨n, m', a', rfl, ty, ha⟩, .inr ⟨n, m', a', .rfl, ty, ha, H⟩⟩, le⟩

/-- The lowering induction (on `LE_Interp.RHS`). For the subterm `t = mkInst ls (r.toVExpr sel K j)`
of the abstracted RHS, it produces the subtree's self entries `sl` and, at every fitting `ρ'`
holding them at `j, j+1, …`: the downward claim (every typed shape below the RHS shape whose type
interprets `t`'s type is interpreted at `ρ'`), and, unless `r` is a variable not covered by
`hhead`'s first disjunct, the RHS shape itself is interpreted at `ρ'`. -/
theorem T.rhs_lower_core {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name} {ls : List SLevel}
    {R : TShape → SExpr → Prop} {rank : Name → Nat} (LIH : LR.LocalIH rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e) {p : Pattern} {m2 : p.Path → TShape}
    (sel : VExpr → Bool) (hsel : ∀ e, sel e = true → ∃ c' us, e = .const c' us ∧ rank c' = rank c)
    (K : Nat) (Γ : List SExpr) :
    ∀ {ms : TShape} {r : p.RHS}, LE_Interp.RHS ls m2 R ms r →
    ∃ sl : List TShape, sl.length = (r.selfLeaves sel).length ∧
      (∀ (i : Nat) (s : TShape) (e : VExpr), sl[i]? = some s → (r.selfLeaves sel)[i]? = some e →
        T.SelfFact Γ₀ ρ₀ ls R e s) ∧
      ∀ (j : Nat) {Γb : List SExpr} {ρ' : Valuation}, Valuation.Fits Γb Γ ρ' →
        (∀ (i : Nat) (s : TShape), sl[i]? = some s → s ≤ ρ' (j + i)) →
        (∀ path {n} {y b : WShape n} {T'}, Lookup Γ (K + p.pathIdx path) T' → y.T ≤ m2 path →
          y.HasType b → LE_Interp ρ' b.T T' → y.T ≤ ρ' (K + p.pathIdx path)) →
        (∀ path, m2 path ≤ ρ' (K + p.pathIdx path) ∨ ∀ T', Lookup Γ (K + p.pathIdx path) T' →
          ∃ I' ls' k, T' = .const I' ls' ∧ Params.classify I' = some (.indTy k)) →
        ∀ {T}, StrongSound Γ (mkInst ls (r.toVExpr sel K j)) T →
          (∀ {n} {y b : WShape n}, y.T ≤ ms → y.HasType b → LE_Interp ρ' b.T T →
            LE_Interp ρ' y.T (mkInst ls (r.toVExpr sel K j))) ∧
          ((∀ path, r = .var path → m2 path ≤ ρ' (K + p.pathIdx path)) →
            LE_Interp ρ' ms (mkInst ls (r.toVExpr sel K j))) := by
  intro ms r hRHS
  induction hRHS with
  | @bot _ r =>
    refine ⟨List.replicate (r.selfLeaves sel).length (WShape.bot (n := 0)).T, by simp,
      fun i s e h1 _ => ?_, fun j Γb ρ' _ _ _ _ T _ =>
        ⟨fun hy _ _ => .mono hy .bot, fun _ => .bot⟩⟩
    rw [List.getElem?_replicate] at h1; split at h1 <;> cases h1
    exact .inl ⟨0, rfl⟩
  | @const ms e cl hms =>
    by_cases hs : sel e = true
    · obtain ⟨c', us, he, hrk⟩ := hsel e hs
      obtain ⟨s, hsf, hle⟩ := T.selfFact_exists LIH hR he hrk hms
      have hsl : (Pattern.RHS.fixed (p := p) e cl).selfLeaves sel = [e] := by
        simp [Pattern.RHS.selfLeaves, Pattern.RHS.fixedLeaves, hs]
      have ht : ∀ j, mkInst ls ((Pattern.RHS.fixed (p := p) e cl).toVExpr sel K j) = .bvar j := by
        intro j; simp [Pattern.RHS.toVExpr, hs, mkInst]
      refine ⟨[s], by simp [hsl], fun i s' e' h1 h2 => ?_, fun j Γb ρ' _ hb _ _ T _ => ?_⟩
      · rw [hsl] at h2
        match i, h1, h2 with
        | 0, h1, h2 => cases h1; cases h2; exact hsf
      · have H : LE_Interp ρ' ms (mkInst ls ((Pattern.RHS.fixed (p := p) e cl).toVExpr sel K j)) := by
          rw [ht]; exact .bvar (hle.trans (by simpa using hb 0 s rfl))
        exact ⟨fun hy _ _ => H.mono hy, fun _ => H⟩
    · have hsl : (Pattern.RHS.fixed (p := p) e cl).selfLeaves sel = [] := by
        simp [Pattern.RHS.selfLeaves, Pattern.RHS.fixedLeaves, hs]
      have ht : ∀ j, mkInst ls ((Pattern.RHS.fixed (p := p) e cl).toVExpr sel K j) = mkInst ls e := by
        intro j; simp [Pattern.RHS.toVExpr, hs]
      refine ⟨[], by simp [hsl], fun i s' e' h1 _ => by simp at h1,
        fun j Γb ρ' _ _ _ _ T _ => ?_⟩
      have H : LE_Interp ρ' ms (mkInst ls ((Pattern.RHS.fixed (p := p) e cl).toVExpr sel K j)) := by
        rw [ht]; exact (LE_Interp.closed_iff cl.mkInstS).1 (hR _ _ hms)
      exact ⟨fun hy _ _ => H.mono hy, fun _ => H⟩
  | @var ms path hms =>
    refine ⟨[], by simp [Pattern.RHS.selfLeaves, Pattern.RHS.fixedLeaves],
      fun i s' e' h1 _ => by simp at h1, fun j Γb ρ' W _ hv1 _ T hT => ?_⟩
    have ht : mkInst ls ((Pattern.RHS.var (p := p) path).toVExpr sel K j) =
        .bvar (K + p.pathIdx path) := rfl
    rw [ht] at hT ⊢
    refine ⟨fun {n y b} hy hty hb => ?_, fun hh => .bvar (hms.trans (hh path rfl))⟩
    obtain ⟨-, -, hc, hTeq⟩ := hT
    cases hc with
    | bvar hL => exact .bvar (hv1 path hL (hy.trans hms) hty ((hTeq W).2 hb))
  | @app n f F A ms a _ _ hms ihf iha =>
    obtain ⟨slF, lF, fF, cF⟩ := ihf
    obtain ⟨slA, lA, fA, cA⟩ := iha
    refine ⟨slF ++ slA, by simp [Pattern.RHS.selfLeaves_app, lF, lA], fun i s e h1 h2 => ?_,
      fun j Γb ρ' W hb hv1 hv2 Ty hT => ?_⟩
    · rw [Pattern.RHS.selfLeaves_app] at h2
      by_cases hi : i < slF.length
      · rw [List.getElem?_append_left hi] at h1
        rw [List.getElem?_append_left (lF ▸ hi)] at h2
        exact fF i s e h1 h2
      · rw [List.getElem?_append_right (by omega)] at h1
        rw [List.getElem?_append_right (by omega), ← lF] at h2
        exact fA _ s e h1 h2
    · have ht : mkInst ls ((Pattern.RHS.app F A).toVExpr sel K j) =
          .app (mkInst ls (F.toVExpr sel K j))
            (mkInst ls (A.toVExpr sel K (j + slF.length))) := by
        rw [lF]; rfl
      rw [ht] at hT ⊢
      obtain ⟨-, -, hc, hTeq⟩ := hT
      cases hc with
      | app hA0 hFt hAt =>
      have bF : ∀ i s, slF[i]? = some s → s ≤ ρ' (j + i) := fun i s h =>
        hb i s (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]; exact h)
      have bA : ∀ i s, slA[i]? = some s → s ≤ ρ' (j + slF.length + i) := fun i s h => by
        rw [Nat.add_assoc]
        exact hb _ s (by rw [List.getElem?_append_right (by omega)]; simpa using h)
      have CF := cF j W bF hv1 hv2 hFt
      have CA := cA (j + slF.length) W bA hv1 hv2 hAt
      have GF : LE_Interp ρ' f.T (mkInst ls (F.toVExpr sel K j)) := by
        match F, CF, hFt with
        | .var path, CF, hFt =>
          rcases hv2 path with h | h
          · exact CF.2 fun _ e => by cases e; exact h
          · exfalso
            obtain ⟨-, -, hc', hTeq'⟩ := hFt
            cases hc' with
            | bvar hL =>
              obtain ⟨I', ls', k, rfl, hI⟩ := h _ hL
              exact T.const_indTy_not_forallE hI ((hTeq' W).2 T.forallE_bot_interp)
        | .fixed .., CF, _ => exact CF.2 fun _ e => by cases e
        | .app .., CF, _ => exact CF.2 fun _ e => by cases e
      have G : LE_Interp ρ' ms _ := T.app_collapse (hFt.sound W GF) CA.1 hms
      exact ⟨fun hy _ _ => G.mono hy, fun _ => G⟩

omit [Params] in
theorem T.onCtx_append_right {P : List VExpr → VExpr → Prop} :
    ∀ (Γ₁ : List VExpr) {Γ₂ : List VExpr}, OnCtx (Γ₁ ++ Γ₂) P → OnCtx Γ₂ P
  | [], _, h => h
  | _ :: Γ₁, _, h => T.onCtx_append_right Γ₁ h.1

/-- `RankParams.strong_below` for the whole environment (`Params.henv`). -/
theorem T.strong_env {U : Nat} {Γ : List VExpr} {e A : VExpr}
    (hΓ : OnCtx Γ (fun Γ A => Params.env.IsType U Γ A))
    (H : Params.env.HasType U Γ e A) (ls : List SLevel) :
    IsDefEqStrong Params.env (Γ.map (mkInst ls)) (mkInst ls e) (mkInst ls e) (mkInst ls A) := by
  obtain ⟨vs, hvs, rfl⟩ := SLevel.exists_map_mk ls
  have hS := (VEnv.IsDefEq.strong Params.henv hΓ H).instL hvs
  have := hS.mkSE (CtorProviderE.synE VEnv.LE.rfl) (onCtx_map_instL_levelWF hvs Γ)
  have hctx : Γ.map (mkInst (vs.map SLevel.mk)) = (Γ.map (VExpr.instL vs)).map SExpr.mk := by
    rw [List.map_map]; congr 1; funext B; exact mkInst_map_mk hvs
  rw [hctx, mkInst_map_mk hvs, mkInst_map_mk hvs]
  exact this

/-- Every bare-constant leaf of a well-typed unabstracted RHS has the right number of levels
(`StrongSoundCore.const`). -/
theorem T.leaf_levels {Γ : List SExpr} {ls : List SLevel} {p : Pattern} :
    ∀ (r : p.RHS) (j : Nat) {T : SExpr}, StrongSound Γ (mkInst ls (r.toVExpr (fun _ => false) 0 j)) T →
    ∀ {c' : Name} {us : List VLevel} {ci' : VConstant}, VExpr.const c' us ∈ r.fixedLeaves →
      Params.env.constants c' = some ci' → us.length = ci'.uvars
  | .fixed e _, j, T, hT, c', us, ci', hm, hc => by
    simp only [Pattern.RHS.fixedLeaves, List.mem_singleton] at hm; subst hm
    obtain ⟨-, -, hcore, -⟩ := hT
    cases hcore with
    | const h1 h2 => cases h1.symm.trans hc; simpa using h2
  | .var _, _, _, _, _, _, _, hm, _ => by simp [Pattern.RHS.fixedLeaves] at hm
  | .app F A, j, T, hT, c', us, ci', hm, hc => by
    obtain ⟨-, -, hcore, -⟩ := hT
    cases hcore with
    | app _ hF hA =>
      simp only [Pattern.RHS.fixedLeaves, List.mem_append] at hm
      rcases hm with hm | hm
      · exact T.leaf_levels F j hF hm hc
      · exact T.leaf_levels A _ hA hm hc

/-- From `pat_defeq`: every bare-constant leaf of the RHS has the right number of levels. -/
theorem T.pat_leaf_levels (RP : RankParams) {p : Pattern} {r : p.RHS × p.Check} {g : PatGen}
    {ci : VConstant} (hP : Params.Pat p r)
    (hg : Pattern.gen Params.env RP.rank Params.classify p r.1 = some g)
    (hci : Params.env.constants p.head = some ci) (ls : List SLevel) (Γ₀ : List SExpr)
    {c' : Name} {us : List VLevel} {ci' : VConstant} (hm : VExpr.const c' us ∈ r.1.fixedLeaves)
    (hc : Params.env.constants c' = some ci') : us.length = ci'.uvars := by
  have hΓ : OnCtx g.ctx (fun Γ A => Params.env.IsType ci.uvars Γ A) :=
    (T.onCtx_append_right g.self (RP.pat_typed hP hg hci).1).mono
      (fun h => h.mono (Params.env.below_le ..))
  have H := (T.strong_env hΓ (RP.pat_defeq hP hg hci).hasType.2 ls).weak_append (Γ₀ := Γ₀)
  have hrhs := (Pattern.gen_eq_some hg).2.2.1
  rw [hrhs] at H
  exact T.leaf_levels r.1 0 (LE_Interp.strongSoundS H).left hm hc

/-- E6a (PLAN D4 step 2), proved: the self entries of `W_p` and `LE_Interp ρ_low y' rhsAbs`
for every typed `y'` below the RHS shape whose type interprets `g.type`. Statement changes from
`RhsLowerStmt.lean:208-234` (module header): `RP`, `hR`, `hhead`, and the self clause's
`⊥`-or-`R`-witness disjunct (with the occurrence named and the level count unconditional). -/
theorem LR.rhs_lower (RP : RankParams) {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name}
    {ls : List SLevel} {R : TShape → SExpr → Prop} (LIH : LR.LocalIH RP.rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e)
    {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} {mC : TShape}
    (hP : Params.Pat p r) (hMt : LE_Interp.Matches p c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1)
    (g : PatGen) (hg : Pattern.gen Params.env RP.rank Params.classify p r.1 = some g)
    {fields : List TShape} {ρ : Valuation} {m : Nat} (hm : g.ctx.length = fields.length + m)
    (hfit : (Valuation.lowerCtx fields ρ m).Fits Γ₀ (g.ctx.map (SExpr.mkInst ls) ++ Γ₀))
    (hvar : ∀ path {n} {y b : WShape n}, y.T ≤ m2 path → y.HasType b →
      LE_Interp (Valuation.lowerCtx fields ρ m) b.T
        (SExpr.mkInst ls ((g.ctx.getD (p.pathIdx path) (.sort .zero)).liftN (p.pathIdx path + 1))) →
      y.T ≤ Valuation.lowerCtx fields ρ m (p.pathIdx path))
    (hhead : ∀ path, m2 path ≤ Valuation.lowerCtx fields ρ m (p.pathIdx path) ∨
      ∃ (I' : Name) (us : List VLevel) (k : Nat), g.ctx[p.pathIdx path]? = some (.const I' us) ∧
        Params.classify I' = some (.indTy k)) :
    ∃ selfs : List TShape, selfs.length = g.self.length ∧
      (∀ j s, selfs[j]? = some s → ∃ (c' : Name) (us : List VLevel) (ci' : VConstant),
        (r.1.selfLeaves (Pattern.sameRank RP.rank p.head))[j]? = some (.const c' us) ∧
        RP.rank c' = RP.rank c ∧ Params.env.constants c' = some ci' ∧ us.length = ci'.uvars ∧
        SExpr.mkInst ls (g.self.getD j (.sort .zero)) =
          SExpr.mkInst (us.map (SLevel.instV ls)) ci'.type ∧
        (∃ (k : Nat) (x b : WShape k), s = x.T ∧ x.HasType b ∧
          LE_Interp ρ₀ b.T (SExpr.mkInst (us.map (SLevel.instV ls)) ci'.type)) ∧
        LR.ConstGoal Γ₀ ρ₀ s c' (us.map (SLevel.instV ls)) ci' ∧
        ((∃ k, s = (WShape.bot (n := k)).T) ∨
          ∃ me, R me (.const c' (us.map (SLevel.instV ls))) ∧ me ≤ s)) ∧
      ∀ {n'} {y' a' : WShape n'}, y'.T ≤ mC → y'.HasType a' →
        LE_Interp (Valuation.lower selfs fields ρ m) a'.T
          (SExpr.mkInst ls (g.type.liftN g.self.length)) →
        LE_Interp (Valuation.lower selfs fields ρ m) y'.T (SExpr.mkInst ls g.rhsAbs) := by
  have hhd : p.head = c := T.matches_head hMt
  obtain ⟨⟨ci, hci⟩, hctxlen⟩ := T.gen_head_ctx hg
  obtain ⟨-, -, -, hAbs⟩ := Pattern.gen_eq_some hg
  have hpt := RP.pat_typed hP hg hci
  have hroot : StrongSound ((g.self ++ g.ctx).map (mkInst ls) ++ Γ₀) (mkInst ls g.rhsAbs)
      (mkInst ls (g.type.liftN g.self.length)) :=
    (LE_Interp.strongSoundS (((RP.strong_below hpt.1 hpt.2 ls).weak_append
      (Γ₀ := Γ₀)).mono (Params.env.below_le ..))).left
  have hsel : ∀ e, Pattern.sameRank RP.rank p.head e = true →
      ∃ c' us, e = .const c' us ∧ RP.rank c' = RP.rank c := fun e h => by
    obtain ⟨c', us, rfl, h'⟩ := Pattern.sameRank_eq_true.1 h; exact ⟨c', us, rfl, hhd ▸ h'⟩
  obtain ⟨sl, hlen, hfacts, hclaim⟩ := T.rhs_lower_core LIH hR (Pattern.sameRank RP.rank p.head)
    hsel g.self.length ((g.self ++ g.ctx).map (mkInst ls) ++ Γ₀) hRHS
  have hgs := Pattern.gen_self hg
  have hK : sl.length = g.self.length := hlen.trans hgs.1.symm
  refine ⟨sl, hK, fun j s hs => ?_, ?_⟩
  · have hj : j < (r.1.selfLeaves (Pattern.sameRank RP.rank p.head)).length :=
      hlen ▸ (List.getElem?_eq_some_iff.1 hs).1
    obtain ⟨e, he⟩ : ∃ e, (r.1.selfLeaves (Pattern.sameRank RP.rank p.head))[j]? = some e :=
      ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨c', us, ci', T', rfl, h1, h2, h3, -, h5⟩ := Pattern.gen_self_mkInst hg he ls
    have hgetD : g.self.getD j (.sort .zero) = T' := by simp [List.getD_eq_getElem?_getD, h3]
    have hmem : VExpr.const c' us ∈ r.1.fixedLeaves :=
      (Pattern.RHS.mem_selfLeaves.1 (List.mem_of_getElem? he)).1
    refine ⟨c', us, ci', he, hhd ▸ h2, h1, T.pat_leaf_levels RP hP hg hci ls Γ₀ hmem h1,
      by rw [hgetD, h5], ?_⟩
    rcases hfacts j s _ hs he with ⟨k, rfl⟩ | ⟨c'', us', ci'', me, he', h1', -, hR', hle, hty, hcg⟩
    · exact ⟨⟨k, .bot, .bot, rfl, .bot' (.bot' .sort), .bot⟩, .inl ⟨k, rfl⟩, .inl ⟨k, rfl⟩⟩
    · cases he'
      cases h1.symm.trans h1'
      exact ⟨hty, hcg, .inr ⟨me, hR', hle⟩⟩
  · have hΓ : (g.self ++ g.ctx).map (mkInst ls) ++ Γ₀ =
        g.self.map (mkInst ls) ++ (g.ctx.map (mkInst ls) ++ Γ₀) := by simp
    have W : Valuation.Fits Γ₀ ((g.self ++ g.ctx).map (mkInst ls) ++ Γ₀)
        (Valuation.lower sl fields ρ m) := by
      rw [hΓ]
      refine T.fits_foldr_push hfit _ sl (by simp [hK]) fun j A x hA hx => ?_
      rw [List.getElem?_map] at hA
      obtain ⟨Aj, hAj, rfl⟩ := Option.map_eq_some_iff.1 hA
      have hj : j < g.self.length := (List.getElem?_eq_some_iff.1 hAj).1
      obtain ⟨u, Hu⟩ := (EnvStrongR.of_params RP).ctx ls hP hg hci j Aj
        (by rw [List.getElem?_append_left hj]; exact hAj)
      have hctx : ((g.self ++ g.ctx).drop (j + 1)).map (mkInst ls) ++ Γ₀ =
          (g.self.map (mkInst ls)).drop (j + 1) ++ (g.ctx.map (mkInst ls) ++ Γ₀) := by
        rw [List.drop_append_of_le_length (by omega)]; simp [List.map_drop]
      refine ⟨⟨u, hctx ▸ (LE_Interp.strongSoundS ((Hu.weak_append (Γ₀ := Γ₀)).mono
        (Params.env.below_le ..))).left⟩, ?_⟩
      have hj' : j < (r.1.selfLeaves (Pattern.sameRank RP.rank p.head)).length := hgs.1 ▸ hj
      obtain ⟨e, he⟩ : ∃ e, (r.1.selfLeaves (Pattern.sameRank RP.rank p.head))[j]? = some e :=
        ⟨_, List.getElem?_eq_getElem hj'⟩
      obtain ⟨c', us, ci', T', rfl, h1, -, h3, -, h5⟩ := Pattern.gen_self_mkInst hg he ls
      cases hAj.symm.trans h3
      rcases hfacts j x _ hx he with ⟨k, rfl⟩ | ⟨c'', us', ci'', me, he', h1', -, -, -, hty, -⟩
      · exact ⟨_, fun _ => .bot, WShape.HasType.T (.bot' (.bot' .sort))⟩
      · cases he'
        cases h1.symm.trans h1'
        obtain ⟨k, x', b, rfl, hxb, hb⟩ := hty
        refine ⟨b.T, fun ρ' => ?_, WShape.HasType.T hxb⟩
        rw [h5]; exact (LE_Interp.closed_iff (Params.henv.closedC h1).mkInstS).1 hb
    have hb : ∀ (i : Nat) (s : TShape), sl[i]? = some s →
        s ≤ (Valuation.lower sl fields ρ m) (0 + i) := fun i s h => by
      rw [Nat.zero_add, Valuation.lower, T.foldr_push_lt _ sl i s h]; exact .rfl
    have hshift : ∀ i, Valuation.lower sl fields ρ m (g.self.length + i) =
        Valuation.lowerCtx fields ρ m i := fun i => by
      rw [← hK]; exact T.foldr_push_add _ sl i
    have hΓi : ∀ i (hi : i < g.ctx.length),
        ((g.self ++ g.ctx).map (mkInst ls) ++ Γ₀)[g.self.length + i]? =
          some (mkInst ls g.ctx[i]) := by
      intro i hi
      rw [List.getElem?_append_left (by simp; omega), List.getElem?_map,
        List.getElem?_append_right (by omega)]
      simp [List.getElem?_eq_getElem hi]
    have hv1 : ∀ path {n} {y b : WShape n} {T'},
        Lookup ((g.self ++ g.ctx).map (mkInst ls) ++ Γ₀) (g.self.length + p.pathIdx path) T' →
        y.T ≤ m2 path → y.HasType b → LE_Interp (Valuation.lower sl fields ρ m) b.T T' →
        y.T ≤ (Valuation.lower sl fields ρ m) (g.self.length + p.pathIdx path) := by
      intro path n y b T' hL hy hty hbT
      have hi : p.pathIdx path < g.ctx.length := hctxlen ▸ T.pathIdx_lt p path
      obtain ⟨B, hB, rfl⟩ := T.lookup_eq hL
      rw [hΓi _ hi] at hB; cases hB
      rw [hshift]
      refine hvar path hy hty ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
        T.mkInst_liftN]
      have e1 : g.self.length + p.pathIdx path + 1 = (p.pathIdx path + 1) + sl.length := by omega
      rw [e1, T.liftK_add] at hbT
      exact (T.LE_Interp_foldr_push_liftK sl).1 hbT
    have hv2 : ∀ path, m2 path ≤ (Valuation.lower sl fields ρ m) (g.self.length + p.pathIdx path) ∨
        ∀ T', Lookup ((g.self ++ g.ctx).map (mkInst ls) ++ Γ₀) (g.self.length + p.pathIdx path) T' →
          ∃ I' ls' k, T' = .const I' ls' ∧ Params.classify I' = some (.indTy k) := by
      intro path
      rcases hhead path with h | ⟨I', us, k, hc, hI⟩
      · exact .inl (by rw [hshift]; exact h)
      · refine .inr fun T' hL => ?_
        have hi : p.pathIdx path < g.ctx.length := hctxlen ▸ T.pathIdx_lt p path
        obtain ⟨B, hB, rfl⟩ := T.lookup_eq hL
        rw [hΓi _ hi] at hB; cases hB
        rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hc
        rw [hc]
        exact ⟨I', _, k, T.liftK_const .., hI⟩
    have C := hclaim 0 W hb hv1 hv2 (hAbs ▸ hroot)
    intro n' y' a' hy hty ha
    rw [hAbs]
    exact C.1 hy hty ha

/-! ## The pinned statement is false -/

/-- `historical/RhsLowerStmt.lean:208-234` verbatim as a proposition, with the stand-ins
instantiated: `gen := Pattern.gen`, `idx := Pattern.pathIdx p`; `rank` stays explicit. -/
def T.PinnedRhsLower (rank : Name → Nat) : Prop :=
  ∀ {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name} {ls : List SLevel}
    {R : TShape → SExpr → Prop} (_LIH : LR.LocalIH rank Γ₀ ρ₀ c R)
    {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} {mC : TShape}
    (_hP : Params.Pat p r) (_hMt : LE_Interp.Matches p c rargs m2)
    (_hRHS : LE_Interp.RHS ls m2 R mC r.1)
    (g : PatGen) (_hg : Pattern.gen Params.env rank Params.classify p r.1 = some g)
    {fields : List TShape} {ρ : Valuation} {m : Nat} (_hm : g.ctx.length = fields.length + m)
    (_hfit : (Valuation.lowerCtx fields ρ m).Fits Γ₀ (g.ctx.map (SExpr.mkInst ls) ++ Γ₀))
    (_hvar : ∀ path {n} {y b : WShape n}, y.T ≤ m2 path → y.HasType b →
      LE_Interp (Valuation.lowerCtx fields ρ m) b.T
        (SExpr.mkInst ls ((g.ctx.getD (p.pathIdx path) (.sort .zero)).liftN (p.pathIdx path + 1))) →
      y.T ≤ Valuation.lowerCtx fields ρ m (p.pathIdx path)),
    ∃ selfs : List TShape, selfs.length = g.self.length ∧
      (∀ j s, selfs[j]? = some s → ∃ (me : TShape) (c' : Name) (ls' : List SLevel) (ci' : VConstant),
        R me (.const c' ls') ∧ rank c' = rank c ∧ Params.env.constants c' = some ci' ∧
        ls'.length = ci'.uvars ∧ me ≤ s ∧
        SExpr.mkInst ls (g.self.getD j (.sort .zero)) = SExpr.mkInst ls' ci'.type ∧
        (∃ (k : Nat) (x b : WShape k), s = x.T ∧ x.HasType b ∧
          LE_Interp ρ₀ b.T (SExpr.mkInst ls' ci'.type)) ∧
        LR.ConstGoal Γ₀ ρ₀ s c' ls' ci') ∧
      ∀ {n'} {y' a' : WShape n'}, y'.T ≤ mC → y'.HasType a' →
        LE_Interp (Valuation.lower selfs fields ρ m) a'.T
          (SExpr.mkInst ls (g.type.liftN g.self.length)) →
        LE_Interp (Valuation.lower selfs fields ρ m) y'.T (SExpr.mkInst ls g.rhsAbs)

theorem T.instV_zero (ls : List SLevel) : SLevel.instV ls .zero = .zero := by
  apply Subtype.ext; funext v; rfl

theorem T.instV_one_ne (ls : List SLevel) : SLevel.instV ls (.succ .zero) ≠ .zero := by
  intro h; have := congrArg (fun l : SLevel => l.1 []) h
  simp [SLevel.instV, SLevel.zero, VLevel.eval] at this

/-- (F1) The pinned statement has no link from `R` to `LE_Interp`: it fails at the delta rule
`def c : Type := Prop` (RHS the closed leaf `Prop`), with `R := fun _ e => e = Prop`. -/
theorem T.pinned_false_const {rank : Name → Nat} (H : T.PinnedRhsLower rank) {c : Name}
    {r : (Pattern.const c).RHS × (Pattern.const c).Check} {cl : (VExpr.sort .zero).Closed}
    {g : PatGen} {ci : VConstant} (hP : Params.Pat (.const c) r) (hr : r.1 = .fixed (.sort .zero) cl)
    (hg : Pattern.gen Params.env rank Params.classify (.const c) r.1 = some g)
    (hci : Params.env.constants c = some ci) (hty : ci.type = .sort (.succ .zero)) : False := by
  obtain ⟨ci', hci', hctx, -, htype⟩ := Pattern.gen_delta hg
  cases hci.symm.trans hci'
  obtain ⟨-, -, -, hAbs⟩ := Pattern.gen_eq_some hg
  have hself : g.self = [] := by
    have := (Pattern.gen_self hg).1
    rw [hr] at this
    simpa [Pattern.RHS.selfLeaves, Pattern.RHS.fixedLeaves, Pattern.sameRank] using this
  have hrhs : g.rhsAbs = .sort .zero := by
    rw [hAbs, hr]; simp [Pattern.RHS.toVExpr, Pattern.sameRank]
  have hRHS : LE_Interp.RHS (p := .const c) [] nofun (fun _ e => e = mkInst [] (.sort .zero))
      (WShape.sort (n := 0) true).T r.1 := hr ▸ .const rfl
  obtain ⟨selfs, -, -, hmain⟩ := H (Γ₀ := []) (ρ₀ := .nil) (c := c)
    (fun _ _ he _ _ _ he' => by rw [he'] at he; cases he)
    (rargs := ([] : List (WShape 0))) hP .const hRHS g hg (fields := []) (ρ := .nil) (m := 0) (by simp [hctx])
    (by rw [hctx]; exact .nil) (fun path => path.elim)
  have ha : LE_Interp (Valuation.lower selfs [] .nil 0) (WShape.sort (n := 0) true).T
      (mkInst [] (g.type.liftN g.self.length)) := by
    rw [hself, htype, hty]
    refine .sort ?_
    simp only [ne_eq, T.instV_one_ne, not_false_eq_true, decide_true]
    exact TShape.sort_eqv.1
  have h := (hmain (y' := WShape.sort (n := 0) true) (a' := WShape.sort true) .rfl .sort ha)
  rw [hrhs] at h
  have h2 := h.le_sort
  simp only [T.instV_zero, ne_eq, not_true_eq_false, decide_false] at h2
  have h3 := WShape.LE.of_T (h2.trans TShape.sort_eqv.2)
  rcases WShape.le_sort.1 h3 with h4 | h4 <;> cases congrArg (·.1) h4

/-- All-`⊥` arguments match a `varN` pattern, binding every path to `⊥`. -/
theorem T.matches_varN_bot {n : Nat} (c : Name) : ∀ k, ∃ m2,
    LE_Interp.Matches (n := n) (.varN (.const c) k) c (List.replicate k WShape.bot) m2 ∧
      ∀ path, m2 path ≤ TShape.bot
  | 0 => ⟨nofun, .const, nofun⟩
  | k+1 => by
    obtain ⟨m2, h1, h2⟩ := T.matches_varN_bot c k
    refine ⟨_, .var h1, fun path => ?_⟩
    cases path with
    | none => exact TShape.bot_eqv.1
    | some x => exact h2 x

/-- (F2) The pinned statement demands an `R`-witness for every self entry: it fails at every
iota rule with a same-rank bare leaf (e.g. `Nat.rec`'s `succ` rule), with `R := ∅`,
`hRHS := .bot`, all-`⊥` arguments and the all-`⊥` lowered context (which `Fits` by
`pat_typed`'s context typings). -/
theorem T.pinned_false_iota (RP : RankParams) (H : T.PinnedRhsLower RP.rank)
    {rec c' : Name} {mm k : Nat} {r : (Pattern.iota rec mm c' k).RHS × (Pattern.iota rec mm c' k).Check}
    {g : PatGen} (hP : Params.Pat (.iota rec mm c' k) r)
    (hg : Pattern.gen Params.env RP.rank Params.classify (.iota rec mm c' k) r.1 = some g)
    (hne : g.self ≠ []) : False := by
  obtain ⟨⟨ci, hci⟩, -⟩ := T.gen_head_ctx hg
  obtain ⟨mf, hf1, hf2⟩ := T.matches_varN_bot (n := 1) rec mm
  obtain ⟨ma, ha1, ha2⟩ := T.matches_varN_bot (n := 0) c' k
  have hM := LE_Interp.Matches.app hf1 ha1
  have hfit : (Valuation.lowerCtx (List.replicate g.ctx.length TShape.bot) .nil 0).Fits []
      (g.ctx.map (mkInst []) ++ []) := by
    refine T.fits_foldr_push .nil (g.ctx.map (mkInst [])) _ (by simp) fun j A x hA hx => ?_
    rw [List.getElem?_map] at hA
    obtain ⟨Aj, hAj, rfl⟩ := Option.map_eq_some_iff.1 hA
    rw [List.getElem?_replicate] at hx; split at hx <;> cases hx
    obtain ⟨u, Hu⟩ := (EnvStrongR.of_params RP).ctx [] hP hg hci (g.self.length + j) Aj
      (by rw [List.getElem?_append_right (by omega)]; simpa using hAj)
    have hctx : ((g.self ++ g.ctx).drop (g.self.length + j + 1)).map (mkInst []) ++ [] =
        (g.ctx.map (mkInst [])).drop (j + 1) ++ [] := by
      rw [Nat.add_assoc, List.drop_append]; simp [List.map_drop]
    exact ⟨⟨u, hctx ▸ (LE_Interp.strongSoundS ((Hu.weak_append (Γ₀ := [])).mono
      (Params.env.below_le ..))).left⟩, TShape.bot, fun _ => .bot,
      .bot' (.bot' (TShape.HasType.sort (r := true)))⟩
  obtain ⟨selfs, hlen, hself, -⟩ := H (Γ₀ := []) (ρ₀ := .nil) (ls := [])
    (R := fun _ _ => False) (fun _ _ h => h.elim) hP hM
    (mC := (WShape.bot (n := 0)).T) .bot g hg (by simp) hfit
    (fun path {n y b} hy _ _ => by
      have h0 : y.T ≤ TShape.bot := hy.trans (by cases path with
        | inl x => exact hf2 x | inr x => exact ha2 x)
      rw [TShape.le_bot'.1 h0]; exact TShape.bot_le')
  obtain ⟨s, hs⟩ : ∃ s, selfs[0]? = some s := by
    have : 0 < selfs.length := by
      rw [hlen]; exact List.length_pos_iff.2 hne
    exact ⟨_, List.getElem?_eq_getElem this⟩
  obtain ⟨_, _, _, _, h, -⟩ := hself 0 s hs
  exact h

end Lean4Lean.SExpr
