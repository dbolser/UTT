import Lean4Lean.Experimental.E3.Measure7
/-! # E6a: the field-entry lowering for the pattern leaf (PLAN.md §2 row E6a, §1 D4 steps 1-2)

Default option (a): the lowered valuation `ρ_low` (`Valuation.lowerCtx`/`Valuation.lower`, exactly
`docs/const-case/plan/historical/RhsLowerStmt.lean:195-205`) and the lowering lemma.

Verdict: the pinned statement `LR.rhs_lower` (`RhsLowerStmt.lean:208-226` with `gen :=
Pattern.gen`, `idx := p.genIdx`, `rank := RP.rank`) is FALSE. `Toy.lean` refutes it in two
concrete `Params` + `RankParams` models (`LR.rhs_lower_unprovable`): its self conjunct fails at
self occurrences inside `⊥` subtrees of `hRHS` (P2; `LR.rhs_lower_forces_no_self` shows it forces
`g.self = []` for every rule, even with `hR hrec hfield` added), and its main conjunct fails
without `hR` (P1, at a rule with no self occurrence). Its proof here reduces it to the corrected
lemma `LR.rhs_lower'` and leaves exactly four marked sorries (`hR`, `hrec`, `hfield`, P2).

`LR.rhs_lower'` (sorry-free) proves D4's argument [A] with `hR hrec hfield` added and the self
conjunct changed (the occurrence pinned, the arity fact for every entry via `LR.selfOcc_uvars`,
the `R`-witness only when `s ≠ ⊥`). Its engine is `LR.rhs_core`, an induction on `LE_Interp.RHS`
against the syntax-directed typing `StrongSound` of `rhsAbs` (from `pat_typed` via
`EnvStrongR.pat_rhs`, `weak_append`, `strongSoundS`) at `ρ_low` (which `Fits`): every node gets a
typed upper bound interpreting it (`InterpTyped`, via `SoundTy`), except a field variable, which
gets the typed-below conjunct from `hvar`; at an application the function's typed upper bound has
`HasDom`, so the raw argument collapses to a typed part below it (`LE_Interp.app_collapse`,
`WShape.HasDom.iff`), where the argument's typed-below conjunct applies. Self entries come from
`LIH` alone; `hR` is used only at fixed leaves that are not self occurrences.
`LR.rhs_lower_iota` discharges `hrec`/`hfield` from what the pat leaf has (iota pattern,
`fields.length = n`, the spine lemma's `hρ`, `RP`): only `hR` is left. `hR` is `h7` of
`LR.const_local`'s `LE_Interp.const` node: `LR.const_local_of_spineR` re-proves `const_local`
against R9's statement with `hR` added (`LR.ConstSpineR`), so R9/R10 must take `hR`. -/
namespace Lean4Lean

theorem Pattern.gen_shape {env : VEnv} {rank : Name → Nat} {classify} {p : Pattern} {r : p.RHS}
    {g : PatGen} (hg : Pattern.gen env rank classify p r = some g) :
    (∃ c, p = .const c) ∨ ∃ rec m c' n, p = .app (.varN (.const rec) m) (.varN (.const c') n) := by
  match p, r, hg with
  | .const c, _, _ => exact .inl ⟨c, rfl⟩
  | .var _, _, hg => simp [gen] at hg
  | .app f a, r, hg =>
    simp only [gen, genIota] at hg
    split at hg
    · rename_i rec m c' n h1 h2
      exact .inr ⟨rec, m, c', n, by rw [eq_varN_of_constVarN? h1, eq_varN_of_constVarN? h2]⟩
    · cases hg

theorem Pattern.gen_head_const {env : VEnv} {rank : Name → Nat} {classify} {p : Pattern}
    {r : p.RHS} {g : PatGen} (hg : Pattern.gen env rank classify p r = some g) :
    ∃ ci, env.constants p.head = some ci := by
  rcases gen_shape hg with ⟨c, rfl⟩ | ⟨rec, m, c', n, rfl⟩
  · obtain ⟨ci, h, -⟩ := gen_delta hg; exact ⟨ci, h⟩
  · obtain ⟨ci, -, -, -, -, -, -, -, h, -⟩ := gen_iota hg
    exact ⟨ci, by simpa [head, head_varN] using h⟩

theorem Pattern.gen_genIdx_lt' {env : VEnv} {rank : Name → Nat} {classify} {p : Pattern}
    {r : p.RHS} {g : PatGen} (hg : Pattern.gen env rank classify p r = some g) (path : p.Path) :
    p.genIdx path < g.ctx.length := by
  rcases gen_shape hg with ⟨c, rfl⟩ | ⟨rec, m, c', n, rfl⟩
  · exact nomatch path
  · exact gen_genIdx_lt hg path

theorem Pattern.gen_ctx_iota {env : VEnv} {rank : Name → Nat} {classify} {rec c' : Name}
    {m n : Nat} {r : (Pattern.app (.varN (.const rec) m) (.varN (.const c') n)).RHS} {g : PatGen}
    (hg : Pattern.gen env rank classify (.app (.varN (.const rec) m) (.varN (.const c') n)) r = some g) :
    g.ctx.length = n + m := by
  obtain ⟨ci, Hs, I, us, Bmaj, ci', Fs, X, -, hHs, -, -, -, hFs, -, hc⟩ := gen_iota hg
  obtain ⟨_, _, rfl⟩ := genCore_eq_some.1 hc
  simp [hHs, hFs]

theorem VExpr.foldr_forallE_max : ∀ {Ts Ts' : List VExpr} {B B' : VExpr},
    (∀ A C, B ≠ .forallE A C) → (∀ A C, B' ≠ .forallE A C) →
    Ts.foldr .forallE B = Ts'.foldr .forallE B' → Ts = Ts'
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, hB, _, h => absurd h (hB _ _)
  | _ :: _, [], _, _, _, hB', h => absurd h.symm (hB' _ _)
  | T :: Ts, T' :: Ts', _, _, hB, hB', h => by
    simp only [List.foldr_cons, VExpr.forallE.injEq] at h
    rw [h.1, foldr_forallE_max hB hB' h.2]

theorem VExpr.foldr_app_ne_forallE {I : Name} {us : List VLevel} :
    ∀ (args : List VExpr) (A C : VExpr),
      args.foldr (fun A acc => VExpr.app acc A) (VExpr.const I us) ≠ VExpr.forallE A C
  | [], _, _ => nofun
  | _ :: _, _, _ => nofun

namespace SExpr
variable [Params]

/-! ## The lowered valuation (D4 step 1), exactly `RhsLowerStmt.lean:195-205` -/

/-- ρ_low's pattern-context part (PLAN D4 step 1), over `.nil` (the valuation of `SubstWF.id`,
base context `Γ₀`), innermost first: the lowered field entries `fields`, then the recursor
arguments `ρ 1 … ρ m` (`ρ 0` is the major). -/
def Valuation.lowerCtx (fields : List TShape) (ρ : Valuation) (m : Nat) : Valuation :=
  fields.foldr (fun x ρ' => ρ'.push x) <|
    (List.range m).foldr (fun i ρ' => ρ'.push (ρ (i + 1))) .nil

/-- ρ_low (PLAN D4 step 1): the self entries (index `j` = `j`-th self) on top of `lowerCtx`. -/
def Valuation.lower (selfs fields : List TShape) (ρ : Valuation) (m : Nat) : Valuation :=
  selfs.foldr (fun x ρ' => ρ'.push x) (Valuation.lowerCtx fields ρ m)

theorem LE_Interp.Matches.head_eq {p : Pattern} {c : Name} {n} {rargs : List (WShape n)} {m2}
    (H : LE_Interp.Matches p c rargs m2) : p.head = c := by
  induction H with
  | const => rfl
  | var _ ih => exact ih
  | app _ _ ih => exact ih

/-- `xs.foldr push base`: `xs[i]` at `i < xs.length` (`xs[0]` outermost, `bvar 0`). -/
theorem Valuation.foldr_push_lt {base : Valuation} :
    ∀ (xs : List TShape) {i : Nat} (h : i < xs.length),
      (xs.foldr (fun x ρ' => ρ'.push x) base) i = xs[i]
  | _ :: _, 0, _ => rfl
  | _ :: xs, _+1, h => foldr_push_lt xs (Nat.lt_of_succ_lt_succ h)

theorem Valuation.foldr_push_add {base : Valuation} :
    ∀ (xs : List TShape) (k : Nat), (xs.foldr (fun x ρ' => ρ'.push x) base) (xs.length + k) = base k
  | [], k => by simp
  | x :: xs, k => by
    simp only [List.foldr_cons, List.length_cons, Nat.add_right_comm _ 1 k]
    exact foldr_push_add xs k

theorem LE_Interp.foldr_push_liftK {base : Valuation} {a : TShape} {Y : SExpr} :
    ∀ xs : List TShape,
      LE_Interp (xs.foldr (fun x ρ' => ρ'.push x) base) a (liftK Y xs.length) ↔ LE_Interp base a Y
  | [] => Iff.rfl
  | _ :: xs => LE_Interp.weak_iff.trans (foldr_push_liftK xs)

theorem liftK_add (e : SExpr) (a : Nat) : ∀ b, liftK e (a + b) = liftK (liftK e a) b
  | 0 => rfl
  | b+1 => congrArg SExpr.lift (liftK_add e a b)

theorem mkInst_liftN {ls : List SLevel} (e : VExpr) : ∀ k, mkInst ls (e.liftN k) = liftK (mkInst ls e) k
  | 0 => by simp [liftK]
  | k+1 => by
    rw [VExpr.liftN_succ, liftK, ← mkInst_liftN e k, VExpr.lift_eq_lift', mkInst_lift']

/-- The lookup type of the `i`-th entry of the middle block `C` of `S ++ C ++ Γ₀`. -/
theorem Lookup.mid {S C Γ₀ : List SExpr} {i : Nat} (hi : i < C.length) {L : SExpr}
    (h : Lookup (S ++ C ++ Γ₀) (S.length + i) L) : L = liftK C[i] (S.length + i + 1) := by
  have := Lookup.append_self (A := C[i]) (Γ := C.drop (i+1) ++ Γ₀) (S ++ C.take i)
  have e1 : (S ++ C.take i) ++ C[i] :: (C.drop (i+1) ++ Γ₀) = S ++ C ++ Γ₀ := by
    rw [List.append_assoc, List.append_assoc]; congr 1
    rw [← List.cons_append, List.getElem_cons_drop hi, ← List.append_assoc,
      List.take_append_drop]
  have e2 : (S ++ C.take i).length = S.length + i := by
    simp [Nat.min_eq_left (Nat.le_of_lt hi)]
  rw [e1, e2] at this
  exact h.determ this

/-- Extend a `Fits` by closed, typed entries (the self entries of `ρ_low`). -/
theorem Valuation.Fits.foldr_push {Γ₀ D : List SExpr} {base : Valuation}
    (W : Valuation.Fits Γ₀ D base) :
    ∀ (xs : List TShape) (As : List SExpr), xs.length = As.length →
      (∀ (i : Nat) x A, xs[i]? = some x → As[i]? = some A → A.ClosedN ∧
        (∀ {a}, LE_Interp .nil a A → ∃ a', a ≤ a' ∧ LE_Interp .nil a' A ∧ a'.HasType .type) ∧
        ∃ b, LE_Interp .nil b A ∧ x.HasType b) →
      Valuation.Fits Γ₀ (As ++ D) (xs.foldr (fun x ρ' => ρ'.push x) base)
  | [], [], _, _ => W
  | x :: xs, A :: As, hl, H => by
    obtain ⟨cl, hcl, b, hb, hx⟩ := H 0 x A rfl rfl
    refine .cons (foldr_push W xs As (by simpa using hl) fun i x A h1 h2 => H (i+1) x A h1 h2)
      (fun h => ?_) ((LE_Interp.closed_iff cl).1 hb) hx
    obtain ⟨a', h1, h2, h3⟩ := hcl ((LE_Interp.closed_iff cl).1 h)
    exact ⟨a', h1, (LE_Interp.closed_iff cl).1 h2, h3⟩

/-- D4's [A] at one application: a typed upper bound of the function (`InterpTyped`, at a Π type)
has `HasDom`, so the raw argument `a` collapses to a typed part `x' ≤ a` with the same output
(`WShape.HasDom.iff`); only typed parts of the argument need to interpret `X`. -/
theorem LE_Interp.app_collapse {ρ : Valuation} {F X A B : SExpr} {n : Nat} {f : WShape (n+1)}
    {a : WShape n} (hF : InterpTyped ρ f.T F (.forallE A B))
    (hX : ∀ {k} (x t : WShape k), x.T ≤ a.T → x.HasType t → LE_Interp ρ t.T A → LE_Interp ρ x.T X) :
    LE_Interp ρ (f.app a).T (F.app X) := by
  by_cases hm : (f.app a).T ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ .bot
  obtain ⟨f_ts, s_ts, le_f, a2, a3, a4⟩ := hF
  have hf : ¬f_ts ≤ .bot := fun h => by
    apply hm
    rw [show f = .bot from TShape.le_bot.1 (le_f.trans h), WShape.bot_app]
    exact TShape.bot_le'
  have hs : ¬s_ts ≤ .bot := fun h => hf (a4.bot_r' h)
  cases a3 with | bot => cases hs TShape.bot_le' | forallE b1 b2 b3 b4 b5
  rename_i npi b_pi b_pi' f_pi
  cases b5.le_forall with | bot b5 => cases hs b5 | @forallE m _ _ _ _ b5 b6
  obtain c1 | ⟨n₂, g_lam, rfl, c1⟩ := a4.ty_forallE_inv; · cases hf (c1 ▸ .rfl)
  let k := max (max n₂ m) n
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  have c1 := (TShape.HasTypeLam.def hk.1.1 hk.1.2).1 c1
  have c1_d := WShape.HasDom.iff.1 c1.2.1
  obtain ⟨x', e1, e2, e3⟩ := c1_d (a.lift k)
  have hb : LE_Interp ρ (WShape.lift k _).T A := (b1.mono b5).lift hk.1.2
  have hx' : LE_Interp ρ x'.T X := hX x' _ (e1.T.trans (TShape.lift_eqv hk.2).1) e2 hb
  refine .mono ?_ (.app' (a2.lift (Nat.succ_le_succ hk.1.1)) hx')
  refine .trans (TShape.app_mono (le_f.trans (TShape.lift_eqv (Nat.succ_le_succ hk.1.1)).2)
    (TShape.lift_eqv hk.2).2) ?_
  rw [WShape.lift_lam' hk.1.1, WShape.lam'_app, WShape.lam'_app]
  exact e3.T

/-- `forallE ⊥ ⊥` interprets every Π type (used to refute a field variable in function position). -/
theorem LE_Interp.forallE_botShape {ρ : Valuation} {A B : SExpr} :
    LE_Interp ρ (WShape.forallE (n := 0) .bot .bot).T (.forallE A B) :=
  .forallE' .bot .bot (.bot (.bot' .sort)) fun _ _ => WShapeFun.bot_app ▸ .bot

theorem TShape.forallE_not_le_indTy :
    ¬ (WShape.forallE (n := 0) .bot .bot).T ≤ (WShape.indTy (n := 0)).T := by
  intro h
  rcases WShape.le_indTy.1 (WShape.LE.of_T h) with h | h <;> cases congrArg (·.1) h

/-- What `LR.rhs_core` proves at each node of the RHS: the typed-below conjunct, and either a typed
upper bound interpreting the node (`InterpTyped`), or the node is a variable whose type is only
interpreted below `indTy` (a stage-1a field variable, never in function position). -/
def LR.RhsClaim (Δ : List SExpr) (ρL : Valuation) (m : TShape) (M T : SExpr) : Prop :=
  (∀ {k} (y t : WShape k), y.T ≤ m → y.HasType t → LE_Interp ρL t.T T → LE_Interp ρL y.T M) ∧
  (InterpTyped ρL m M T ∨ ∃ i, M = .bvar i ∧
    ∀ L, Lookup Δ i L → ∀ a, LE_Interp ρL a L → a ≤ (WShape.indTy (n := 0)).T)

theorem LR.RhsClaim.of_interp {Γ₀ Δ : List SExpr} {ρL : Valuation} {m : TShape} {M T : SExpr}
    (hT : StrongSound Δ M T) (W : Valuation.Fits Γ₀ Δ ρL) (h : LE_Interp ρL m M) :
    LR.RhsClaim Δ ρL m M T :=
  ⟨fun _ _ h1 _ _ => h.mono h1, .inl (hT.sound W h)⟩

/-- A node in function position (its type a Π) is never the field-variable exception. -/
theorem LR.RhsClaim.fn {Γ₀ Δ : List SExpr} {ρL : Valuation} {m : TShape} {M A B : SExpr}
    (hT : StrongSound Δ M (.forallE A B)) (W : Valuation.Fits Γ₀ Δ ρL)
    (H : LR.RhsClaim Δ ρL m M (.forallE A B)) : InterpTyped ρL m M (.forallE A B) := by
  refine H.2.resolve_right fun ⟨i, hi, hL⟩ => ?_
  subst hi
  obtain ⟨_, _, core, seq⟩ := hT
  cases core with
  | bvar hl => exact TShape.forallE_not_le_indTy (hL _ hl _ ((seq W).2 LE_Interp.forallE_botShape))

/-- The engine of `LR.rhs_lower'`: induction on `hRHS`, producing the self entries of the subtree
(an entry `Ent c us s` per same-rank occurrence, `⊥` inside `⊥` subtrees) and, at every valuation
`ρL` that `Fits` `Δ`, covers them, and bounds the path shapes (rec-arg: raw below the entry; field:
type below `indTy` and typed parts below the entry), the claim `LR.RhsClaim` for any `StrongSound`
type of the node. -/
theorem LR.rhs_core {p : Pattern} {Γ₀ Δ : List SExpr} {ρ₀ : Valuation} {ls : List SLevel}
    {m2 : p.Path → TShape} {R : TShape → SExpr → Prop}
    (sel : VExpr → Option (Name × List VLevel)) (idx : p.Path → Nat) (S : Nat)
    (Ent : Name → List VLevel → TShape → Prop)
    (hEnt_bot : ∀ c us, Ent c us TShape.bot)
    (hEnt : ∀ e c us m, sel e = some (c, us) → R m (mkInst ls e) → ∃ s, m ≤ s ∧ Ent c us s)
    (hfix : ∀ e m, sel e = none → R m (mkInst ls e) → LE_Interp ρ₀ m (mkInst ls e)) :
    ∀ {mC : TShape} {r₀ : p.RHS}, LE_Interp.RHS ls m2 R mC r₀ → ∀ j : Nat,
    ∃ selfs₀ : List TShape, selfs₀.length = (r₀.selfConsts sel).length ∧
      (∀ (i : Nat) s c us, selfs₀[i]? = some s → (r₀.selfConsts sel)[i]? = some (c, us) →
        Ent c us s) ∧
      ∀ ρL : Valuation, Valuation.Fits Γ₀ Δ ρL →
        (∀ (i : Nat) s, selfs₀[i]? = some s → s ≤ ρL (j + i)) →
        (∀ path, m2 path ≤ ρL (S + idx path) ∨
          ((∀ L, Lookup Δ (S + idx path) L → ∀ a, LE_Interp ρL a L →
              a ≤ (WShape.indTy (n := 0)).T) ∧
           ∀ L, Lookup Δ (S + idx path) L → ∀ {k} (y t : WShape k), y.T ≤ m2 path → y.HasType t →
             LE_Interp ρL t.T L → y.T ≤ ρL (S + idx path))) →
        ∀ T, StrongSound Δ (mkInst ls (r₀.toVExpr sel idx S j)) T →
          LR.RhsClaim Δ ρL mC (mkInst ls (r₀.toVExpr sel idx S j)) T := by
  intro mC r₀ H
  induction H with
  | @bot _ r =>
    intro j
    refine ⟨List.replicate (r.selfConsts sel).length TShape.bot, List.length_replicate ..,
      fun i s c us h1 _ => ?_, fun ρL W _ _ T hT => .of_interp hT W .bot⟩
    rw [List.getElem?_replicate] at h1
    split at h1 <;> cases h1
    exact hEnt_bot c us
  | @const m e cl h1 =>
    intro j
    cases hs : sel e with
    | none =>
      refine ⟨[], by simp [Pattern.RHS.selfConsts, hs], by simp, fun ρL W _ _ T hT => ?_⟩
      simp only [Pattern.RHS.toVExpr, hs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hT ⊢
      exact .of_interp hT W ((LE_Interp.closed_iff cl.mkInstS).1 (hfix e m hs h1))
    | some x =>
      obtain ⟨c', us⟩ := x
      obtain ⟨s, hms, hE⟩ := hEnt e c' us m hs h1
      refine ⟨[s], by simp [Pattern.RHS.selfConsts, hs], fun i s' c us' h1 h2 => ?_,
        fun ρL W hsl _ T hT => ?_⟩
      · cases i with
        | zero =>
          simp [Pattern.RHS.selfConsts, hs] at h2 h1
          obtain ⟨rfl, rfl⟩ := h2; subst h1; exact hE
        | succ i => simp at h1
      · simp only [Pattern.RHS.toVExpr, hs, Option.isSome_some, ↓reduceIte, mkInst] at hT ⊢
        have := hsl 0 s rfl
        exact .of_interp hT W (.bvar (hms.trans this))
  | @var m path h1 =>
    intro j
    refine ⟨[], by simp [Pattern.RHS.selfConsts], by simp, fun ρL W _ hv T hT => ?_⟩
    simp only [Pattern.RHS.toVExpr, mkInst] at hT ⊢
    rcases hv path with h | ⟨hF1, hF2⟩
    · exact .of_interp hT W (.bvar (h1.trans h))
    · refine ⟨fun y t hy ht hA => ?_, .inr ⟨_, rfl, hF1⟩⟩
      obtain ⟨_, _, core, seq⟩ := hT
      cases core with
      | bvar hl => exact .bvar (hF2 _ hl y t (hy.trans h1) ht ((seq W).2 hA))
  | @app n f F A m a hf ha hle ihf iha =>
    intro j
    obtain ⟨sF, hlF, hEF, hF⟩ := ihf j
    obtain ⟨sA, hlA, hEA, hA⟩ := iha (j + (F.selfConsts sel).length)
    refine ⟨sF ++ sA, by simp [Pattern.RHS.selfConsts, hlF, hlA], fun i s c us h1 h2 => ?_,
      fun ρL W hsl hv T hT => ?_⟩
    · simp only [Pattern.RHS.selfConsts] at h2
      rcases Nat.lt_or_ge i sF.length with hi | hi
      · rw [List.getElem?_append_left hi] at h1
        rw [List.getElem?_append_left (hlF ▸ hi)] at h2
        exact hEF i s c us h1 h2
      · rw [List.getElem?_append_right hi] at h1
        rw [List.getElem?_append_right (hlF ▸ hi), ← hlF] at h2
        exact hEA _ s c us h1 h2
    · simp only [Pattern.RHS.toVExpr, mkInst] at hT ⊢
      obtain ⟨_, hsT, core, seq⟩ := hT
      cases core with
      | app hA' hFS hAS =>
        have cF := hF ρL W (fun i s h => hsl i s (by
          rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]; exact h)) hv _ hFS
        have cA := hA ρL W (fun i s h => by
          have := hsl (sF.length + i) s (by rw [List.getElem?_append_right (Nat.le_add_right ..)]; simpa using h)
          rw [Nat.add_assoc, ← hlF]; exact this) hv _ hAS
        have hlow := LE_Interp.app_collapse (cF.fn hFS W) (fun x t h1 h2 h3 => cA.1 x t h1 h2 h3)
        exact .of_interp ⟨‹_›, hsT, .app hA' hFS hAS, seq⟩ W (hlow.mono hle)

theorem Valuation.lower_lt {selfs fields : List TShape} {ρ : Valuation} {m i : Nat}
    (h : i < selfs.length) : Valuation.lower selfs fields ρ m i = selfs[i] :=
  Valuation.foldr_push_lt selfs h

theorem Valuation.lower_add {selfs fields : List TShape} {ρ : Valuation} {m k : Nat} :
    Valuation.lower selfs fields ρ m (selfs.length + k) = Valuation.lowerCtx fields ρ m k :=
  Valuation.foldr_push_add selfs k

/-- Every selected occurrence of a well-typed open RHS is a declared constant at its arity
(typing inversion, `VEnv.HasType.app_inv`/`const_inv`). -/
theorem LR.selfConsts_uvars {p : Pattern} {sel : VExpr → Option (Name × List VLevel)}
    (hsel : ∀ e c us, sel e = some (c, us) → e = .const c us) {idx : p.Path → Nat}
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (Params.env.IsType U)) :
    ∀ (r : p.RHS) {V}, Params.env.HasType U Γ (r.toOpen idx) V →
      ∀ c us, (c, us) ∈ r.selfConsts sel →
        ∃ ci, Params.env.constants c = some ci ∧ us.length = ci.uvars
  | .fixed e _, V, H, c, us, hm => by
    simp only [Pattern.RHS.selfConsts, Option.mem_toList] at hm
    have := hsel e c us hm; subst this
    obtain ⟨ci, h1, -, h3⟩ := VEnv.HasType.const_inv Params.henv hΓ H
    exact ⟨ci, h1, h3⟩
  | .var _, _, _, _, _, hm => by simp [Pattern.RHS.selfConsts] at hm
  | .app f a, V, H, c, us, hm => by
    obtain ⟨A, B, hf, ha⟩ := VEnv.HasType.app_inv Params.henv hΓ H
    simp only [Pattern.RHS.selfConsts, List.mem_append] at hm
    rcases hm with hm | hm
    · exact selfConsts_uvars hsel hΓ f hf c us hm
    · exact selfConsts_uvars hsel hΓ a ha c us hm

/-- Every self occurrence `(c', us)` of a rule is a declared constant with `us.length = ci'.uvars`
(from `RP.pat_typed` and `RP.pat_defeq` by typing inversion). So the self conjunct's arity fact
holds for every entry, `⊥` ones included, without `hR`. -/
theorem LR.selfOcc_uvars (RP : RankParams) {p : Pattern} {r : p.RHS × p.Check}
    (hP : Params.Pat p r) {g : PatGen}
    (hg : Pattern.gen Params.env RP.rank Params.classify p r.1 = some g) {ci : VConstant}
    (hci : Params.env.constants p.head = some ci) {c' : Name} {us : List VLevel}
    (hj : (c', us) ∈ r.1.selfOccs RP.rank (RP.rank p.head)) :
    ∃ ci', Params.env.constants c' = some ci' ∧ us.length = ci'.uvars := by
  have hΓ : OnCtx g.ctx (Params.env.IsType ci.uvars) := by
    have h := (RP.pat_typed hP hg hci).1
    generalize g.self = S at h
    induction S with
    | nil => exact h.mono fun h => h.mono (Params.env.below_le ..)
    | cons _ S ih => exact ih h.1
  have H := (RP.pat_defeq hP hg hci).hasType.2
  rw [(Pattern.gen_rhs_eq hg).1] at H
  exact LR.selfConsts_uvars (fun _ _ _ h => (VExpr.selfConst?_eq_some.1 h).1) hΓ r.1 H c' us hj

/-- The corrected E6a lemma (statement change, flagged): `RhsLowerStmt.lean:208-226` with
`gen := Pattern.gen`, `idx := p.genIdx`, `rank := RP.rank`, plus
* `hR` (P1): `R`'s sub-derivations interpret (`LE_Interp.const`'s 7th premise). Used only at
  fixed leaves that are not self occurrences; necessary (`LR.ToyB.noHR_false`, `Toy.lean`);
* `hrec` (P3): recursor-argument raw path shapes lie below their lowered entries;
* `hfield`: field entry types are interpreted only below `indTy` (no field in function position);
and the self conjunct changed (P2, forced: `LR.ToyA.pinnedH_false`): the entry is for the
`j`-th same-rank occurrence `(c', us)` of the RHS, `ls'.length = ci'.uvars` holds for every
entry, and the `R`-witness `me ≤ s` is given only when `s ≠ ⊥`. -/
theorem LR.rhs_lower' (RP : RankParams) {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name}
    {ls : List SLevel} {R : TShape → SExpr → Prop} (LIH : LR.LocalIH RP.rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e)
    {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} {mC : TShape}
    (hP : Params.Pat p r) (hMt : LE_Interp.Matches p c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1)
    (g : PatGen) (hg : Pattern.gen Params.env RP.rank Params.classify p r.1 = some g)
    {fields : List TShape} {ρ : Valuation} {m : Nat} (_hm : g.ctx.length = fields.length + m)
    (hfit : (Valuation.lowerCtx fields ρ m).Fits Γ₀ (g.ctx.map (SExpr.mkInst ls) ++ Γ₀))
    (hvar : ∀ path {n} {y b : WShape n}, y.T ≤ m2 path → y.HasType b →
      LE_Interp (Valuation.lowerCtx fields ρ m) b.T
        (SExpr.mkInst ls ((g.ctx.getD (p.genIdx path) (.sort .zero)).liftN (p.genIdx path + 1))) →
      y.T ≤ Valuation.lowerCtx fields ρ m (p.genIdx path))
    (hrec : ∀ path, fields.length ≤ p.genIdx path →
      m2 path ≤ Valuation.lowerCtx fields ρ m (p.genIdx path))
    (hfield : ∀ path, p.genIdx path < fields.length → ∀ a : TShape,
      LE_Interp (Valuation.lowerCtx fields ρ m) a
        (SExpr.mkInst ls ((g.ctx.getD (p.genIdx path) (.sort .zero)).liftN (p.genIdx path + 1))) →
      a ≤ (WShape.indTy (n := 0)).T) :
    ∃ selfs : List TShape, selfs.length = g.self.length ∧
      (∀ j s, selfs[j]? = some s → ∃ (c' : Name) (us : List VLevel) (ci' : VConstant),
        (r.1.selfOccs RP.rank (RP.rank c))[j]? = some (c', us) ∧
        RP.rank c' = RP.rank c ∧ Params.env.constants c' = some ci' ∧
        (us.map (SLevel.instV ls)).length = ci'.uvars ∧
        SExpr.mkInst ls (g.self.getD j (.sort .zero)) =
          SExpr.mkInst (us.map (SLevel.instV ls)) ci'.type ∧
        (∃ (k : Nat) (x b : WShape k), s = x.T ∧ x.HasType b ∧
          LE_Interp ρ₀ b.T (SExpr.mkInst (us.map (SLevel.instV ls)) ci'.type)) ∧
        LR.ConstGoal Γ₀ ρ₀ s c' (us.map (SLevel.instV ls)) ci' ∧
        (s = TShape.bot ∨ ∃ me, R me (.const c' (us.map (SLevel.instV ls))) ∧ me ≤ s)) ∧
      ∀ {n'} {y' a' : WShape n'}, y'.T ≤ mC → y'.HasType a' →
        LE_Interp (Valuation.lower selfs fields ρ m) a'.T
          (SExpr.mkInst ls (g.type.liftN g.self.length)) →
        LE_Interp (Valuation.lower selfs fields ρ m) y'.T (SExpr.mkInst ls g.rhsAbs) := by
  have hhead := hMt.head_eq
  subst hhead
  obtain ⟨ci, hci⟩ := Pattern.gen_head_const hg
  -- what a self entry carries; the typed bound and `ConstGoal` are conditional on the arity
  -- data, which `rhs_core` does not have but `LR.selfOcc_uvars` supplies at every occurrence
  let Ent : Name → List VLevel → TShape → Prop := fun c' us s =>
    s = TShape.bot ∨ ∃ me, R me (.const c' (us.map (SLevel.instV ls))) ∧ me ≤ s ∧
      ∀ ci', Params.env.constants c' = some ci' → (us.map (SLevel.instV ls)).length = ci'.uvars →
        (∃ (k : Nat) (x b : WShape k), s = x.T ∧ x.HasType b ∧
          LE_Interp ρ₀ b.T (SExpr.mkInst (us.map (SLevel.instV ls)) ci'.type)) ∧
        LR.ConstGoal Γ₀ ρ₀ s c' (us.map (SLevel.instV ls)) ci'
  -- self occurrences: `LIH` alone (no `hR`)
  have hEnt : ∀ e c' us m, VExpr.selfConst? RP.rank (RP.rank p.head) e = some (c', us) →
      R m (mkInst ls e) → ∃ s, m ≤ s ∧ Ent c' us s := by
    intro e c' us m hs hRm
    obtain ⟨rfl, hrk⟩ := VExpr.selfConst?_eq_some.1 hs
    simp only [mkInst] at hRm
    by_cases hci' : ∃ ci', Params.env.constants c' = some ci' ∧
        (us.map (SLevel.instV ls)).length = ci'.uvars
    · obtain ⟨ci', h1, h2⟩ := hci'
      rcases LIH _ _ hRm _ _ _ rfl hrk h1 h2 with ⟨n, hn⟩ | ⟨n, m', a', hle, hty, hA, H⟩
      · exact ⟨TShape.bot, hn ▸ TShape.bot_eqv.1, .inl rfl⟩
      · refine ⟨m'.T, hle, .inr ⟨m, hRm, hle, fun ci'' h1' _ => ?_⟩⟩
        cases h1.symm.trans h1'
        exact ⟨⟨n, m', a', rfl, hty, hA⟩, .inr ⟨n, m', a', TShape.LE.rfl, hty, hA, H⟩⟩
    · exact ⟨m, TShape.LE.rfl, .inr ⟨m, hRm, TShape.LE.rfl, fun ci' h1 h2 => absurd ⟨ci', h1, h2⟩ hci'⟩⟩
  -- `hR` is used only here: fixed leaves that are not self occurrences
  obtain ⟨selfs, hlen, hent, hclaim⟩ := LR.rhs_core (Γ₀ := Γ₀)
    (Δ := (g.self ++ g.ctx).map (mkInst ls) ++ Γ₀) (ρ₀ := ρ₀)
    (VExpr.selfConst? RP.rank (RP.rank p.head)) p.genIdx g.self.length Ent
    (fun _ _ => .inl rfl) hEnt (fun _ _ _ h => hR _ _ h) hRHS 0
  have hgs := Pattern.gen_self hg
  have hlen' : selfs.length = g.self.length := hlen.trans hgs.1.symm
  have hentry : ∀ (j : Nat) s, selfs[j]? = some s → ∃ (c' : Name) (us : List VLevel) (ci' : VConstant),
      (r.1.selfOccs RP.rank (RP.rank p.head))[j]? = some (c', us) ∧
      RP.rank c' = RP.rank p.head ∧ Params.env.constants c' = some ci' ∧
      (us.map (SLevel.instV ls)).length = ci'.uvars ∧
      g.self[j]? = some (ci'.type.instL us) ∧
      (∃ (k : Nat) (x b : WShape k), s = x.T ∧ x.HasType b ∧
        LE_Interp ρ₀ b.T (SExpr.mkInst (us.map (SLevel.instV ls)) ci'.type)) ∧
      LR.ConstGoal Γ₀ ρ₀ s c' (us.map (SLevel.instV ls)) ci' ∧
      (s = TShape.bot ∨ ∃ me, R me (.const c' (us.map (SLevel.instV ls))) ∧ me ≤ s) := by
    intro j s hj
    have hj' : j < (r.1.selfOccs RP.rank (RP.rank p.head)).length :=
      hlen ▸ (List.getElem?_eq_some_iff.1 hj).1
    obtain ⟨⟨c', us⟩, hcu⟩ : ∃ x, (r.1.selfOccs RP.rank (RP.rank p.head))[j]? = some x :=
      ⟨_, List.getElem?_eq_getElem hj'⟩
    obtain ⟨ci', h1, h2, h3⟩ := hgs.2 j c' us hcu
    obtain ⟨ci'', h1', hl⟩ := LR.selfOcc_uvars RP hP hg hci (List.mem_of_getElem? hcu)
    cases h1.symm.trans h1'
    have hl' : (us.map (SLevel.instV ls)).length = ci'.uvars := by rw [List.length_map, hl]
    rcases hent j s c' us hj hcu with rfl | ⟨me, hRm, hle, F⟩
    · exact ⟨c', us, ci', hcu, h2, h1, hl', h3, ⟨0, .bot, .bot, rfl, .bot' (.bot' .sort), .bot⟩,
        .inl ⟨0, rfl⟩, .inl rfl⟩
    · obtain ⟨hty, hCG⟩ := F ci' h1 hl'
      exact ⟨c', us, ci', hcu, h2, h1, hl', h3, hty, hCG, .inr ⟨me, hRm, hle⟩⟩
  refine ⟨selfs, hlen', fun j s hj => ?_, ?_⟩
  · obtain ⟨c', us, ci', hcu, h2, h1, hl', h3, hty, hCG, hd⟩ := hentry j s hj
    refine ⟨c', us, ci', hcu, h2, h1, hl', ?_, hty, hCG, hd⟩
    rw [List.getD_eq_getElem?_getD, h3, Option.getD_some, mkInst_instL]
  · intro n' y' a' hy hya hA
    have W : Valuation.Fits Γ₀ ((g.self ++ g.ctx).map (mkInst ls) ++ Γ₀)
        (Valuation.lower selfs fields ρ m) := by
      rw [List.map_append, List.append_assoc]
      refine hfit.foldr_push selfs (g.self.map (mkInst ls)) (by simp [hlen']) fun i x A hx hA => ?_
      obtain ⟨c', us, ci', -, -, h1, -, h3, ⟨k, x', b, rfl, hxb, hb⟩, -, -⟩ := hentry i x hx
      rw [List.getElem?_map, h3] at hA; cases hA
      rw [mkInst_instL]
      have cl : (mkInst (us.map (SLevel.instV ls)) ci'.type).ClosedN :=
        (Params.henv.closedC h1).mkInstS
      obtain ⟨u, H⟩ := (EnvStrongR.of_params RP).const (us.map (SLevel.instV ls)) h1
      refine ⟨cl, fun h => InterpTyped.hsort
        (fun h => (LE_Interp.soundSE (Params.env.below_le ..) H .nil).2 h) h,
        b.T, (LE_Interp.closed_iff cl).1 hb, hxb.T⟩
    have hv : ∀ path, m2 path ≤ Valuation.lower selfs fields ρ m (g.self.length + p.genIdx path) ∨
        ((∀ L, Lookup ((g.self ++ g.ctx).map (mkInst ls) ++ Γ₀) (g.self.length + p.genIdx path) L →
            ∀ a, LE_Interp (Valuation.lower selfs fields ρ m) a L →
            a ≤ (WShape.indTy (n := 0)).T) ∧
         ∀ L, Lookup ((g.self ++ g.ctx).map (mkInst ls) ++ Γ₀) (g.self.length + p.genIdx path) L →
           ∀ {k} (y t : WShape k), y.T ≤ m2 path → y.HasType t →
           LE_Interp (Valuation.lower selfs fields ρ m) t.T L →
           y.T ≤ Valuation.lower selfs fields ρ m (g.self.length + p.genIdx path)) := by
      intro path
      have hlt := Pattern.gen_genIdx_lt' hg path
      have hρL : Valuation.lower selfs fields ρ m (g.self.length + p.genIdx path) =
          Valuation.lowerCtx fields ρ m (p.genIdx path) := by
        rw [← hlen']; exact Valuation.lower_add
      have hconv : ∀ L, Lookup ((g.self ++ g.ctx).map (mkInst ls) ++ Γ₀)
          (g.self.length + p.genIdx path) L → ∀ a,
          LE_Interp (Valuation.lower selfs fields ρ m) a L ↔
          LE_Interp (Valuation.lowerCtx fields ρ m) a
            (SExpr.mkInst ls ((g.ctx.getD (p.genIdx path) (.sort .zero)).liftN (p.genIdx path + 1))) := by
        intro L hL a
        rw [List.map_append] at hL
        have hL' := Lookup.mid (S := g.self.map (mkInst ls)) (C := g.ctx.map (mkInst ls))
          (i := p.genIdx path) (by simpa using hlt) (by simpa using hL)
        rw [hL']; simp only [List.getElem_map, List.length_map]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
          Option.getD_some, mkInst_liftN,
          show g.self.length + p.genIdx path + 1 = (p.genIdx path + 1) + selfs.length by omega,
          liftK_add]
        exact LE_Interp.foldr_push_liftK selfs
      rcases Nat.lt_or_ge (p.genIdx path) fields.length with h | h
      · exact .inr ⟨fun L hL a ha => hfield path h a ((hconv L hL a).1 ha),
          fun L hL k y t hy ht htL => hρL ▸ hvar path hy ht ((hconv L hL t.T).1 htL)⟩
      · exact .inl (hρL ▸ hrec path h)
    have hSS := (LE_Interp.strongSoundS <| IsDefEqStrong.mono (Params.env.below_le ..)
      (((EnvStrongR.of_params RP).pat_rhs ls hP hg hci).weak_append (Γ₀ := Γ₀))).left
    rw [(Pattern.gen_rhs_eq hg).2] at hSS ⊢
    refine (hclaim _ W (fun i s h => ?_) hv _ hSS).1 y' a' hy hya hA
    rw [Nat.zero_add, Valuation.lower_lt (List.getElem?_eq_some_iff.1 h).1]
    rw [List.getElem?_eq_some_iff] at h; obtain ⟨_, rfl⟩ := h; exact TShape.LE.rfl


/-! ## Suppliability of `hfield` (D4 step 1's `Const.indTy` leaf): an `indTy 0` constant is
interpreted only below `indTy`. -/

theorem TShape.indTy_le_indTy {a b : Nat} :
    (WShape.indTy (n := a)).T ≤ (WShape.indTy (n := b)).T := by
  rw [TShape.LE.def (m := max a b + 1) (Nat.succ_le_succ (Nat.le_max_left ..))
    (Nat.succ_le_succ (Nat.le_max_right ..)), WShape.lift_indTy, WShape.lift_indTy]
  exact WShape.LE.rfl

theorem LE_Interp.Const.indTy0_le {I : Name} {ls : List SLevel} {R : TShape → SExpr → Prop}
    (hI : Params.classify I = some (.indTy 0)) {n : Nat} {y : TShape}
    (H : LE_Interp.Const I ls R ([] : List (WShape n)) y) : y ≤ (WShape.indTy (n := 0)).T := by
  cases H with
  | bot => exact TShape.bot_le'
  | @lam f _ _ hRec hle =>
    by_cases hf : f.NonZero
    · obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf
      have := (hRec s t (WShapeFun.mem_val hxy)).compat_mismatch (rargs2 := []) (by simp)
        (.inr (.inl hI))
      cases hn <| WShape.LE.T_iff.1 <| this.trans TShape.bot_eqv.2
    · have := WShape.lam'_le_lam'.2 <| NonZero.not_iff.1 hf
      exact hle.trans <| (WShape.lam'_bot ▸ this).T.trans TShape.bot_le'
  | ctor h _ => cases hI.symm.trans h
  | indTy _ h => exact h.trans TShape.indTy_le_indTy
  | pat hP hM _ =>
    obtain ⟨_, h⟩ := hM.head_wf (Params.pat_wf hP)
    cases hI.symm.trans h

/-- The `Const.indTy` leaf: every interpretation of an `indTy 0` constant is below `indTy`. -/
theorem LE_Interp.indTy0_le {ρ : Valuation} {a : TShape} {I : Name} {ls : List SLevel}
    (hI : Params.classify I = some (.indTy 0)) (H : LE_Interp ρ a (.const I ls)) :
    a ≤ (WShape.indTy (n := 0)).T := by
  cases H with
  | bot => exact TShape.bot_le'
  | const _ _ h3 _ _ h6 _ => exact h3.trans (LE_Interp.Const.indTy0_le hI h6)

/-- `hfield` for a context entry that is an `indTy 0` constant (stage 1a field types). -/
theorem LR.hfield_of_indTy {ρL : Valuation} {ls : List SLevel} {X : VExpr} {I : Name}
    {us : List VLevel} (hX : X = .const I us) (hI : Params.classify I = some (.indTy 0)) (k : Nat)
    (a : TShape) (H : LE_Interp ρL a (SExpr.mkInst ls (X.liftN k))) :
    a ≤ (WShape.indTy (n := 0)).T := by
  subst hX; exact LE_Interp.indTy0_le hI H

theorem Valuation.ofRargs_lt {n : Nat} : ∀ (rargs : List (WShape n)) {i : Nat}
    (h : i < rargs.length), Valuation.ofRargs rargs i = rargs[i].T
  | _ :: _, 0, _ => rfl
  | _ :: l, _+1, h => Valuation.ofRargs_lt l (Nat.lt_of_succ_lt_succ h)

theorem Valuation.range_foldr_push : ∀ (m : Nat) (ρ : Valuation) {i : Nat}, i < m →
    ((List.range m).foldr (fun i (ρ' : Valuation) => ρ'.push (ρ (i + 1))) Valuation.nil) i = ρ (i + 1)
  | m+1, ρ, i, h => by
    rw [List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
    cases i with
    | zero => rfl
    | succ i =>
      exact Valuation.range_foldr_push m (fun k => ρ (k + 1)) (Nat.lt_of_succ_lt_succ h)

theorem LE_Interp.Matches.varN_spec {rec c : Name} : ∀ {k n : Nat} {rargs : List (WShape n)}
    {mf : (Pattern.varN (.const rec) k).Path → TShape},
    LE_Interp.Matches (.varN (.const rec) k) c rargs mf →
    rargs.length = k ∧ ∀ x, ∃ h : (Pattern.varN (.const rec) k).genIdx x < rargs.length,
      mf x = rargs[(Pattern.varN (.const rec) k).genIdx x].T
  | 0, _, _, _, H => by cases H; exact ⟨rfl, nofun⟩
  | k+1, _, _, _, H => by
    cases H with
    | var H' =>
      obtain ⟨h1, h2⟩ := varN_spec H'
      refine ⟨by simp [h1], fun x => ?_⟩
      cases x with
      | none => exact ⟨by simp [Pattern.varN, Pattern.genIdx], rfl⟩
      | some x =>
        obtain ⟨h3, h4⟩ := h2 x
        refine ⟨by simp only [Pattern.varN, Pattern.genIdx, List.length_cons]; omega, ?_⟩
        simpa [Pattern.varN, Pattern.genIdx] using h4

/-- Suppliability of `hrec` at the pat leaf (iota pattern, `fields.length = n`): the raw
recursor-argument shapes lie below `ρ (i+1)`, by the spine lemma's `hρ`. -/
theorem LR.hrec_of_spine {rec c' : Name} {m' n' : Nat} {n : Nat} {rargs : List (WShape n)}
    {m2 : (Pattern.app (.varN (.const rec) m') (.varN (.const c') n')).Path → TShape}
    {fields : List TShape} {ρ : Valuation} {m : Nat}
    (hMt : LE_Interp.Matches (.app (.varN (.const rec) m') (.varN (.const c') n')) rec rargs m2)
    (hρ : (Valuation.ofRargs rargs).LE ρ) (hf : fields.length = n') (hmm : m' ≤ m) :
    ∀ path, fields.length ≤ (Pattern.app (.varN (.const rec) m') (.varN (.const c') n')).genIdx path →
      m2 path ≤ Valuation.lowerCtx fields ρ m
        ((Pattern.app (.varN (.const rec) m') (.varN (.const c') n')).genIdx path) := by
  cases hMt with
  | app hF hA =>
    rename_i n₀ rargs_f c₀ rargs' mf ma
    intro path hle
    cases path with
    | inr y =>
      have := Pattern.genIdx_varN_lt y
      simp only [Pattern.genIdx] at hle; omega
    | inl x =>
      obtain ⟨hl, hx⟩ := hF.varN_spec
      obtain ⟨hi, hmf⟩ := hx x
      simp only [Pattern.genIdx, Pattern.varDepth_varN, Sum.elim_inl, hmf]
      have h1 := hρ (Pattern.genIdx _ x + 1)
      rw [show Valuation.ofRargs (WShape.ctor' c₀ rargs'.reverse :: rargs_f) (Pattern.genIdx _ x + 1)
        = Valuation.ofRargs rargs_f (Pattern.genIdx _ x) from rfl, Valuation.ofRargs_lt _ hi] at h1
      rw [← hf, Valuation.lowerCtx, Valuation.foldr_push_add,
        Valuation.range_foldr_push m ρ (by omega)]
      exact h1


/-- Suppliability of `hfield` at the pat leaf (iota pattern, `fields.length = n`): the field
entries of `g.ctx` are stage-1a `indTy 0` constants (`gen_head` + `ctor_fields_closed`), whose
interpretations lie below `indTy` (`LE_Interp.indTy0_le`). -/
theorem LR.gen_field_const (RP : RankParams) {rec c' : Name} {m' n' : Nat}
    {r : (Pattern.app (.varN (.const rec) m') (.varN (.const c') n')).RHS} {g : PatGen}
    (hg : Pattern.gen Params.env RP.rank Params.classify
      (.app (.varN (.const rec) m') (.varN (.const c') n')) r = some g) :
    ∀ i < n', ∃ I us, g.ctx[i]? = some (.const I us) ∧ Params.classify I = some (.indTy 0) := by
  obtain ⟨ci, -, -, -, -, -, -, -, h1, -⟩ := Pattern.gen_iota hg
  obtain ⟨Hs, I, us, Bmaj, hHs, hT, hcl, ci', I', Ts, args, hci', hTs, hI', hty, hctx⟩ :=
    Pattern.gen_head hg h1
  obtain ⟨I0, Ts', hty', hTs'⟩ := RP.ctor_fields_closed (cl := .ctor n') rfl hcl hci'
  have hTT : Ts = Ts' :=
    VExpr.foldr_forallE_max (VExpr.foldr_app_ne_forallE args) (fun _ _ h => by cases h)
      (hty.symm.trans hty')
  subst hTT
  intro i hi
  have hi' : i < (Ts.map (·.instL us)).reverse.length := by simpa [hTs] using hi
  rw [hctx, List.getElem?_append_left hi', List.getElem?_eq_getElem hi', List.getElem_reverse,
    List.getElem_map]
  obtain ⟨I'', us'', he, hc⟩ := hTs' _ (List.getElem_mem ..)
  rw [he]
  exact ⟨I'', _, rfl, hc⟩

theorem LR.hfield_of_gen (RP : RankParams) {rec c' : Name} {m' n' : Nat}
    {r : (Pattern.app (.varN (.const rec) m') (.varN (.const c') n')).RHS} {g : PatGen}
    (hg : Pattern.gen Params.env RP.rank Params.classify
      (.app (.varN (.const rec) m') (.varN (.const c') n')) r = some g)
    {fields : List TShape} (hf : fields.length = n') {ρL : Valuation} {ls : List SLevel} :
    ∀ path, (Pattern.app (.varN (.const rec) m') (.varN (.const c') n')).genIdx path < fields.length →
      ∀ a : TShape, LE_Interp ρL a (SExpr.mkInst ls
        ((g.ctx.getD ((Pattern.app (.varN (.const rec) m') (.varN (.const c') n')).genIdx path)
          (.sort .zero)).liftN ((Pattern.app (.varN (.const rec) m') (.varN (.const c') n')).genIdx path + 1))) →
      a ≤ (WShape.indTy (n := 0)).T := by
  intro path hp a ha
  obtain ⟨I, us, h1, h2⟩ := LR.gen_field_const RP hg _ (hf ▸ hp)
  rw [List.getD_eq_getElem?_getD, h1, Option.getD_some] at ha
  exact LE_Interp.indTy0_le h2 ha

/-- `LR.rhs_lower'` with `hrec` and `hfield` discharged from what the pat leaf has (iota pattern,
`fields.length = n`, the spine lemma's `hρ`, `RP`): only `hR` remains as a new hypothesis. -/
theorem LR.rhs_lower_iota (RP : RankParams) {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name}
    {ls : List SLevel} {R : TShape → SExpr → Prop} (LIH : LR.LocalIH RP.rank Γ₀ ρ₀ c R)
    (hR : ∀ m e, R m e → LE_Interp ρ₀ m e) {rec c' : Name} {m' n' : Nat}
    {r : (Pattern.app (.varN (.const rec) m') (.varN (.const c') n')).RHS ×
      (Pattern.app (.varN (.const rec) m') (.varN (.const c') n')).Check}
    {n : Nat} {rargs : List (WShape n)}
    {m2 : (Pattern.app (.varN (.const rec) m') (.varN (.const c') n')).Path → TShape} {mC : TShape}
    (hP : Params.Pat _ r) (hMt : LE_Interp.Matches _ c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1)
    (g : PatGen) (hg : Pattern.gen Params.env RP.rank Params.classify _ r.1 = some g)
    {fields : List TShape} {ρ : Valuation} {m : Nat} (hm : g.ctx.length = fields.length + m)
    (hfit : (Valuation.lowerCtx fields ρ m).Fits Γ₀ (g.ctx.map (SExpr.mkInst ls) ++ Γ₀))
    (hvar : ∀ path {n} {y b : WShape n}, y.T ≤ m2 path → y.HasType b →
      LE_Interp (Valuation.lowerCtx fields ρ m) b.T
        (SExpr.mkInst ls ((g.ctx.getD (Pattern.genIdx _ path) (.sort .zero)).liftN
          (Pattern.genIdx _ path + 1))) →
      y.T ≤ Valuation.lowerCtx fields ρ m (Pattern.genIdx _ path))
    (hρ : (Valuation.ofRargs rargs).LE ρ) (hf : fields.length = n') :
    ∃ selfs : List TShape, selfs.length = g.self.length ∧
      (∀ j s, selfs[j]? = some s → ∃ (c'' : Name) (us : List VLevel) (ci' : VConstant),
        (r.1.selfOccs RP.rank (RP.rank c))[j]? = some (c'', us) ∧
        RP.rank c'' = RP.rank c ∧ Params.env.constants c'' = some ci' ∧
        (us.map (SLevel.instV ls)).length = ci'.uvars ∧
        SExpr.mkInst ls (g.self.getD j (.sort .zero)) =
          SExpr.mkInst (us.map (SLevel.instV ls)) ci'.type ∧
        (∃ (k : Nat) (x b : WShape k), s = x.T ∧ x.HasType b ∧
          LE_Interp ρ₀ b.T (SExpr.mkInst (us.map (SLevel.instV ls)) ci'.type)) ∧
        LR.ConstGoal Γ₀ ρ₀ s c'' (us.map (SLevel.instV ls)) ci' ∧
        (s = TShape.bot ∨ ∃ me, R me (.const c'' (us.map (SLevel.instV ls))) ∧ me ≤ s)) ∧
      ∀ {n'} {y' a' : WShape n'}, y'.T ≤ mC → y'.HasType a' →
        LE_Interp (Valuation.lower selfs fields ρ m) a'.T
          (SExpr.mkInst ls (g.type.liftN g.self.length)) →
        LE_Interp (Valuation.lower selfs fields ρ m) y'.T (SExpr.mkInst ls g.rhsAbs) := by
  have hc : rec = c := by
    have := hMt.head_eq; simpa [Pattern.head, Pattern.head_varN] using this
  subst hc
  have hmm : m' ≤ m := by have := Pattern.gen_ctx_iota hg; omega
  exact LR.rhs_lower' RP LIH hR hP hMt hRHS g hg hm hfit hvar
    (LR.hrec_of_spine hMt hρ hf hmm) (LR.hfield_of_gen RP hg hf)

/-! ## The pinned statement (`RhsLowerStmt.lean:208-226`, `gen := Pattern.gen`, `idx := p.genIdx`,
`rank := RP.rank`): reduced to `LR.rhs_lower'`; the residue is exactly what is missing or false.
`Toy.lean` refutes it in a concrete model (`LR.rhs_lower_unprovable`). -/

/-- E6a interface (PLAN D4 step 2), the statement pinned by `RhsLowerStmt.lean:208-226`. FALSE
in general (`LR.rhs_lower_unprovable`, `Toy.lean`): its self conjunct fails at self occurrences
inside a `⊥` subtree of `hRHS` (P2, `LR.ToyA.pinnedH_false`, even with `hR hrec hfield` added),
and its main conjunct fails without `hR` (P1, `LR.ToyB.pinned_false`, a rule with no self
occurrence). The body reduces it to `LR.rhs_lower'`; each `sorry` is one missing hypothesis or the
false conjunct. -/
theorem LR.rhs_lower (RP : RankParams) {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name}
    {ls : List SLevel} {R : TShape → SExpr → Prop} (LIH : LR.LocalIH RP.rank Γ₀ ρ₀ c R)
    {p : Pattern} {r : p.RHS × p.Check} {n : Nat} {rargs : List (WShape n)}
    {m2 : p.Path → TShape} {mC : TShape}
    (hP : Params.Pat p r) (hMt : LE_Interp.Matches p c rargs m2)
    (hRHS : LE_Interp.RHS ls m2 R mC r.1)
    (g : PatGen) (hg : Pattern.gen Params.env RP.rank Params.classify p r.1 = some g)
    {fields : List TShape} {ρ : Valuation} {m : Nat} (hm : g.ctx.length = fields.length + m)
    (hfit : (Valuation.lowerCtx fields ρ m).Fits Γ₀ (g.ctx.map (SExpr.mkInst ls) ++ Γ₀))
    (hvar : ∀ path {n} {y b : WShape n}, y.T ≤ m2 path → y.HasType b →
      LE_Interp (Valuation.lowerCtx fields ρ m) b.T
        (SExpr.mkInst ls ((g.ctx.getD (p.genIdx path) (.sort .zero)).liftN (p.genIdx path + 1))) →
      y.T ≤ Valuation.lowerCtx fields ρ m (p.genIdx path)) :
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
        LE_Interp (Valuation.lower selfs fields ρ m) y'.T (SExpr.mkInst ls g.rhsAbs) := by
  have hR : ∀ m e, R m e → LE_Interp ρ₀ m e := by
    sorry -- SORRY(E6a): missing hypothesis `hR : ∀ m e, R m e → LE_Interp ρ₀ m e` (P1), the 7th
          -- premise of the `LE_Interp.const` node (`h7` in `LR.const_local`, not passed on to
          -- `const_spine`/`pat_leaf_1a`). Needed only at fixed leaves that are NOT self
          -- occurrences: there `R mC e` is the only fact about `mC`, and `LIH` covers same-rank
          -- bare constants only. Formal: `LR.ToyB.pinned_false` (rule `d ⤳ I`, `I : Sort 1` an
          -- `indTy 0`, `R := {(forallE ⊥ ⊥, I)}`) and `LR.ToyB.noHR_false` (`rhs_lower'` minus `hR`).
  have hrec : ∀ path, fields.length ≤ p.genIdx path →
      m2 path ≤ Valuation.lowerCtx fields ρ m (p.genIdx path) := by
    sorry -- SORRY(E6a): missing hypothesis (P3): a recursor-argument path's RAW shape lies below
          -- its lowered entry. `hvar` bounds only TYPED shapes below `m2 path`, and a minor premise
          -- sits in function position, where `app_collapse` needs the raw function below a typed
          -- bound. Argued, not formalised (a model needs a constructor, hence `ctor_sort`): for
          -- `rec s (mk z) ⤳ s z`, raw `m2 s = lam {(⊥,⊥),(sort, ctor zero [])}` and raw field
          -- `m2 z = sort` give `mC = ctor zero []` while every typed shape below `m2 s` is `⊥`.
          -- The pat leaf has it: `LR.hrec_of_spine` (spine lemma's `hρ`, `fields.length = n`).
  have hfield : ∀ path, p.genIdx path < fields.length → ∀ a : TShape,
      LE_Interp (Valuation.lowerCtx fields ρ m) a
        (SExpr.mkInst ls ((g.ctx.getD (p.genIdx path) (.sort .zero)).liftN (p.genIdx path + 1))) →
      a ≤ (WShape.indTy (n := 0)).T := by
    sorry -- SORRY(E6a): missing hypothesis: an entry in the "field" block (`idx < fields.length`)
          -- has its type interpreted only below `indTy`. `hm` lets `fields` be all of `g.ctx`
          -- (`m = 0`), and then `hrec` is vacuous and P3 recurs at the minor premise. The pat leaf
          -- has it when `fields.length = n` (stage-1a field types are `indTy 0` constants:
          -- `LR.hfield_of_gen` via `RP.ctor_fields_closed`, `LE_Interp.indTy0_le`).
  obtain ⟨selfs, h1, h2, h3⟩ := LR.rhs_lower' RP LIH hR hP hMt hRHS g hg hm hfit hvar hrec hfield
  refine ⟨selfs, h1, fun j s hj => ?_, h3⟩
  obtain ⟨c', us, ci', -, h2', h1', hlen, heq, hty, hCG, hd⟩ := h2 j s hj
  rcases hd with rfl | ⟨me, hRm, hle⟩
  · sorry -- SORRY(E6a): FALSE as stated (P2). A self entry inside a `⊥` subtree of `hRHS`
          -- (`RHS.bot`, or an `R`-witness interpreted at `⊥`) has no `R me (.const c' ls')`
          -- witness. Formal: `LR.rhs_lower_forces_no_self` (the statement, even with `hR hrec
          -- hfield`, forces `g.self = []` for every rule) and `LR.ToyA.pinnedH_false` (a model
          -- whose rule `a ⤳ a` has one self occurrence). `LR.rhs_lower'` returns `s = ⊥` there,
          -- with the arity fact, which is all `W_p` needs (`LR.bot`, `⊥ : ⊥`).
  · exact ⟨me, c', _, ci', hRm, h2', h1', hlen, hle, heq, hty, hCG⟩

/-- The pinned statement as a `Prop` (binders exactly as `LR.rhs_lower`). -/
def LR.RhsLowerStmt (RP : RankParams) : Prop :=
  ∀ {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name}
    {ls : List SLevel} {R : TShape → SExpr → Prop} (_LIH : LR.LocalIH RP.rank Γ₀ ρ₀ c R)
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

/-- The pinned statement with `rhs_lower'`'s three extra hypotheses `hR hrec hfield` added and
the pinned conclusion kept: still false (`LR.ToyA.pinnedH_false`), so the self-conjunct change is
forced whatever hypotheses are added. -/
def LR.RhsLowerStmtH (RP : RankParams) : Prop :=
  ∀ {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name}
    {ls : List SLevel} {R : TShape → SExpr → Prop} (_LIH : LR.LocalIH RP.rank Γ₀ ρ₀ c R)
    (_hR : ∀ m e, R m e → LE_Interp ρ₀ m e)
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
      y.T ≤ Valuation.lowerCtx fields ρ m (p.genIdx path))
    (_hrec : ∀ path, fields.length ≤ p.genIdx path →
      m2 path ≤ Valuation.lowerCtx fields ρ m (p.genIdx path))
    (_hfield : ∀ path, p.genIdx path < fields.length → ∀ a : TShape,
      LE_Interp (Valuation.lowerCtx fields ρ m) a
        (SExpr.mkInst ls ((g.ctx.getD (p.genIdx path) (.sort .zero)).liftN (p.genIdx path + 1))) →
      a ≤ (WShape.indTy (n := 0)).T),
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

theorem LR.RhsLowerStmt.toH {RP : RankParams} (H : LR.RhsLowerStmt RP) : LR.RhsLowerStmtH RP :=
  by
  intro _ _ _ _ _ LIH _ _ _ _ _ _ _ hP hMt hRHS g hg _ _ _ hm hfit hvar _ _
  exact H LIH hP hMt hRHS g hg hm hfit hvar

/-- `rhs_lower'` without `hR` (otherwise verbatim): false (`LR.ToyB.noHR_false`), so `hR` is
necessary. -/
def LR.RhsLowerNoHR (RP : RankParams) : Prop :=
  ∀ {Γ₀ : List SExpr} {ρ₀ : Valuation} {c : Name}
    {ls : List SLevel} {R : TShape → SExpr → Prop} (_LIH : LR.LocalIH RP.rank Γ₀ ρ₀ c R)
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
      y.T ≤ Valuation.lowerCtx fields ρ m (p.genIdx path))
    (_hrec : ∀ path, fields.length ≤ p.genIdx path →
      m2 path ≤ Valuation.lowerCtx fields ρ m (p.genIdx path))
    (_hfield : ∀ path, p.genIdx path < fields.length → ∀ a : TShape,
      LE_Interp (Valuation.lowerCtx fields ρ m) a
        (SExpr.mkInst ls ((g.ctx.getD (p.genIdx path) (.sort .zero)).liftN (p.genIdx path + 1))) →
      a ≤ (WShape.indTy (n := 0)).T),
    ∃ selfs : List TShape, selfs.length = g.self.length ∧
      (∀ j s, selfs[j]? = some s → ∃ (c' : Name) (us : List VLevel) (ci' : VConstant),
        (r.1.selfOccs RP.rank (RP.rank c))[j]? = some (c', us) ∧
        RP.rank c' = RP.rank c ∧ Params.env.constants c' = some ci' ∧
        (us.map (SLevel.instV ls)).length = ci'.uvars ∧
        SExpr.mkInst ls (g.self.getD j (.sort .zero)) =
          SExpr.mkInst (us.map (SLevel.instV ls)) ci'.type ∧
        (∃ (k : Nat) (x b : WShape k), s = x.T ∧ x.HasType b ∧
          LE_Interp ρ₀ b.T (SExpr.mkInst (us.map (SLevel.instV ls)) ci'.type)) ∧
        LR.ConstGoal Γ₀ ρ₀ s c' (us.map (SLevel.instV ls)) ci' ∧
        (s = TShape.bot ∨ ∃ me, R me (.const c' (us.map (SLevel.instV ls))) ∧ me ≤ s)) ∧
      ∀ {n'} {y' a' : WShape n'}, y'.T ≤ mC → y'.HasType a' →
        LE_Interp (Valuation.lower selfs fields ρ m) a'.T
          (SExpr.mkInst ls (g.type.liftN g.self.length)) →
        LE_Interp (Valuation.lower selfs fields ρ m) y'.T (SExpr.mkInst ls g.rhsAbs)

/-! ### P2 with every side condition discharged -/

/-- All-`⊥` arguments match `varN (const c) k`, with all-`⊥` path shapes. -/
theorem LE_Interp.Matches.varN_bot (c : Name) {n : Nat} : ∀ k : Nat,
    ∃ mf : (Pattern.varN (.const c) k).Path → TShape,
      LE_Interp.Matches (n := n) (.varN (.const c) k) c (List.replicate k WShape.bot) mf ∧
      ∀ x, mf x ≤ TShape.bot
  | 0 => ⟨nofun, .const, nofun⟩
  | k+1 => by
    obtain ⟨mf, h, hb⟩ := LE_Interp.Matches.varN_bot c (n := n) k
    refine ⟨_, .var (a := WShape.bot) h, ?_⟩
    intro x; cases x with
    | none => exact TShape.bot_eqv.1
    | some x => exact hb x

theorem Valuation.nil_push_bot : Valuation.nil.push TShape.bot = Valuation.nil := by
  funext i; cases i <;> rfl

theorem Valuation.lowerCtx_replicate_bot (k m : Nat) :
    Valuation.lowerCtx (List.replicate k TShape.bot) Valuation.nil m = Valuation.nil := by
  unfold Valuation.lowerCtx
  have h2 : ∀ m, (List.range m).foldr (fun i (ρ' : Valuation) => ρ'.push (Valuation.nil (i + 1)))
      Valuation.nil = Valuation.nil := by
    intro m; induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.foldr_append]; simp only [List.foldr_cons, List.foldr_nil]
      have : Valuation.nil.push (Valuation.nil (m + 1)) = Valuation.nil := Valuation.nil_push_bot
      rw [this, ih]
  rw [h2]
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.foldr_cons, ih]; exact Valuation.nil_push_bot

/-- The all-`⊥` valuation fits any closed context strongly typed entry by entry. -/
theorem Valuation.Fits.nil_of_strong (E : VEnv) (hE : E ≤ Params.env) (ls : List SLevel) :
    ∀ L : List VExpr,
    (∀ (Δ : List VExpr) A Γ, L = Δ ++ A :: Γ →
      ∃ u, IsDefEqStrong E (Γ.map (mkInst ls)) (mkInst ls A) (mkInst ls A) (.sort u)) →
    Valuation.Fits [] (L.map (mkInst ls)) Valuation.nil
  | [], _ => .nil
  | A :: L, h => by
    have W := Valuation.Fits.nil_of_strong E hE ls L fun Δ A' Γ e => h (A :: Δ) A' Γ (by rw [e]; rfl)
    obtain ⟨u, H⟩ := h [] A L rfl
    rw [← Valuation.nil_push_bot]
    exact .cons W (fun h => InterpTyped.hsort (fun h => (LE_Interp.soundSE hE H W).2 h) h) .bot
      (WShape.HasType.T_iff.2 <| .bot' <| .bot' .sort)

/-- P2, all side conditions discharged: the pinned conclusion, even under `hR hrec hfield`,
forces EVERY rule to have no self occurrence (instance: `Γ₀ = []`, `ρ₀ = ρ = .nil`, `ls = []`,
`R := ∅` so `LIH`/`hR` are vacuous, `hRHS := RHS.bot`, all-`⊥` raw shapes and lowered entries,
`fields.length = n`). `LR.ToyA.pinnedH_false` is a model with a self occurrence. -/
theorem LR.rhs_lower_forces_no_self (RP : RankParams) (H : LR.RhsLowerStmtH RP) {p : Pattern}
    {r : p.RHS × p.Check} (hP : Params.Pat p r) {g : PatGen}
    (hg : Pattern.gen Params.env RP.rank Params.classify p r.1 = some g) : g.self = [] := by
  obtain ⟨ci, hci⟩ := Pattern.gen_head_const hg
  have hfitL : Valuation.Fits [] (g.ctx.map (mkInst [])) Valuation.nil :=
    Valuation.Fits.nil_of_strong _ (Params.env.below_le ..) [] g.ctx fun Δ A Γ e =>
      (EnvStrongR.of_params RP).pat_ctx [] hP hg hci (Δ := g.self ++ Δ) (by rw [e, List.append_assoc])
  have key : ∀ {c : Name} {n : Nat} {rargs : List (WShape n)} {m2 : p.Path → TShape},
      LE_Interp.Matches p c rargs m2 → (∀ x, m2 x ≤ TShape.bot) →
      ∀ {fields : List TShape} {m : Nat}, g.ctx.length = fields.length + m →
      Valuation.lowerCtx fields Valuation.nil m = Valuation.nil →
      (∀ path, p.genIdx path < fields.length → ∀ a : TShape,
        LE_Interp Valuation.nil a
          (SExpr.mkInst [] ((g.ctx.getD (p.genIdx path) (.sort .zero)).liftN (p.genIdx path + 1))) →
        a ≤ (WShape.indTy (n := 0)).T) → g.self = [] := by
    intro c n rargs m2 hMt hb fields m hm hnil hfield
    have hfit : (Valuation.lowerCtx fields Valuation.nil m).Fits []
        (g.ctx.map (SExpr.mkInst []) ++ []) := by
      rw [hnil, List.append_nil]; exact hfitL
    obtain ⟨selfs, hl, hs, -⟩ := H (Γ₀ := []) (ρ₀ := .nil) (ls := []) (R := fun _ _ => False)
      (fun _ _ h => h.elim) (fun _ _ h => h.elim) hP hMt
      (LE_Interp.RHS.bot : LE_Interp.RHS [] m2 (fun _ _ => False) (WShape.bot (n := 0)).T r.1)
      g hg hm hfit (fun path _ _ _ hy _ _ => (hy.trans (hb path)).trans TShape.bot_le)
      (fun path _ => (hb path).trans TShape.bot_le) (fun path h a ha => hfield path h a (hnil ▸ ha))
    cases hgs : g.self with
    | nil => rfl
    | cons A As =>
      have : 0 < selfs.length := by rw [hl, hgs]; exact Nat.succ_pos _
      obtain ⟨_, _, _, _, h, -⟩ := hs 0 _ (List.getElem?_eq_getElem this)
      exact h.elim
  rcases Pattern.gen_shape hg with ⟨c, rfl⟩ | ⟨rec, m', c', n', rfl⟩
  · obtain ⟨_, -, hctx, -⟩ := Pattern.gen_delta hg
    exact key (n := 0) .const nofun (fields := []) (m := 0) (by simp [hctx]) rfl nofun
  · obtain ⟨mf, hf, hbf⟩ := LE_Interp.Matches.varN_bot rec (n := 1) m'
    obtain ⟨ma, ha, hba⟩ := LE_Interp.Matches.varN_bot c' (n := 0) n'
    exact key (.app hf ha) (fun x => by cases x <;> simp [hbf, hba])
      (fields := List.replicate n' TShape.bot) (m := m')
      (by rw [Pattern.gen_ctx_iota hg, List.length_replicate])
      (Valuation.lowerCtx_replicate_bot n' m')
      (LR.hfield_of_gen RP hg (List.length_replicate ..))

/-- P2 for the pinned statement itself. -/
theorem LR.rhs_lower_forces_no_self' (RP : RankParams) (H : LR.RhsLowerStmt RP) {p : Pattern}
    {r : p.RHS × p.Check} (hP : Params.Pat p r) {g : PatGen}
    (hg : Pattern.gen Params.env RP.rank Params.classify p r.1 = some g) : g.self = [] :=
  LR.rhs_lower_forces_no_self RP H.toH hP hg

/-! ## Suppliability of `hR`: R9's amended statement, and `const_local` re-proved against it

`hR` is `h7` of the `LE_Interp.const` node in `LR.const_local`; E3's `const_spine` (R9) and
`pat_leaf_1a` (R10) do not take it, and under P1 they are false as stated (same junk `R` as
`LR.ToyB.pinned_false`). `LR.ConstSpineR` is `LR.const_spine`'s statement with `hR` added
after `LIH` (otherwise verbatim); `LR.const_local_of_spineR` is `LR.const_local` (same statement,
same proof) calling it with `h7`: no sorry. Inside the `Const` induction `R` and `ρ₀` do not
change, so `hR` reaches `Const.pat` and `pat_leaf_1a` unchanged. -/

/-- `LR.const_spine` (R9) with `hR` added: the amended R9 statement, as a `Prop`. -/
def LR.ConstSpineR (RP : RankParams) (Γ₀ : List SExpr) (k : Nat) : Prop :=
  ∀ {ρ₀ : Valuation} (_WFIH : LR.WFIH RP.rank Γ₀ k) {c : Name} {ci : VConstant} {ls : List SLevel}
    (_hc : RP.rank c < k) (_h1 : Params.env.constants c = some ci) (_h2 : ls.length = ci.uvars)
    {R : TShape → SExpr → Prop} (_LIH : LR.LocalIH RP.rank Γ₀ ρ₀ c R)
    (_hR : ∀ m e, R m e → LE_Interp ρ₀ m e)
    {n : Nat} {rargs : List (WShape n)} {mC : TShape} (_hC : LE_Interp.Const c ls R rargs mC)
    {Ts : List SExpr} {B : SExpr} (_hT : mkInst ls ci.type = Ts.foldr .forallE B)
    (_hk : rargs.length = Ts.length)
    {ρ : Valuation} {σ σ' : Subst} (_hρ : (Valuation.ofRargs rargs).LE ρ)
    (_W : LR.SubstWF Γ₀ σ σ' (Ts.reverse ++ Γ₀) ρ)
    {n'} {m a : WShape n'} (_le : m.T ≤ mC) (_hA : LE_Interp ρ a.T B) (_hmem : m.HasType a)
    (_tyV : ∀ {τ τ'}, LR.SubstWF Γ₀ τ τ' (Ts.reverse ++ Γ₀) ρ →
      (LR Γ₀).TyDefEq (B.subst τ) (B.subst τ') a),
    (LR Γ₀).DefEq ((openSpine c ls Ts.length).subst σ) ((openSpine c ls Ts.length).subst σ')
      (B.subst σ) m a

/-- `LR.const_local` from the amended R9 (`LR.ConstSpineR`), passing `h7` as `hR`. -/
theorem LR.const_local_of_spineR (RP : RankParams) {Γ₀ : List SExpr} {k : Nat} {c₀ : Name}
    (S : LR.ConstSpineR RP Γ₀ k)
    (WFIH : LR.WFIH RP.rank Γ₀ k) (hΓ₀ : ⊢ Γ₀) (hc₀ : RP.rank c₀ < k) :
    ∀ {ρ mT M} (_hM : LE_Interp ρ mT M) {c ls ci}, M = .const c ls → RP.rank c ≤ RP.rank c₀ →
      Params.env.constants c = some ci → ls.length = ci.uvars →
      LR.ConstGoal Γ₀ ρ mT c ls ci := by
  intro ρ mT M hM
  induction hM with
  | bot => intro c ls ci _ _ _ _; exact .inl ⟨_, rfl⟩
  | @const _ c ci _ m' ρ aT ls R h1 h2 h3 h4 h5 h6 h7 _ ih7 =>
    intro c₁ ls₁ ci₁ eM hrk h1' hlen
    cases eM; cases h1.symm.trans h1'
    have hc : RP.rank c < k := Nat.lt_of_le_of_lt hrk hc₀
    have LIH : LR.LocalIH RP.rank Γ₀ ρ c R := fun m e hR c' ls' ci' he hr h1'' h2'' =>
      ih7 m e hR he (Nat.le_trans (Nat.le_of_eq hr) hrk) h1'' h2''
    have hK := Nat.max_le.1 (Nat.le_refl (max m'.1 aT.1))
    refine .inr ⟨_, m'.2.lift _, aT.2.lift _, h3.trans (TShape.lift_eqv hK.1).2,
      (TShape.HasType.def hK.1 hK.2).1 h4, h5.mono (TShape.lift_eqv hK.2).1, ?_⟩
    intro n' m₁ a₁ hle hA hmem
    have hcl := (Params.henv.closedC h1).mkInstS (ls := ls)
    have hA₀ : LE_Interp .nil a₁.T (mkInst ls ci.type) := (LE_Interp.closed_iff hcl).1 hA
    have tyV := LR.constType_valid RP WFIH hΓ₀ hc h1 hA hmem.isType
    have := S WFIH hc h1 hlen LIH h7 h6 (Ts := []) (B := mkInst ls ci.type) rfl rfl
      (ρ := .nil) Valuation.LE.rfl (LR.SubstWF.id hΓ₀) (hle.trans (TShape.lift_eqv hK.1).1) hA₀
      hmem (fun _ => by rw [hcl.subst_eq .zero, hcl.subst_eq .zero]; exact tyV)
    simpa [openSpine] using this
  | _ => intro c ls ci eM; cases eM

end SExpr
end Lean4Lean
