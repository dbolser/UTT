import Lean4Lean.Experimental.SExpr

/-! # `Pattern.gen`: the `SExpr` forms of the spec lemmas

The spec lemmas of `Pattern.gen` (docs/const-case/PLAN.md D4, item R5) that need `SExpr`
(`mkInst`, `spine`, `subst`) or a `Params` field: (b) `gen_lhs_subst`/`gen_lhs_openSpine`,
(c) `RHS.toVExpr_subst`/`gen_rhsAbs`, (f) `gen_rhs`, (g) `gen_self_mkInst`, (e) `gen_arity_mkInst`
and, through `pat_gen`, `Params.pat_arity`, (a) with `ctor_syn` `gen_head_ctor`. `Pattern.gen`
itself and the `Params`-free lemmas are in `SExpr.lean`, before `class Params`. -/

namespace Lean4Lean

namespace SExpr
variable [Params]

/-- `SelfType.lean` (docs/const-case/plan/historical/, not in the build). -/
theorem _root_.Lean4Lean.SLevel.instV_inst {ls : List SLevel} {us : List VLevel} {l : VLevel} :
    SLevel.instV ls (l.inst us) = SLevel.instV (us.map (SLevel.instV ls)) l := by
  apply Subtype.ext; funext v
  simp only [SLevel.instV, VLevel.eval_inst, List.map_map, Function.comp_def]

/-- `SelfType.lean: mkInst_instL`. -/
theorem mkInst_instL {ls : List SLevel} {us : List VLevel} :
    ∀ {e : VExpr}, mkInst ls (e.instL us) = mkInst (us.map (SLevel.instV ls)) e
  | .bvar _ => rfl
  | .sort u => by simp only [VExpr.instL, mkInst, SLevel.instV_inst]
  | .const c vs => by
    simp only [VExpr.instL, mkInst, List.map_map, Function.comp_def, SLevel.instV_inst]
  | .app f a | .lam f a | .forallE f a => by
    simp only [VExpr.instL, mkInst, mkInst_instL (e := f), mkInst_instL (e := a)]

theorem _root_.Lean4Lean.SLevel.instV_params {ls : List SLevel} {n : Nat} (h : ls.length = n) :
    (VLevel.params n).map (SLevel.instV ls) = ls := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [VLevel.params, List.map_map, List.getElem_map, List.getElem_range, Function.comp]
  apply Subtype.ext; funext v
  simp [SLevel.instV, VLevel.eval, List.getD_eq_getElem?_getD, h2]

theorem mkInst_foldl_app (ls : List SLevel) : ∀ (Xs : List VExpr) (h : VExpr),
    mkInst ls (Xs.foldl .app h) = spine (mkInst ls h) (Xs.map (mkInst ls))
  | [], _ => rfl
  | X :: Xs, h => mkInst_foldl_app ls Xs (.app h X)

theorem spine_subst (σ : Subst) : ∀ (Xs : List SExpr) (h : SExpr),
    (spine h Xs).subst σ = spine (h.subst σ) (Xs.map (·.subst σ))
  | [], _ => rfl
  | X :: Xs, h => spine_subst σ Xs (.app h X)

theorem mkInst_foldr_forallE (ls : List SLevel) : ∀ (Hs : List VExpr) (B : VExpr),
    mkInst ls (Hs.foldr .forallE B) = (Hs.map (mkInst ls)).foldr .forallE (mkInst ls B)
  | [], _ => rfl
  | A :: Hs, B => by simp [mkInst, mkInst_foldr_forallE ls Hs B]

theorem mkInst_bvarSpine (ls : List SLevel) (h : VExpr) (k off : Nat) :
    mkInst ls (VExpr.bvarSpine h k off) =
      spine (mkInst ls h) ((List.range k).reverse.map fun i => .bvar (off + i)) := by
  unfold VExpr.bvarSpine; rw [mkInst_foldl_app]; simp [List.map_map, Function.comp_def, mkInst]

/-- `const c ls (bvar (k-1)) … (bvar 0)` (docs/const-case/CtorClause.lean:102). -/
def openSpine (c : Name) (ls : List SLevel) (k : Nat) : SExpr :=
  spine (.const c ls) ((List.range k).reverse.map .bvar)

theorem openSpine_subst (c : Name) (ls : List SLevel) (k : Nat) (σ : Subst) :
    (openSpine c ls k).subst σ = spine (.const c ls) ((List.range k).reverse.map σ) := by
  simp [openSpine, spine_subst, List.map_map, Function.comp_def, SExpr.subst]

/-- Spec lemma (b), `gen_lhs`, under a substitution: the `openSpine rec ls (m+1)` instance
with the major replaced by the ctor spine. -/
theorem _root_.Lean4Lean.Pattern.gen_lhs_subst {env : VEnv} {rank : Name → Nat}
    {classify : Name → Option Classification}
    {rec c' : Name} {m n : Nat} {r : (Pattern.iota rec m c' n).RHS} {g : PatGen} {ci : VConstant}
    {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr}
    (hg : Pattern.gen env rank classify (.iota rec m c' n) r = some g)
    (hci : env.constants rec = some ci) (hHs : Hs.length = m)
    (hT : ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj))
    {ls : List SLevel} (hls : ls.length = ci.uvars) (σ : Subst) :
    (mkInst ls g.lhs).subst σ =
      .app (spine (.const rec ls) ((List.range m).reverse.map fun i => σ (n + i)))
        (spine (.const c' (us.map (SLevel.instV ls))) ((List.range n).reverse.map σ)) := by
  rw [Pattern.gen_lhs hg hci hHs hT]
  simp only [mkInst, mkInst_bvarSpine, SExpr.subst, spine_subst, List.map_map, Function.comp_def,
    SLevel.instV_params hls, Nat.zero_add]

theorem _root_.Lean4Lean.Pattern.gen_lhs_openSpine {env : VEnv} {rank : Name → Nat}
    {classify : Name → Option Classification}
    {rec c' : Name} {m n : Nat} {r : (Pattern.iota rec m c' n).RHS} {g : PatGen} {ci : VConstant}
    {Hs : List VExpr} {I : Name} {us : List VLevel} {Bmaj : VExpr}
    (hg : Pattern.gen env rank classify (.iota rec m c' n) r = some g)
    (hci : env.constants rec = some ci) (hHs : Hs.length = m)
    (hT : ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj))
    {ls : List SLevel} (hls : ls.length = ci.uvars) (σ : Subst) :
    (mkInst ls g.lhs).subst σ =
      .app ((openSpine rec ls m).subst fun i => σ (n + i))
        ((openSpine c' (us.map (SLevel.instV ls)) n).subst σ) := by
  rw [Pattern.gen_lhs_subst hg hci hHs hT hls, openSpine_subst, openSpine_subst]

/-- The per-occurrence RHS instance as a substitution instance (generic form of (c)). -/
theorem _root_.Lean4Lean.Pattern.RHS.toVExpr_subst {p : Pattern} (sel : VExpr → Bool) (k : Nat)
    (ls : List SLevel) (m2 : p.Path → SExpr) (σ : Subst)
    (hidx : ∀ path, σ (k + p.pathIdx path) = m2 path) :
    ∀ (r : p.RHS) (j : Nat),
      (∀ (i : Nat) (e : VExpr), (r.selfLeaves sel)[i]? = some e → σ (j + i) = mkInst ls e) →
      (mkInst ls (r.toVExpr sel k j)).subst σ = r.applyS ls m2
  | .fixed e cl, j, hs => by
    simp only [Pattern.RHS.toVExpr, Pattern.RHS.applyS]
    split
    · next h =>
      have := hs 0 e (by simp [Pattern.RHS.selfLeaves, Pattern.RHS.fixedLeaves, h])
      simpa [mkInst, SExpr.subst] using this
    · exact cl.mkInstS.subst_eq .zero
  | .var path, _, _ => by
    simp only [Pattern.RHS.toVExpr, Pattern.RHS.applyS, mkInst, SExpr.subst, hidx]
  | .app f a, j, hs => by
    rw [Pattern.RHS.selfLeaves_app] at hs
    have hf := toVExpr_subst sel k ls m2 σ hidx f j fun i e he =>
      hs i e (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 he).1]; exact he)
    have ha := toVExpr_subst sel k ls m2 σ hidx a (j + (f.selfLeaves sel).length) fun i e he => by
      rw [Nat.add_assoc]
      exact hs _ e (by rw [List.getElem?_append_right (by omega)]; simpa using he)
    simp only [Pattern.RHS.toVExpr, Pattern.RHS.applyS, mkInst, SExpr.subst, hf, ha]

/-- Spec lemma (c), the per-occurrence `RHS.toVExpr_subst` at `Pattern.gen`'s `rhsAbs`:
`σ` sends the `j`-th same-rank bare leaf occurrence's self variable `bvar j` to that occurrence
(instantiated), and the pattern variable of `path` (`bvar (g.self.length + pathIdx path)`) to
`m2 path`. -/
theorem _root_.Lean4Lean.Pattern.gen_rhsAbs {env : VEnv} {rank : Name → Nat}
    {classify : Name → Option Classification} {p : Pattern} {r : p.RHS} {g : PatGen}
    (hg : Pattern.gen env rank classify p r = some g)
    (ls : List SLevel) (m2 : p.Path → SExpr) (σ : Subst)
    (hself : ∀ (j : Nat) (e : VExpr), (r.selfLeaves (Pattern.sameRank rank p.head))[j]? = some e →
      σ j = mkInst ls e)
    (hidx : ∀ path, σ (g.self.length + p.pathIdx path) = m2 path) :
    (mkInst ls g.rhsAbs).subst σ = r.applyS ls m2 := by
  rw [(Pattern.gen_eq_some hg).2.2.2]
  exact Pattern.RHS.toVExpr_subst _ _ ls m2 σ hidx r 0 fun i e he => by
    rw [Nat.zero_add]; exact hself i e he

/-- Spec lemma (f), `gen_rhs`: the unabstracted RHS under the pattern substitution. -/
theorem _root_.Lean4Lean.Pattern.gen_rhs {env : VEnv} {rank : Name → Nat}
    {classify : Name → Option Classification} {p : Pattern} {r : p.RHS} {g : PatGen}
    (hg : Pattern.gen env rank classify p r = some g)
    (ls : List SLevel) (m2 : p.Path → SExpr) (σ : Subst)
    (hidx : ∀ path, σ (p.pathIdx path) = m2 path) :
    (mkInst ls g.rhs).subst σ = r.applyS ls m2 := by
  rw [(Pattern.gen_eq_some hg).2.2.1]
  refine Pattern.RHS.toVExpr_subst _ 0 ls m2 σ (fun path => by rw [Nat.zero_add]; exact hidx path)
    r 0 fun i e he => ?_
  have : r.selfLeaves (fun _ => false) = [] := by
    rw [Pattern.RHS.selfLeaves, List.filter_eq_nil_iff]; simp
  simp [this] at he

/-- Spec lemma (g) at the `SExpr` level (`SelfType.lean: mkInst_instL`): the `j`-th self entry,
instantiated, is `ConstGoal`'s type at the occurrence `mkInst ls (.const c' us)`. -/
theorem _root_.Lean4Lean.Pattern.gen_self_mkInst {env : VEnv} {rank : Name → Nat}
    {classify : Name → Option Classification} {p : Pattern} {r : p.RHS} {g : PatGen}
    (hg : Pattern.gen env rank classify p r = some g) {j : Nat} {e : VExpr}
    (he : (r.selfLeaves (Pattern.sameRank rank p.head))[j]? = some e) (ls : List SLevel) :
    ∃ (c' : Name) (us : List VLevel) (ci' : VConstant) (T : VExpr), e = .const c' us ∧
      env.constants c' = some ci' ∧ rank c' = rank p.head ∧ g.self[j]? = some T ∧
      mkInst ls e = .const c' (us.map (SLevel.instV ls)) ∧
      mkInst ls T = mkInst (us.map (SLevel.instV ls)) ci'.type := by
  obtain ⟨c', us, ci', rfl, h1, h2, h3⟩ := (Pattern.gen_self hg).2 j e he
  exact ⟨c', us, ci', _, rfl, h1, h2, h3, rfl, mkInst_instL⟩

/-- Spec lemma (e) for the instantiated type. -/
theorem _root_.Lean4Lean.Pattern.gen_arity_mkInst {env : VEnv} {rank : Name → Nat}
    {classify : Name → Option Classification}
    {p : Pattern} {r : p.RHS} {g : PatGen} {ci : VConstant} {k : Nat}
    (hg : Pattern.gen env rank classify p r = some g) (hci : env.constants p.head = some ci)
    (hk : Arity (.const p.head) k p) (ls : List SLevel) :
    ∃ (Hs : List SExpr) (B : SExpr), Hs.length = k ∧ mkInst ls ci.type = Hs.foldr .forallE B := by
  obtain ⟨Hs, B, h1, h2⟩ := Pattern.gen_arity hg hci hk
  exact ⟨Hs.map (mkInst ls), mkInst ls B, by simp [h1], by rw [h2, mkInst_foldr_forallE]⟩

/-- Spec lemma (a) with `ctor_syn`: the field telescope `Fs` of `gen_head` is the constructor's
`ctor_syn` telescope at the major's levels `us`. -/
theorem _root_.Lean4Lean.Pattern.gen_head_ctor {rank : Name → Nat}
    {rec c' : Name} {m n : Nat} {r : (Pattern.iota rec m c' n).RHS} {g : PatGen} {ci : VConstant}
    (hg : Pattern.gen Params.env rank Params.classify (.iota rec m c' n) r = some g)
    (hci : Params.env.constants rec = some ci) :
    ∃ (Hs : List VExpr) (I : Name) (us : List VLevel) (Bmaj : VExpr),
      Hs.length = m ∧ ci.type = Hs.foldr .forallE (.forallE (.const I us) Bmaj) ∧
      ∃ (ci' : VConstant) (I' : Name) (Ts args : List VExpr),
        Params.env.constants c' = some ci' ∧ Params.classify c' = some (.ctor n) ∧
        Ts.length = n ∧ Params.classify I' = some (.indTy args.length) ∧
        ci'.type = Ts.foldr .forallE
          (args.foldr (fun A acc => acc.app A) (.const I' (VLevel.params ci'.uvars))) ∧
        g.ctx = (Ts.map (·.instL us)).reverse ++ Hs.reverse := by
  obtain ⟨Hs, I, us, Bmaj, l1, e1, ci', Fs, R', hcl, hci', l2, e2, hctx⟩ := Pattern.gen_head hg hci
  obtain ⟨I', Ts, args, hTs, hI', e3⟩ := Params.ctor_syn (cl := .ctor n) rfl hcl hci'
  rw [e3, VExpr.instL_foldr_forallE] at e2
  obtain ⟨rfl, -⟩ := VExpr.foldr_forallE_inj (by simp [l2]; exact hTs) e2
  exact ⟨Hs, I, us, Bmaj, l1, e1, ci', I', Ts, args, hci', hcl, hTs, hI', e3, hctx⟩

/-- Spec lemma (e) through `pat_gen`, for any `Pat` (iota or delta). -/
theorem _root_.Lean4Lean.Params.pat_arity {p : Pattern} {r : p.RHS × p.Check}
    {ci : VConstant} {k : Nat} (hP : Params.Pat p r) (hci : Params.env.constants p.head = some ci)
    (hk : Arity (.const p.head) k p) :
    ∃ (Hs : List VExpr) (B : VExpr), Hs.length = k ∧ ci.type = Hs.foldr .forallE B := by
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 (Params.pat_gen hP)
  exact Pattern.gen_arity hg hci hk

end SExpr
end Lean4Lean
