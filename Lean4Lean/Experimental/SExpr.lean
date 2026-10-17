import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Typing.Strong

namespace Lean4Lean
open Lean4Lean

inductive Classification where
  | ctor (arity : Nat)
  | etaCtor (params args : Nat)
  | symb (arity : Nat)
  | indTy (arity : Nat)

def Classification.arity : Classification → Nat
  | .ctor k | .symb k | .indTy k => k
  | .etaCtor p a => p + a

def Pattern.WF (cl : Name → Option Classification) :
    Pattern → (top : Bool := true) → (extra : Nat := 0) → Prop
  | .const c, top, n => cl c = some (if top then .symb n else .ctor n)
  | .var p, top, n => WF cl p top (n + 1)
  | .app p p', top, n => WF cl p top (n + 1) ∧ WF cl p' false

class Params where
  env : VEnv
  henv : env.Ordered
  univs : Nat
  Pat : (p : Pattern) → p.RHS × p.Check → Prop
  classify : Name → Option Classification
  pat_simple : Pat p r → ∃ sp : SimplePattern, p = sp.toPattern
  pat_wf : Pat p r → p.WF classify
  pat_uniq : Pat p₁ r → Pat p₂ r' → Subpattern p₃ p₁ → p₂.inter p₃ = some p₄ →
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r'
  -- pat_wf : Pat p r → p.Matches e m1 m2 → HasType env univs Γ e A →
  --   r.2.OK (IsDefEqU env univs Γ) m1 m2 → IsDefEqU env univs Γ e (r.1.apply m1 m2)
  -- pat_app_l : Pat p r → Subpattern (.app p₁ p₂) p → ¬Subpattern (.app p₃ p₄) p₁
  -- pat_app_l_uniq : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
  --   Subpattern (.app p₁' p₂') p' → Subpattern (.var p₃) p₁ → p₁'.inter p₃ = none
  -- pat_app_uniq : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
  --   Subpattern (.app p₁' p₂') p' → Subpattern p₃ p₁ → Subpattern p₃' p₂' → p₃.inter p₃' = none
  -- pat_app_r_arity : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
  --   Subpattern (.app p₁' p₂') p' → Arity (.const c) n p₂ → Arity (.const c) n' p₂' → n = n'
  /-- Every defeq rule of the environment, instantiated at well-formed levels, is an instance of
  some pattern `p` (with its side conditions holding) whose right-hand side is the rule's rhs.
  Stated on `VExpr`; the `SExpr` form is derived as `SExpr.Params.extra_pat`. -/
  extra_patV {df : VDefEq} {ls : List VLevel} {Γ : List VExpr} :
    env.defeqs df → (∀ l ∈ ls, l.WF univs) → ls.length = df.uvars →
    ∃ p r m1 m2, Pat p r ∧ p.Matches (df.lhs.instL ls) m1 m2 ∧
      r.2.OK (env.IsDefEqU univs Γ) m1 m2 ∧ df.rhs.instL ls = r.1.apply m1 m2
  /-- The type of a constructor (`classify c = ctor/etaCtor`) *is* syntactically a Π-telescope
  `Ts` over an application of the inductive type `I` (at the constant's own universe parameters)
  to `args`, with `Ts.length` the classified arity and `I` classified as an inductive type with
  `args.length` indices.  Lean's kernel guarantees this shape for every constructor it accepts.
  A merely *definitional* equation to such a telescope would not do: the strong judgment
  `IsDefEqStrong.const` needs the equation as a strong derivation, and translating a defeq
  derivation that lives in the full environment can require the strong typing of the very
  constant whose type is being described (`IsDefEq.strong` is then unprovable in general). -/
  ctor_syn {c : Name} {cl : Classification} {ci : VConstant} :
    (cl matches .ctor .. | .etaCtor ..) → classify c = some cl → env.constants c = some ci →
    ∃ (I : Name) (Ts args : List VExpr),
      Ts.length = cl.arity ∧ classify I = some (.indTy args.length) ∧
      ci.type = Ts.foldr .forallE
        (args.foldr (fun A acc => acc.app A) (.const I (VLevel.params ci.uvars)))
  /-- Every derivable sort of (an instance of) a constructor's type is non-zero under every
  universe assignment.  This is what makes the instantiated sort `SLevel.mk u ≠ .zero` demanded
  by `CtorBundle.hu0`; it excludes classifying constructors of universe-polymorphic inductives
  that can be instantiated to `Prop` (e.g. `PUnit.{u}`), which must stay unclassified.  It is
  stated for every derivable sort rather than one canonical sort because the strong `const`
  rule ties the bundle's sort to the sort of the derivation at hand, and sort uniqueness is not
  available at this point. -/
  ctor_sort {c : Name} {cl : Classification} {ci : VConstant} {U : Nat} {vs : List VLevel}
      {u : VLevel} :
    (cl matches .ctor .. | .etaCtor ..) → classify c = some cl → env.constants c = some ci →
    (∀ l ∈ vs, l.WF U) → vs.length = ci.uvars →
    env.HasType U [] (ci.type.instL vs) (.sort u) → ∀ ns, u.eval ns ≠ 0
open Params
variable [Params]

/-- The former `Params` field: a constructor's type is definitionally (indeed syntactically) a
Π-telescope over its inductive type, at a sort that is never zero. -/
theorem Params.ctor_tyV {c : Name} {cl : Classification} {ci : VConstant}
    (hctor : cl matches .ctor .. | .etaCtor ..) (hcl : classify c = some cl)
    (hci : env.constants c = some ci) :
    ∃ (I : Name) (Ts args : List VExpr) (u : VLevel),
      Ts.length = cl.arity ∧ classify I = some (.indTy args.length) ∧ (∀ ns, u.eval ns ≠ 0) ∧
      env.IsDefEq ci.uvars [] ci.type
        (Ts.foldr .forallE
          (args.foldr (fun A acc => acc.app A) (.const I (VLevel.params ci.uvars))))
        (.sort u) := by
  obtain ⟨I, Ts, args, hTs, hI, heq⟩ := ctor_syn hctor hcl hci
  have ⟨u, hu⟩ := henv.constWF hci
  have hwf : ci.type.LevelWF ci.uvars := (hu.levelWF ⟨⟩).1
  refine ⟨I, Ts, args, u, hTs, hI, ?_, heq ▸ hu⟩
  exact ctor_sort hctor hcl hci VLevel.params_wf VLevel.params_length (by rwa [hwf.instL_id])

/-- A semantically quotiented version of `VLevel`. This avoids the need for some congruences. -/
def SLevel := { f : List Nat → Nat // ∃ l : VLevel, l.WF univs ∧ l.eval = f }

namespace SLevel

def zero : SLevel := ⟨_, .zero, ⟨⟩, rfl⟩

def mk (l : VLevel) : SLevel := if h : l.WF univs then ⟨_, l, h, rfl⟩ else .zero

theorem mk_of_wf (h : l.WF univs) : mk l = (⟨_, l, h, rfl⟩ : SLevel) := by
  have hm : mk l = if h' : l.WF univs then
      (⟨_, l, h', rfl⟩ : SLevel) else SLevel.zero := rfl
  rw [hm]
  exact dif_pos h

theorem mk_eq (hl : l.WF univs) (hl' : l'.WF univs) (h : l ≈ l') : mk l = mk l' := by
  rw [mk_of_wf hl, mk_of_wf hl']
  apply Subtype.ext
  exact VLevel.equiv_def'.1 h

@[simp] theorem mk_zero : mk .zero = zero := by
  apply Subtype.ext
  rfl

theorem mk_val (h : l.WF univs) : (mk l).1 = l.eval := by rw [mk_of_wf h]

theorem mk_inj (hl : l.WF univs) (hl' : l'.WF univs) (h : mk l = mk l') : l ≈ l' :=
  VLevel.equiv_def'.2 (by rw [← mk_val hl, ← mk_val hl', h])

def succ (l : SLevel) : SLevel :=
  ⟨fun v => l.1 v + 1, let ⟨u, h1, h2⟩ := l.2; ⟨u.succ, h1, h2 ▸ rfl⟩⟩

def max (l₁ l₂ : SLevel) : SLevel :=
  ⟨fun v => (l₁.1 v).max (l₂.1 v),
    let ⟨u, h1, h2⟩ := l₁.2; let ⟨v, h3, h4⟩ := l₂.2; ⟨u.max v, ⟨h1, h3⟩, h2 ▸ h4 ▸ rfl⟩⟩

def imax (l₁ l₂ : SLevel) : SLevel :=
  ⟨fun v => Lean.Nat.imax (l₁.1 v) (l₂.1 v),
    let ⟨u, h1, h2⟩ := l₁.2; let ⟨v, h3, h4⟩ := l₂.2; ⟨u.imax v, ⟨h1, h3⟩, h2 ▸ h4 ▸ rfl⟩⟩

@[simp] theorem mk_succ (h : l.WF univs) : mk l.succ = succ (mk l) := by
  have hs : l.succ.WF univs := h
  rw [mk_of_wf hs, mk_of_wf h]; apply Subtype.ext; rfl

@[simp] theorem mk_max (h1 : l₁.WF univs) (h2 : l₂.WF univs) :
    mk (.max l₁ l₂) = max (mk l₁) (mk l₂) := by
  rw [mk_of_wf (l := l₁.max l₂) ⟨h1, h2⟩, mk_of_wf h1, mk_of_wf h2]
  apply Subtype.ext; rfl

@[simp] theorem mk_imax (h1 : l₁.WF univs) (h2 : l₂.WF univs) :
    mk (.imax l₁ l₂) = imax (mk l₁) (mk l₂) := by
  rw [mk_of_wf (l := l₁.imax l₂) ⟨h1, h2⟩, mk_of_wf h1, mk_of_wf h2]
  apply Subtype.ext; rfl

def inst (ls : List SLevel) (l : SLevel) : SLevel := by
  refine ⟨fun v => l.1 (ls.map (·.1 v)), ?_⟩
  simp [funext_iff]
  have ⟨ls', h3⟩ :
      ∃ ls' : List VLevel, ls'.Forall₂ (fun l' l => l'.WF univs ∧ l'.eval = l.1) ls := by
    induction ls with
    | nil => exact ⟨_, .nil⟩
    | cons a l ih =>
      let ⟨l', h1, h2⟩ := a.2; let ⟨ls', h3⟩ := ih
      exact ⟨l'::ls', .cons ⟨h1, h2⟩ h3⟩
  have ⟨l', h1, h2⟩ := l.2
  refine ⟨l'.inst ls', VLevel.WF.inst fun _ h => ?_, fun v => ?_⟩
  · let ⟨_, h⟩ := h3.forall_exists_l _ h; exact h.2.1
  · simp [VLevel.eval_inst, ← h2]; congr 1
    rw [← List.forall₂_eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact h3.imp fun _ _ h => congrFun h.2 _

/-- Instantiate a syntactic level directly into semantic levels. Unlike `inst ls (mk l)`,
this does not require `l` to be well-formed in the ambient universe context. -/
def instV (ls : List SLevel) (l : VLevel) : SLevel := by
  refine ⟨fun v => l.eval (ls.map (·.1 v)), ?_⟩
  have ⟨ls', h⟩ :
      ∃ ls' : List VLevel, ls'.Forall₂ (fun l' l => l'.WF univs ∧ l'.eval = l.1) ls := by
    induction ls with
    | nil => exact ⟨_, .nil⟩
    | cons a ls ih =>
      let ⟨l', h1, h2⟩ := a.2
      let ⟨ls', ih⟩ := ih
      exact ⟨l' :: ls', .cons ⟨h1, h2⟩ ih⟩
  refine ⟨l.inst ls', VLevel.WF.inst fun _ hl => ?_, ?_⟩
  · let ⟨_, hl⟩ := h.forall_exists_l _ hl; exact hl.2.1
  · funext v
    simp only [VLevel.eval_inst]
    congr 1
    rw [← List.forall₂_eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact h.imp fun _ _ hl => congrFun hl.2 _

theorem instV_map_mk (hls : ∀ u ∈ ls, u.WF univs) :
    instV (ls.map mk) l = mk (l.inst ls) := by
  apply Subtype.ext
  funext ns
  rw [congrFun (mk_val (VLevel.WF.inst hls)) ns]
  simp only [VLevel.eval_inst]
  change l.eval ((ls.map mk).map fun u => u.1 ns) = l.eval (ls.map (VLevel.eval ns))
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro u hu
  exact congrFun (mk_val (hls u hu)) ns

theorem mk_inst (hl : l.WF univs) (hls : ∀ u ∈ ls, u.WF univs) :
    mk (l.inst ls) = inst (ls.map mk) (mk l) := by
  apply Subtype.ext
  funext ns
  rw [congrFun (mk_val (VLevel.WF.inst hls)) ns]
  simp only [VLevel.eval_inst]
  change l.eval (ls.map (VLevel.eval ns)) = (mk l).1 ((ls.map mk).map fun u => u.1 ns)
  rw [congrFun (mk_val hl) _]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro u hu
  exact (congrFun (mk_val (hls u hu)) ns).symm

theorem map_mk_eq (hls : ∀ l ∈ ls, l.WF univs) (hls' : ∀ l ∈ ls', l.WF univs)
    (h : List.Forall₂ (fun l l' => l ≈ l') ls ls') :
    ls.map mk = ls'.map mk := by
  induction h with
  | nil => rfl
  | cons h _ ih =>
    simp only [List.map_cons]
    rw [mk_eq (hls _ (by simp)) (hls' _ (by simp)) h,
      ih (fun _ hu => hls _ (by simp [hu])) (fun _ hu => hls' _ (by simp [hu]))]

theorem map_mk_inj (hls : ∀ l ∈ ls, l.WF univs) (hls' : ∀ l ∈ ls', l.WF univs)
    (h : ls.map mk = ls'.map mk) : List.Forall₂ (· ≈ ·) ls ls' := by
  induction ls generalizing ls' with
  | nil => cases ls' with | nil => exact .nil | cons => cases h
  | cons l ls ih =>
    cases ls' with
    | nil => cases h
    | cons l' ls' =>
      simp only [List.map_cons, List.cons.injEq] at h
      exact .cons (mk_inj (hls _ (by simp)) (hls' _ (by simp)) h.1)
        (ih (fun _ hu => hls _ (by simp [hu])) (fun _ hu => hls' _ (by simp [hu])) h.2)

/-- Every semantic level is the image of a well-formed syntactic level. -/
theorem exists_mk (u : SLevel) : ∃ l : VLevel, l.WF univs ∧ mk l = u :=
  let ⟨l, h1, h2⟩ := u.2; ⟨l, h1, by rw [mk_of_wf h1]; exact Subtype.ext h2⟩

theorem exists_map_mk : ∀ ls : List SLevel,
    ∃ vs : List VLevel, (∀ l ∈ vs, l.WF univs) ∧ vs.map mk = ls
  | [] => ⟨[], nofun, rfl⟩
  | u :: ls =>
    let ⟨l, h1, h2⟩ := exists_mk u
    let ⟨vs, h3, h4⟩ := exists_map_mk ls
    ⟨l :: vs, List.forall_mem_cons.2 ⟨h1, h3⟩, by simp [h2, h4]⟩

end SLevel

inductive SExpr where
  | bvar (i : Nat)
  | sort (u : SLevel)
  | const (c : Name) (ls : List SLevel)
  | app (f a : SExpr)
  | lam (A e : SExpr)
  | forallE (A B : SExpr)

instance : Inhabited SExpr := ⟨.sort .zero⟩

namespace SExpr

@[simp] def lift' : SExpr → Lift → SExpr
  | .bvar i, k => .bvar (k.liftVar i)
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app fn arg, k => .app (fn.lift' k) (arg.lift' k)
  | .lam ty body, k => .lam (ty.lift' k) (body.lift' k.cons)
  | .forallE ty body, k => .forallE (ty.lift' k) (body.lift' k.cons)

abbrev lift e := lift' e (.skip .refl)

theorem lift'_comp {e : SExpr} : e.lift' (.comp l₁ l₂) = (e.lift' l₁).lift' l₂ := Eq.symm <| by
  induction e generalizing l₁ l₂ <;> simp [Lift.liftVar_comp, *]

theorem lift'_depth_zero {e : SExpr} (H : l.depth = 0) : e.lift' l = e := by
  induction e generalizing l <;> simp_all [Lift.liftVar_depth_zero]

@[simp] theorem lift'_refl {e : SExpr} : e.lift' .refl = e := lift'_depth_zero rfl

def ClosedN : SExpr → (k :_:= 0) → Prop
  | .bvar i, k => i < k
  | .sort .., _ | .const .., _ => True
  | .app fn arg, k => fn.ClosedN k ∧ arg.ClosedN k
  | .lam ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)
  | .forallE ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)

theorem ClosedN.mono (h : k ≤ k') (self : ClosedN e k) : ClosedN e k' := by
  induction e generalizing k k' with (simp [ClosedN] at self ⊢; try simp [self, *])
  | bvar i => exact Nat.lt_of_lt_of_le self h
  | app _ _ ih1 ih2 => exact ⟨ih1 h self.1, ih2 h self.2⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    exact ⟨ih1 h self.1, ih2 (Nat.succ_le_succ h) self.2⟩

theorem ClosedN.lift'_eq (self : ClosedN e k) (h : ρ.Fixes k) : lift' e ρ = e := by
  induction e generalizing k ρ with (simp [ClosedN] at self; simp [*])
  | bvar i => exact h.liftVar_eq self
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩

theorem ClosedN.lift_eq (self : ClosedN e) : lift e = e := self.lift'_eq ⟨⟩

variable (ls : List SLevel) in
def instL : SExpr → SExpr
  | .bvar i => .bvar i
  | .sort u => .sort (u.inst ls)
  | .const c us => .const c (us.map (SLevel.inst ls))
  | .app fn arg => .app fn.instL arg.instL
  | .lam ty body => .lam ty.instL body.instL
  | .forallE ty body => .forallE ty.instL body.instL

theorem ClosedN.instL : ∀ {e}, ClosedN e k → ClosedN (e.instL ls) k
  | .bvar .., h | .sort .., h | .const .., h => h
  | .app .., h | .lam .., h | .forallE .., h => ⟨h.1.instL, h.2.instL⟩

def mk : VExpr → SExpr
  | .bvar i => .bvar i
  | .sort u => .sort (.mk u)
  | .const c us => .const c (us.map .mk)
  | .app fn arg => .app (.mk fn) (.mk arg)
  | .lam ty body => .lam (.mk ty) (.mk body)
  | .forallE ty body => .forallE (.mk ty) (.mk body)

/-- Translate an expression while instantiating its universe parameters. -/
def mkInst (ls : List SLevel) : VExpr → SExpr
  | .bvar i => .bvar i
  | .sort u => .sort (.instV ls u)
  | .const c us => .const c (us.map (.instV ls))
  | .app fn arg => .app (mkInst ls fn) (mkInst ls arg)
  | .lam ty body => .lam (mkInst ls ty) (mkInst ls body)
  | .forallE ty body => .forallE (mkInst ls ty) (mkInst ls body)

@[simp] theorem mkInst_lift' : mkInst ls (e.lift' ρ) = (mkInst ls e).lift' ρ := by
  induction e generalizing ρ <;> simp [VExpr.lift', mkInst, *]

theorem _root_.Lean4Lean.VExpr.ClosedN.mkInstS : ∀ {e : VExpr},
    e.ClosedN k → (mkInst ls e).ClosedN k
  | .bvar .., h | .sort .., h | .const .., h => h
  | .app .., h | .lam .., h | .forallE .., h => ⟨h.1.mkInstS, h.2.mkInstS⟩

theorem mkInst_map_mk (hls : ∀ u ∈ ls, u.WF univs) :
    mkInst (ls.map SLevel.mk) e = mk (e.instL ls) := by
  induction e with
  | bvar => rfl
  | sort u => exact congrArg SExpr.sort (SLevel.instV_map_mk hls)
  | const c us =>
    simp only [mkInst, VExpr.instL, mk, List.map_map]
    congr 1
    apply List.map_congr_left
    intro u hu
    exact SLevel.instV_map_mk hls
  | app f a ihf iha | lam f a ihf iha | forallE f a ihf iha =>
    simp only [mkInst, VExpr.instL, mk]
    rw [ihf, iha]

@[simp] theorem mk_lift' : ∀ {e : VExpr}, mk (e.lift' ρ) = (mk e).lift' ρ
  | .bvar .. | .sort .. | .const .. => rfl
  | .app .. | .lam .. | .forallE .. => by simp [VExpr.lift', mk, mk_lift']

@[simp] theorem mk_lift {e : VExpr} : mk e.lift = (mk e).lift := by
  rw [VExpr.lift_eq_lift']
  exact mk_lift'

theorem mk_instL {e : VExpr} {ls : List VLevel}
    (he : e.LevelWF univs) (hls : ∀ u ∈ ls, u.WF univs) :
    mk (e.instL ls) = (mk e).instL (ls.map SLevel.mk) := by
  induction e with
  | bvar => rfl
  | app f a ihf iha | lam f a ihf iha | forallE f a ihf iha =>
    simp [VExpr.LevelWF] at he
    simp only [VExpr.instL, SExpr.mk, SExpr.instL]
    rw [ihf he.1, iha he.2]
  | sort u =>
    simp only [VExpr.instL, SExpr.mk, SExpr.instL]
    exact congrArg SExpr.sort (SLevel.mk_inst he hls)
  | const c us =>
    simp [VExpr.LevelWF] at he
    simp only [VExpr.instL, mk, instL, List.map_map]
    congr 1
    apply List.map_congr_left
    intro u hu
    exact SLevel.mk_inst (he u hu) hls

/-- Every `SExpr` is the image of a level-well-formed `VExpr`. -/
theorem exists_mk : ∀ e : SExpr, ∃ e' : VExpr, e'.LevelWF univs ∧ mk e' = e
  | .bvar i => ⟨.bvar i, ⟨⟩, rfl⟩
  | .sort u => let ⟨l, h1, h2⟩ := SLevel.exists_mk u; ⟨.sort l, h1, by simp [mk, h2]⟩
  | .const c ls =>
    let ⟨vs, h1, h2⟩ := SLevel.exists_map_mk ls; ⟨.const c vs, h1, by simp [mk, h2]⟩
  | .app f a =>
    let ⟨f', hf1, hf2⟩ := exists_mk f; let ⟨a', ha1, ha2⟩ := exists_mk a
    ⟨.app f' a', ⟨hf1, ha1⟩, by simp [mk, hf2, ha2]⟩
  | .lam A b =>
    let ⟨A', hA1, hA2⟩ := exists_mk A; let ⟨b', hb1, hb2⟩ := exists_mk b
    ⟨.lam A' b', ⟨hA1, hb1⟩, by simp [mk, hA2, hb2]⟩
  | .forallE A B =>
    let ⟨A', hA1, hA2⟩ := exists_mk A; let ⟨B', hB1, hB2⟩ := exists_mk B
    ⟨.forallE A' B', ⟨hA1, hB1⟩, by simp [mk, hA2, hB2]⟩

/-- Every `SExpr` context is the image of a level-well-formed `VExpr` context. -/
theorem exists_map_mk : ∀ Γ : List SExpr,
    ∃ Γ' : List VExpr, OnCtx Γ' (fun _ A => A.LevelWF univs) ∧ Γ'.map mk = Γ
  | [] => ⟨[], ⟨⟩, rfl⟩
  | A :: Γ =>
    let ⟨A', h1, h2⟩ := exists_mk A; let ⟨Γ', h3, h4⟩ := exists_map_mk Γ
    ⟨A' :: Γ', ⟨h3, h1⟩, by simp [h2, h4]⟩

theorem _root_.Lean4Lean.VExpr.ClosedN.mkS : ∀ {e : VExpr}, e.ClosedN k → ClosedN (.mk e) k
  | .bvar .., h | .sort .., h | .const .., h => h
  | .app .., h | .lam .., h | .forallE .., h => ⟨h.1.mkS, h.2.mkS⟩

@[reducible] def Subst := Nat → SExpr

def Subst.Depth (σ : Subst) (n n' : Nat) := ∀ i, σ (i + n') = .bvar (i + n)

def Subst.Fixes (σ : Subst) (n : Nat) := ∀ i < n, σ i = .bvar i

theorem Subst.Fixes.zero : Fixes σ 0 := nofun

theorem Subst.Depth.add {σ : Subst} (H : σ.Depth n n') : σ.Depth (n + k) (n' + k) :=
  fun i => cast (by congr 2 <;> omega) <| H (k + i)

def Subst.lift (σ : Subst) : Subst
  | 0 => .bvar 0
  | i+1 => (σ i).lift

theorem Subst.Depth.lift {σ : Subst} (H : σ.Depth n n') : σ.lift.Depth (n + 1) (n' + 1) :=
  fun i => by simp [Subst.lift, H i]; rfl

theorem Subst.Fixes.lift {σ : Subst} (H : σ.Fixes n) : σ.lift.Fixes (n + 1) := fun
  | 0, _ => rfl
  | n+1, h => by simp [Subst.lift, H _ (Nat.lt_of_succ_lt_succ h)]

def Subst.id : Subst := .bvar
def Subst.head (σ : Subst) : SExpr := σ 0
def Subst.tail (σ : Subst) : Subst := fun n => σ (n+1)

theorem Subst.Depth.id : Subst.id.Depth 0 0 := fun _ => rfl
theorem Subst.Depth.tail {σ : Subst} (H : σ.Depth n (n' + 1)) : σ.tail.Depth n n' := H

def Subst.cons (σ : Subst) (e : SExpr) : Subst
  | 0 => e
  | i+1 => σ i

theorem Subst.Depth.cons {σ : Subst} (H : σ.Depth n n') : (σ.cons e).Depth n (n' + 1) := H

abbrev Subst.one (e : SExpr) : Subst := .cons .id e

theorem Subst.Depth.one : (Subst.one e).Depth 0 1 := .id

def Subst.trunc (σ : Subst) (n n' : Nat) : Subst :=
  fun i => if n' ≤ i then .bvar (i - n' + n) else σ i

theorem Subst.Depth.trunc {σ : Subst} : (σ.trunc n n').Depth n n' := by
  intro i; simp [Subst.trunc]

def _root_.Lean4Lean.Lift.invS : Lift → Subst
  | .refl => .id
  | .skip ρ => ρ.invS.cons default
  | .cons ρ => ρ.invS.lift

theorem Subst.Depth.invS : ∀ (ρ : Lift), ρ.invS.Depth ρ.dom ρ.size
  | .refl => .id
  | .skip l => (invS l).cons
  | .cons l => (invS l).lift

@[simp] theorem Subst.head_cons : (cons σ e).head = e := rfl
@[simp] theorem Subst.tail_cons : (cons σ e).tail = σ := rfl

def Subst.lift_r (σ : Subst) (ρ : Lift) : Subst := fun x => (σ x).lift' ρ
def Subst.lift_l (ρ : Lift) (σ : Subst) : Subst := fun x => σ (ρ.liftVar x)

theorem Subst.tail_eq_lift_l {σ : Subst} : σ.tail = σ.lift_l Lift.refl.skip := rfl

theorem Subst.lift_l_lift {σ : Subst} {ρ} : (σ.lift_l ρ).lift = σ.lift.lift_l ρ.cons := by
  funext i; cases i <;> simp! [lift_l]

theorem Subst.lift_r_lift {σ : Subst} {ρ} : (σ.lift_r ρ).lift = σ.lift.lift_r ρ.cons := by
  funext i; cases i <;> simp! [lift_r, ← lift'_comp]

theorem lift_l_inv {ρ : Lift} : .lift_l ρ ρ.invS = Subst.id := by
  funext i; simp [Subst.lift_l, Subst.id]
  induction ρ generalizing i with
  | refl => rfl
  | skip ρ ih => simp [Lift.invS, Subst.cons, ih]
  | cons ρ ih => cases i <;> simp [Lift.invS, Subst.lift, ih]

@[simp] theorem instL_lift' : (lift' e ρ).instL ls = lift' (e.instL ls) ρ := by
  cases e <;> simp [lift', instL, instL_lift']

def _root_.Lean4Lean.Lift.toSubst (ρ : Lift) : Subst := .lift_l ρ .id

theorem _root_.Lean4Lean.Lift.toSubst_apply (ρ : Lift) (i) : ρ.toSubst i = bvar (ρ.liftVar i) := rfl

theorem Subst.Depth.toSubst (ρ : Lift) : ρ.toSubst.Depth ρ.size ρ.dom := by
  intro i; simp [Lift.toSubst_apply]
  induction ρ <;> simp! [*] <;> omega

def subst : SExpr → Subst → SExpr
  | .bvar i, σ => σ i
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app fn arg, σ => .app (fn.subst σ) (arg.subst σ)
  | .lam ty body, σ => .lam (ty.subst σ) (body.subst σ.lift)
  | .forallE ty body, σ => .forallE (ty.subst σ) (body.subst σ.lift)

def mkSubst (σ : VExpr.Subst) : Subst := fun i => mk (σ i)

@[simp] theorem mkSubst_lift : mkSubst σ.lift = (mkSubst σ).lift := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact mk_lift

@[simp] theorem mk_subst : mk (e.subst σ) = (mk e).subst (mkSubst σ) := by
  induction e generalizing σ with
  | bvar => rfl
  | sort | const => rfl
  | app f a ihf iha => simp only [VExpr.subst, mk, subst, ihf, iha]
  | lam A e ihA ihe | forallE A e ihA ihe =>
    simp only [VExpr.subst, mk, subst, ihA, ihe, mkSubst_lift]

@[simp] theorem id_lift : Subst.id.lift = Subst.id := by funext i; cases i <;> rfl

@[simp] theorem subst_id {e : SExpr} : e.subst .id = e := by
  induction e <;> simp! [*]; rfl

theorem subst_lift' {e : SExpr} : (e.lift' ρ).subst σ = subst e (.lift_l ρ σ) := by
  induction e generalizing ρ σ <;> simp! [*, Subst.lift_l_lift]; rfl

theorem lift'_subst {e : SExpr} : (e.subst σ).lift' ρ = subst e (.lift_r σ ρ) := by
  induction e generalizing ρ σ <;> simp! [*, Subst.lift_r, Subst.lift_r_lift]

theorem lift'_inj {e e' : SExpr} {ρ : Lift} : e.lift' ρ = e'.lift' ρ ↔ e = e' :=
  ⟨(by simpa [subst_lift', lift_l_inv] using congrArg (·.subst ρ.invS) ·), (· ▸ rfl)⟩

theorem subst_toSubst {e : SExpr} : subst e ρ.toSubst = lift' e ρ := by
  simp [Lift.toSubst, ← subst_lift']

theorem subst_lift'_inv {e : SExpr} {ρ : Lift} : (e.lift' ρ).subst ρ.invS = e := by
  rw [subst_lift', lift_l_inv, subst_id]

nonrec def Subst.instL (ls : List SLevel) (σ : Subst) : Subst := instL ls ∘ σ

theorem Subst.instL_lift {σ : Subst} : (σ.instL ls).lift = σ.lift.instL ls := by
  funext i; obtain _|i := i <;> simp [Subst.instL, lift, SExpr.instL]

@[simp] theorem instL_subst : (subst e σ).instL ls = subst (e.instL ls) (σ.instL ls) := by
  cases e <;> simp [subst, instL, instL_subst, Subst.instL_lift] <;> simp [Subst.instL]

def Subst.comp (σ σ' : Subst) : Subst := fun x => (σ x).subst σ'

theorem Subst.comp_lift {σ σ' : Subst} : (σ.comp σ').lift = σ.lift.comp σ'.lift := by
  funext i; cases i <;> simp! [comp, SExpr.lift]
  rw [SExpr.lift, SExpr.lift, lift'_subst, subst_lift']; rfl

theorem subst_subst {e : SExpr} : (e.subst σ).subst σ' = subst e (.comp σ σ') := by
  induction e generalizing σ σ' <;> simp! [*, Subst.comp, Subst.comp_lift]

theorem lift_subst {e : SExpr} : e.lift.subst σ = e.subst σ.tail := by
  rw [lift, subst_lift', ← Subst.tail_eq_lift_l]

theorem lift_subst_cons {e : SExpr} : e.lift.subst (σ.cons t) = e.subst σ := by
  rw [lift_subst, Subst.tail_cons]

theorem Subst.lift_l_eq : Subst.lift_l ρ σ = Subst.comp ρ.toSubst σ := by
  funext; simp [lift_l, comp, Lift.toSubst_apply, SExpr.subst]

theorem Subst.lift_r_eq : Subst.lift_r σ ρ = Subst.comp σ ρ.toSubst := by
  funext i; simp [lift_r, comp, subst_toSubst]

theorem Subst.Depth.comp {σ σ' : Subst}
    (H : σ.Depth n₁ n₂) (H2 : σ'.Depth n₂ n₃) : (σ'.comp σ).Depth n₁ n₃ := by
  intro i; simp [Subst.comp, subst, H2 i, H i]

theorem Subst.Depth.lift_l {σ : Subst}
    (H : σ.Depth n ρ.size) : (Subst.lift_l ρ σ).Depth n ρ.dom := by
  rw [lift_l_eq]; exact .comp H (.toSubst _)

theorem Subst.Depth.lift_r {σ : Subst}
    (H : σ.Depth ρ.dom n) : (Subst.lift_r σ ρ).Depth ρ.size n := by
  rw [lift_r_eq]; exact .comp (.toSubst _) H

theorem ClosedN.subst_eq {e : SExpr} (self : ClosedN e k) (h : σ.Fixes k) : e.subst σ = e := by
  induction e generalizing k σ with (simp [ClosedN] at self; simp [*, SExpr.subst])
  | bvar i => exact h _ self
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h.lift⟩

def inst (e a : SExpr) : SExpr := e.subst (.one a)

@[simp] theorem mkSubst_one : mkSubst (VExpr.Subst.one a) = Subst.one (mk a) := by
  funext i
  cases i <;> rfl

@[simp] theorem mk_instExpr : mk (e.inst a) = (mk e).inst (mk a) := by
  rw [VExpr.inst_eq, inst, mk_subst, mkSubst_one]

def Skips (e : SExpr) (ρ : Lift) : Prop := lift' (e.subst ρ.invS) ρ = e

theorem Skips.lift (e : SExpr) (ρ : Lift) : Skips (e.lift' ρ) ρ := by
  rw [Skips, subst_lift'_inv]

def Skips' : SExpr → (ρ : Lift) → Prop
  | .bvar i, ρ => ∃ j, ρ.liftVar j = i
  | .sort .., _ | .const .., _ => True
  | .app fn arg, ρ => fn.Skips' ρ ∧ arg.Skips' ρ
  | .lam ty body, ρ => ty.Skips' ρ ∧ body.Skips' ρ.cons
  | .forallE ty body, ρ => ty.Skips' ρ ∧ body.Skips' ρ.cons

theorem skips_iff {e : SExpr} {ρ : Lift} : Skips e ρ ↔ Skips' e ρ := by
  simp [Skips]; induction e generalizing ρ with simp!
  | app _ _ ih1 ih2 => exact and_congr ih1 ih2
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact and_congr ih1 (@ih2 ρ.cons)
  | bvar i =>
    constructor <;> [intro h; intro ⟨j, h⟩]
    · refine (?_ : have := (match ρ.invS i with | SExpr.bvar .. => True | _ => True); _); split
      · rename_i eq; cases eq ▸ h; exact ⟨_, rfl⟩
      · suffices ρ.invS i = default by cases this ▸ h
        clear h; rename_i h
        induction ρ generalizing i <;> simp [Lift.invS, Subst.id] at * <;>
          cases i <;> simp [Subst.cons, Subst.lift] at *
        case skip.succ ih i => exact ih _ h
        case cons.succ ih i => rw [ih i fun j h' => h _ (by rw [h']; rfl)]; rfl
    · refine .trans (?_ : _ = (bvar j).lift' ρ) (congrArg bvar h); congr 1
      rw [← h]; exact congrFun (@lift_l_inv _ ρ) j

theorem skips_inter {e : SExpr} : Skips e (ρ.inter ρ') ↔ Skips e ρ ∧ Skips e ρ' := by
  simp [skips_iff]
  induction e generalizing ρ ρ' with simp_all!
  | app => grind
  | lam _ _ _ ih2 | forallE _ _ _ ih2 => have := @ih2 ρ.cons ρ'.cons; grind [Lift.inter]
  | bvar =>
    constructor
    · rintro ⟨j, rfl⟩; constructor
      · rw [Lift.inter_comm, ← Lift.diff_comp]; exact ⟨_, Lift.liftVar_comp.symm⟩
      · rw [← Lift.diff_comp]; exact ⟨_, Lift.liftVar_comp.symm⟩
    · rintro ⟨⟨i, h⟩, ⟨j, rfl⟩⟩
      induction ρ generalizing i j ρ' with
      | refl => simp [Lift.inter]
      | skip ρ ih =>
        cases ρ' with
        | refl => simp [Lift.inter]; cases h; exact ⟨_, rfl⟩
        | skip => simp_all [Lift.inter]; exact ih _ _ h
        | cons => cases j <;> simp_all [Lift.inter, Lift.liftVar]; exact ih _ _ h
      | cons ρ ih =>
        cases i <;> simp_all [Lift.liftVar]
        · cases ρ' with
          | refl => simp [Lift.inter]; cases h; exact ⟨0, rfl⟩
          | skip => let 0 := j; simp_all
          | cons => let 0 := j; exact ⟨0, rfl⟩
        · cases ρ' with
          | refl => cases h; exact ⟨_+1, rfl⟩
          | skip => simp_all [Lift.liftVar, Lift.inter]; exact ih _ _ h
          | cons =>
            let _+1 := j; simp_all [Lift.inter]
            have ⟨_, h⟩ := ih _ _ h; exact ⟨_+1, congrArg (·+1) h⟩

theorem lift_r_inj {σ σ' : Subst} : σ.lift_r ρ = σ'.lift_r ρ ↔ σ = σ' := by
  refine ⟨fun h => funext fun i => ?_, (· ▸ rfl)⟩
  simpa [Subst.lift_r, lift'_inj] using congrFun h i

theorem Subst.lift_r_comm (σ : Subst) (ρ : Lift) (H : Subst.Depth σ 0 n) :
    σ.lift_r ρ = .lift_l (ρ.consN n) ((σ.lift_r ρ).trunc 0 n) := by
  funext i; simp [Subst.lift_l, Subst.lift_r, Subst.trunc]
  have : (ρ.consN n).liftVar i = if n ≤ i then ρ.liftVar (i-n) + n else i := by
    clear H; induction n generalizing i <;> [skip; cases i] <;> simp! [*]; split <;> rfl
  rw [this]; split <;> simp
  have := H (i - n); rw [Nat.sub_add_cancel ‹_›] at this; simp [this]

theorem lift_r_one (e : SExpr) (ρ : Lift) :
    (Subst.one e).lift_r ρ = .lift_l ρ.cons (Subst.one (e.lift' ρ)) := by
  refine (Subst.lift_r_comm (Subst.one e) ρ .one).trans ?_; congr 1
  funext i; simp [Subst.trunc]
  cases i <;> simp [Subst.one, Subst.cons, Subst.lift_r, Subst.id]

theorem lift_inst (e : SExpr) : e.lift.inst e' = e := by
  rw [inst, Subst.one, lift, subst_lift', ← Subst.tail_eq_lift_l, Subst.tail_cons, subst_id]

theorem lift'_inst_hi (e1 e2 : SExpr) (ρ : Lift) :
    lift' (e1.inst e2) ρ = (lift' e1 ρ.cons).inst (lift' e2 ρ) := by
  simp [inst, subst_lift', lift'_subst, lift_r_one]

theorem subst_inst {e : SExpr} : (e.inst a).subst σ = (e.subst σ.lift).inst (a.subst σ) := by
  rw [SExpr.inst, SExpr.inst, subst_subst, subst_subst]; congr 1
  funext i; obtain _|i := i <;> simp [Subst.comp, Subst.lift, SExpr.subst]
  · simp [Subst.one, Subst.cons]
  · rw [← SExpr.inst, lift_inst]; rfl

theorem inst_lift_cons {e : SExpr} {σ : Subst} :
    (e.subst σ.lift).inst x = e.subst (σ.cons x) := by
  rw [SExpr.inst, subst_subst, Subst.one]; congr 1
  funext i; obtain _|i := i <;>
    simp [Subst.comp, Subst.lift, SExpr.subst, Subst.cons, lift_subst_cons]

inductive Ctx.Lift' : Lift → List SExpr → List SExpr → Prop where
  | refl : Ctx.Lift' .refl Γ Γ
  | skip : Ctx.Lift' l Γ Γ' → Ctx.Lift' (.skip l) Γ (A :: Γ')
  | cons : Ctx.Lift' l Γ Γ' → Ctx.Lift' (.cons l) (A::Γ) (A.lift' l :: Γ')

theorem Ctx.Lift'.one : Ctx.Lift' (.skip .refl) Γ (A::Γ) := .skip .refl

theorem Ctx.Lift'.comp (H1 : Ctx.Lift' l Γ₀ Γ₁) (H2 : Ctx.Lift' l' Γ₁ Γ₂) : Ctx.Lift' (l.comp l') Γ₀ Γ₂ := by
  induction H2 generalizing l Γ₀ with
  | refl => exact H1
  | skip _ ih => exact (ih H1).skip
  | cons H2 ih =>
    cases H1 with
    | refl => exact .cons H2
    | skip H1 => exact .skip (ih H1)
    | cons H1 => exact SExpr.lift'_comp ▸ .cons (ih H1)

inductive Ctx.Inter : List SExpr → List SExpr → Lift → List SExpr → Lift → List SExpr → Prop where
  | refl_l : Ctx.Lift' ρ Γ Δ → Ctx.Inter Γ Δ .refl Γ ρ Δ
  | refl_r : Ctx.Lift' ρ Γ Δ → Ctx.Inter Γ Γ ρ Δ .refl Δ
  | skip_skip : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ → Ctx.Inter Γ Γ₁ (.skip ρ₁) Γ₂ (.skip ρ₂) (A::Δ)
  | skip_cons : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ →
    Ctx.Inter Γ Γ₁ (.skip ρ₁) (A :: Γ₂) (.cons ρ₂) (A.lift' ρ₂ :: Δ)
  | cons_skip : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ →
    Ctx.Inter Γ (A :: Γ₁) (.cons ρ₁) Γ₂ (.skip ρ₂) (A.lift' ρ₁ :: Δ)
  | cons_cons : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ →
    Ctx.Inter (A :: Γ) (A.lift' (ρ₂.diff ρ₁) :: Γ₁) (.cons ρ₁)
      (A.lift' (ρ₁.diff ρ₂) :: Γ₂) (.cons ρ₂) (A.lift' (ρ₁.inter ρ₂) :: Δ)

theorem lift_eq_lift {e₁ e₂ : SExpr} (H : e₁.lift' ρ₁ = e₂.lift' ρ₂) :
    ∃ e, .lift' e (ρ₂.diff ρ₁) = e₁ ∧ e.lift' (ρ₁.diff ρ₂) = e₂ := by
  have := Skips.lift e₁ ρ₁
  have h1 : _ = _ := skips_inter.2 ⟨.lift e₁ ρ₁, H ▸ Skips.lift e₂ ρ₂⟩
  have h2 := h1; conv at h1 => enter [1,2]; rw [← Lift.diff_comp]
  conv at h2 => enter [1,2]; rw [Lift.inter_comm, ← Lift.diff_comp]
  rw [lift'_comp] at h1 h2
  exact ⟨_, lift'_inj.1 h2, lift'_inj.1 (h1.trans H)⟩

theorem Ctx.Inter.mk (H1 : Ctx.Lift' l₁ Γ₁ Δ) (H2 : Ctx.Lift' l₂ Γ₂ Δ) :
    ∃ Γ, Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ := by
  induction H1 generalizing l₂ Γ₂ with
  | refl => exact ⟨_, .refl_l H2⟩
  | skip H1 ih =>
    cases H2 with
    | refl => exact ⟨_, .refl_r (.skip H1)⟩
    | skip H2 => let ⟨_, H⟩ := ih H2; exact ⟨_, .skip_skip H⟩
    | cons H2 => let ⟨_, H⟩ := ih H2; exact ⟨_, .skip_cons H⟩
  | @cons l₁ _ _ A₁ H1 ih =>
    generalize eq : A₁.lift' l₁ = A' at H2
    cases H2 with
    | refl => subst eq; exact ⟨_, .refl_r (.cons H1)⟩
    | skip H2 => subst eq; let ⟨_, H⟩ := ih H2; exact ⟨_, .cons_skip H⟩
    | @cons l₂ _ _ A₂ H2 =>
      obtain ⟨_, rfl, rfl⟩ := lift_eq_lift eq
      rw [← lift'_comp, Lift.diff_comp]
      let ⟨_, H⟩ := ih H2; exact ⟨_, .cons_cons H⟩

theorem Ctx.Inter.symm (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Inter Γ Γ₂ l₂ Γ₁ l₁ Δ := by
  induction H with
  | refl_l h => exact .refl_r h
  | refl_r h => exact .refl_l h
  | skip_skip _ ih => exact .skip_skip ih
  | skip_cons _ ih => exact .cons_skip ih
  | cons_skip _ ih => exact .skip_cons ih
  | cons_cons _ ih => rw [Lift.inter_comm]; exact .cons_cons ih

theorem Ctx.Inter.diff (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Lift' (l₁.diff l₂) Γ Γ₂ := by
  induction H with
  | refl_l h => exact .refl
  | refl_r h => simpa
  | skip_skip _ ih | cons_skip _ ih => exact ih
  | skip_cons _ ih => exact ih.skip
  | cons_cons _ ih => exact ih.cons

theorem Ctx.Inter.right (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Lift' l₂ Γ₂ Δ := by
  induction H with
  | refl_l h => exact h
  | refl_r h => exact .refl
  | skip_skip _ ih => exact ih.skip
  | cons_skip _ ih => exact ih.skip
  | skip_cons _ ih => exact ih.cons
  | cons_cons _ ih => rw [← Lift.diff_comp, SExpr.lift'_comp]; exact ih.cons

theorem Ctx.Inter.left (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Lift' l₁ Γ₁ Δ := H.symm.right

inductive _root_.Lean4Lean.Pattern.MatchesS :
    (p : Pattern) → SExpr → List SLevel → (p.Path → SExpr) → Prop
  | const : MatchesS (.const c) (.const c ls) ls nofun
  | var : MatchesS f f' f1 g1 → MatchesS (.var f) (.app f' a') f1 (·.elim a' g1)
  | app : MatchesS f f' f1 g1 → MatchesS a a' f2 g2 →
    MatchesS (.app f a) (.app f' a') f1 (Sum.elim g1 g2)

def _root_.Lean4Lean.Pattern.RHS.applyS {p : Pattern}
    (m1 : List SLevel) (m2 : p.Path → SExpr) : p.RHS → SExpr
  | .fixed c _ => .mkInst m1 c
  | .var path => m2 path
  | .app f a => .app (f.applyS m1 m2) (a.applyS m1 m2)

def _root_.Lean4Lean.Pattern.RHS.Closed {p : Pattern} : p.RHS → Prop
  | .fixed c _ => c.Closed
  | .var _ => True
  | .app f a => f.Closed ∧ a.Closed

theorem _root_.Lean4Lean.Pattern.RHS.Closed.applyS {p : Pattern} {m1 m2} :
    ∀ r : p.RHS, r.Closed → (∀ a, (m2 a).ClosedN k) → (r.applyS m1 m2).ClosedN k
  | .fixed .., h1, _ => h1.mkInstS.mono (Nat.zero_le _)
  | .var _, _, h2 => h2 _
  | .app .., h1, h2 => ⟨h1.1.applyS _ h2, h1.2.applyS _ h2⟩

def _root_.Lean4Lean.Pattern.Check.defeqsS {p : Pattern}
    (m1 : List SLevel) (m2 : p.Path → SExpr) : p.Check → List (SExpr × SExpr)
  | .true => []
  | .defeq a b rest => (a.applyS m1 m2, b.applyS m1 m2) :: rest.defeqsS m1 m2

section
set_option hygiene false

inductive Lookup : List SExpr → Nat → SExpr → Prop where
  | zero : Lookup (ty::Γ) 0 ty.lift
  | succ : Lookup Γ n ty → Lookup (A::Γ) (n+1) ty.lift

theorem Lookup.mkS (H : Lean4Lean.Lookup Γ i A) : Lookup (Γ.map mk) i (mk A) := by
  induction H with
  | zero => rw [mk_lift]; exact .zero
  | succ _ ih => rw [mk_lift]; exact .succ ih

theorem Lookup.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Lookup Γ i A) :
    Lookup Γ' (ρ.liftVar i) (A.lift' ρ) := by
  induction W generalizing i A with
  | refl => simp; exact H
  | skip W ih => have' := (ih H).succ; rwa [SExpr.lift, ← SExpr.lift'_comp] at this
  | cons W ih =>
    cases H with
    | zero => refine' cast _ Lookup.zero; congr 1; simp [SExpr.lift, ← SExpr.lift'_comp]
    | succ H => refine' cast _ (ih H).succ; congr 1; simp [SExpr.lift, ← SExpr.lift'_comp]

theorem Lookup.weakU_inv (W : Ctx.Lift' ρ Γ Γ')
    (H : Lookup Γ' (ρ.liftVar i) A') : ∃ A, A' = A.lift' ρ ∧ Lookup Γ i A := by
  induction W generalizing i A' with
  | refl => simpa using H
  | @skip ρ W _ _ _ ih =>
    simp at H; let .succ H := H
    obtain ⟨_, rfl, h2⟩ := ih H; refine ⟨_, ?_, h2⟩
    rw [SExpr.lift, ← SExpr.lift'_comp]; rfl
  | @cons ρ Γ Δ B W ih =>
    cases i with
    | zero => cases H; exact ⟨_, by simp [SExpr.lift, ← SExpr.lift'_comp], .zero⟩
    | succ i =>
      let .succ (ty := C) H := H
      obtain ⟨C, rfl, h⟩ := ih H
      refine ⟨_, ?_, .succ h⟩
      simp [SExpr.lift, ← SExpr.lift'_comp]

theorem Lookup.weak'_inv (W : Ctx.Lift' ρ Γ Γ')
    (H : Lookup Γ' (ρ.liftVar i) (A.lift' ρ)) : Lookup Γ i A := by
  let ⟨_, h1, h2⟩ := H.weakU_inv W
  exact SExpr.lift'_inj.1 h1 ▸ h2

theorem Lookup.uniq (hA : Lookup Γ i A) (hB : Lookup Γ i B) : A = B :=
  match hA, hB with
  | .zero, .zero => rfl
  | .succ hA, .succ hB => Lookup.uniq hA hB ▸ rfl

theorem Lookup.determ (H1 : Lookup Γ i A) (H2 : Lookup Γ i A') : A = A' := by
  induction H1 generalizing A' with obtain _ | r1 := H2
  | zero => rfl
  | succ _ ih => cases ih r1; rfl

scoped notation:65 Γ " ⊢ " e " : " A:36 => IsDefEq Γ e e A
scoped notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEq Γ e1 e2 A
inductive IsDefEq : List SExpr → SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  /-- Heterogeneous transitivity: middle term may be at a different sort. -/
  | trans' : Γ ⊢ A ≡ B : .sort u → Γ ⊢ B ≡ C : .sort v → Γ ⊢ A ≡ C : .sort u
  | sort : Γ ⊢ .sort l : .sort (.succ l)
  | const : env.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ .const c ls : SExpr.mkInst ls ci.type
  | appDF : Γ ⊢ f ≡ f' : .forallE A B → Γ ⊢ a ≡ a' : A →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | lamDF : Γ ⊢ A ≡ A' : .sort u → A::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF : Γ ⊢ A ≡ A' : .sort u → A::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta : A::Γ ⊢ e : B → Γ ⊢ e' : A → Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta : Γ ⊢ e : .forallE A B → Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ h' : p
  -- | extra : Pat p r → p.MatchesS e m1 m2 → (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 →
  --   (∀ a b A, (A, a, b) ∈ dfs → Γ ⊢ a ≡ b : A) → Γ ⊢ e ≡ r.1.applyS m1 m2' : A
  | extra : env.defeqs df → ls.length = df.uvars →
    Γ ⊢ .mkInst ls df.lhs ≡ .mkInst ls df.rhs : .mkInst ls df.type

/-- Translate the main typing judgment into the semantically quotiented syntax. -/
theorem IsDefEq.mkS (H : Params.env.IsDefEq Params.univs Γ e₁ e₂ A) :
    OnCtx Γ (fun _ A => A.LevelWF Params.univs) →
    IsDefEq (Γ.map mk) (mk e₁) (mk e₂) (mk A) := by
  intro hΓ
  induction H with
  | bvar h => exact .bvar (SExpr.Lookup.mkS h)
  | symm _ ih => exact .symm (ih hΓ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ hΓ) (ih₂ hΓ)
  | @sortDF l l' Γ hl hl' h =>
    change IsDefEq _ (.sort (SLevel.mk _)) (.sort (SLevel.mk _)) (.sort (SLevel.mk _))
    have hu := SLevel.mk_eq hl hl' h
    have hus : SLevel.mk l.succ = (SLevel.mk l').succ := by rw [SLevel.mk_succ hl, hu]
    rw [hu, hus]
    exact .sort
  | @constDF c ci ls ls' Γ h₁ h₂ h₃ h₄ h₅ =>
    change IsDefEq _ (.const c (ls.map SLevel.mk)) (.const c (ls'.map SLevel.mk))
      (mk (ci.type.instL ls))
    rw [← SLevel.map_mk_eq h₂ h₃ h₅, ← mkInst_map_mk h₂]
    exact IsDefEq.const (ls := ls.map SLevel.mk) h₁ (by simpa using h₄)
  | appDF _ _ ihf iha => simpa only [mk, mk_instExpr] using IsDefEq.appDF (ihf hΓ) (iha hΓ)
  | lamDF hA _ ihA ihb =>
    have hAwf := (hA.levelWF hΓ).1
    exact .lamDF (ihA hΓ) (ihb ⟨hΓ, hAwf⟩)
  | forallEDF hA hb ihA ihb =>
    have hAwf := (hA.levelWF hΓ).1
    have hu := (hA.levelWF hΓ).2.2
    have hv := (hb.levelWF ⟨hΓ, hAwf⟩).2.2
    simpa only [mk, SLevel.mk_imax hu hv] using IsDefEq.forallEDF (ihA hΓ) (ihb ⟨hΓ, hAwf⟩)
  | defeqDF _ _ ihA ihe => exact .defeqDF (ihA hΓ) (ihe hΓ)
  | beta _ he' ihe ihe' =>
    have hAwf := (he'.levelWF hΓ).2.2
    simpa only [mk, mk_instExpr] using IsDefEq.beta (ihe ⟨hΓ, hAwf⟩) (ihe' hΓ)
  | eta _ ih => simpa only [mk, mk_lift] using IsDefEq.eta (ih hΓ)
  | proofIrrel _ _ _ ihp ihh ihh' => exact .proofIrrel (ihp hΓ) (ihh hΓ) (ihh' hΓ)
  | @extra df ls Γ h₁ h₂ h₃ =>
    simpa only [mkInst_map_mk h₂] using
      (IsDefEq.extra (Γ := Γ.map mk) (ls := ls.map SLevel.mk) h₁ (by simpa using h₃))

/-- Translate an empty-context `VExpr` judgment into an arbitrary `SExpr` context. -/
theorem IsDefEq.mkS0 (H : Params.env.IsDefEq Params.univs [] e₁ e₂ A) (Γ : List SExpr) :
    IsDefEq Γ (mk e₁) (mk e₂) (mk A) :=
  let ⟨_, hΓ', h⟩ := SExpr.exists_map_mk Γ
  h ▸ IsDefEq.mkS (H.weak0 Params.henv) hΓ'

/-- Constant types are well-formed types, in any context. -/
theorem Params.const_wf (h : env.constants c = some ci) :
    ∃ u, Γ ⊢ mkInst ls ci.type : .sort u := by
  obtain ⟨vs, hvs, rfl⟩ := SLevel.exists_map_mk ls
  have ⟨_, hu⟩ := Params.henv.constWF h
  rw [mkInst_map_mk hvs]
  exact ⟨_, IsDefEq.mkS0 (hu.instL hvs) Γ⟩

/-- Defeq rules are well-typed: the type is a type and both sides inhabit it, in any context. -/
theorem Params.defeq_wf (h : env.defeqs df) :
    (∃ u, Γ ⊢ mkInst ls df.type : .sort u) ∧
    Γ ⊢ mkInst ls df.lhs : mkInst ls df.type ∧ Γ ⊢ mkInst ls df.rhs : mkInst ls df.type := by
  obtain ⟨vs, hvs, rfl⟩ := SLevel.exists_map_mk ls
  have ⟨hl, hr⟩ := Params.henv.defEqWF h
  have ⟨_, hu⟩ := hl.isType Params.henv (by trivial)
  simp only [mkInst_map_mk hvs]
  exact ⟨⟨_, IsDefEq.mkS0 (hu.instL hvs) Γ⟩,
    IsDefEq.mkS0 (hl.instL hvs) Γ, IsDefEq.mkS0 (hr.instL hvs) Γ⟩

/-! ### Translating the pattern theory along `mk` -/

theorem _root_.Lean4Lean.Pattern.MatchesS.congr {p : Pattern} {e m1} {m2 m2' : p.Path → SExpr}
    (H : p.MatchesS e m1 m2) (h : ∀ x, m2 x = m2' x) : p.MatchesS e m1 m2' := funext h ▸ H

theorem _root_.Lean4Lean.Pattern.Matches.mkS {p : Pattern} {e : VExpr} {m1 m2}
    (H : p.Matches e m1 m2) : p.MatchesS (mk e) (m1.map SLevel.mk) (fun x => mk (m2 x)) := by
  induction H with
  | const => exact Pattern.MatchesS.congr .const nofun
  | var _ ih => exact ih.var.congr fun | none => rfl | some _ => rfl
  | app _ _ ih1 ih2 => exact (ih1.app ih2).congr fun | .inl _ => rfl | .inr _ => rfl

theorem _root_.Lean4Lean.Pattern.RHS.mkS_apply {p : Pattern} {m1 : List VLevel}
    {m2 : p.Path → VExpr} (hm1 : ∀ u ∈ m1, u.WF univs) :
    ∀ r : p.RHS, mk (r.apply m1 m2) = r.applyS (m1.map SLevel.mk) (fun x => mk (m2 x))
  | .fixed _ _ => (mkInst_map_mk hm1).symm
  | .var _ => rfl
  | .app f a => by
    simp only [Pattern.RHS.apply, Pattern.RHS.applyS, mk, mkS_apply hm1 f, mkS_apply hm1 a]

/-- Side conditions that hold as `VExpr` defeqs translate to a list of `SExpr` defeqs. -/
theorem _root_.Lean4Lean.Pattern.Check.OK.mkS {p : Pattern} {Γ : List VExpr} {m1 m2}
    (hΓ : OnCtx Γ fun _ A => A.LevelWF univs) (hm1 : ∀ u ∈ m1, u.WF univs) :
    ∀ {ck : p.Check}, ck.OK (env.IsDefEqU univs Γ) m1 m2 →
    ∃ dfs : List (SExpr × SExpr × SExpr),
      dfs.map (·.2) = ck.defeqsS (m1.map SLevel.mk) (fun x => mk (m2 x)) ∧
      ∀ a b A, (A, a, b) ∈ dfs → IsDefEq (Γ.map mk) a b A
  | .true, _ => ⟨[], rfl, nofun⟩
  | .defeq a b rest, ⟨⟨A, h⟩, hrest⟩ =>
    let ⟨dfs, h1, h2⟩ := Pattern.Check.OK.mkS hΓ hm1 hrest
    ⟨(mk A, mk (a.apply m1 m2), mk (b.apply m1 m2)) :: dfs,
      by simp only [List.map_cons, Pattern.Check.defeqsS, h1, Pattern.RHS.mkS_apply hm1],
      by
        intro a' b' A' h'
        rcases List.mem_cons.1 h' with h' | h'
        · cases h'; exact IsDefEq.mkS h hΓ
        · exact h2 _ _ _ h'⟩

/-- The `SExpr` form of `Params.extra_patV`: every instantiated defeq rule is a pattern
instance whose side conditions hold in any `SExpr` context. -/
theorem Params.extra_pat (Γ) : env.defeqs df → ls.length = df.uvars →
    ∃ p r m1 m2 dfs, Pat p r ∧ p.MatchesS (.mkInst ls df.lhs) m1 m2 ∧
      (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 ∧
      (∀ a b A, (A, a, b) ∈ dfs → Γ ⊢ a ≡ b : A) ∧
      .mkInst ls df.rhs = r.1.applyS m1 m2 := by
  intro h1 h2
  obtain ⟨vs, hvs, rfl⟩ := SLevel.exists_map_mk ls
  obtain ⟨Γ', hΓ', rfl⟩ := SExpr.exists_map_mk Γ
  obtain ⟨p, r, m1, m2, hp, hm, hok, hr⟩ :=
    Params.extra_patV (Γ := Γ') h1 hvs (by simpa using h2)
  have hm1 := hm.levelWF (VExpr.LevelWF.instL hvs)
  obtain ⟨dfs, hdfs, hdefeq⟩ := hok.mkS hΓ' hm1
  refine ⟨p, r, _, _, dfs, hp, ?_, hdfs, hdefeq, ?_⟩
  · rw [mkInst_map_mk hvs]; exact hm.mkS
  · rw [mkInst_map_mk hvs, hr]; exact Pattern.RHS.mkS_apply hm1 _

def CtorBundle.IsCtor (c : Name) : Prop :=
  ∃ cl, Params.classify c = some cl ∧ cl matches .ctor .. | .etaCtor ..

def CtorBundle.IsCtor.cl (H : CtorBundle.IsCtor c) :
    {cl // Params.classify c = some cl ∧ cl matches .ctor .. | .etaCtor ..} := by
  dsimp [CtorBundle.IsCtor] at H
  match Params.classify c, H with
  | some cl, H => refine ⟨cl, ?_⟩; obtain ⟨_, ⟨⟩, H⟩ := H; exact ⟨rfl, H⟩

structure CtorBundle (c : Name) (cl : CtorBundle.IsCtor c) : Type where
  I : Name
  Ts : List SExpr
  args : List SExpr
  u : SLevel
  hlen : Ts.length = cl.cl.1.arity
  hclI : Params.classify I = some (.indTy args.length)
  hu0 : u ≠ .zero

def CtorBundle.rhs (H : CtorBundle c cl) (ls : List SLevel) : SExpr :=
  H.Ts.foldr .forallE (H.args.foldr (fun A acc => acc.app A) (.const H.I ls))

section
local notation:65 (priority := high) Γ " ⊢ " e1 " : " A:36 => IsDefEqStrong Γ e1 e1 A
local notation:65 (priority := high) Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEqStrong Γ e1 e2 A
inductive IsDefEqStrong : List SExpr → SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ A : .sort u → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ A : .sort u → Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  /-- Heterogeneous transitivity: middle term may be at a different sort. -/
  | trans' : Γ ⊢ A ≡ B : .sort u → Γ ⊢ B ≡ C : .sort v → Γ ⊢ A ≡ C : .sort u
  | sort : Γ ⊢ .sort l : .sort (.succ l)
  | const : env.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ SExpr.mkInst ls ci.type : .sort u →
    (F : ∀ cl, CtorBundle c cl) →
    (∀ cl, Γ ⊢ SExpr.mkInst ls ci.type ≡ (F cl).rhs ls : .sort (F cl).u) →
    Γ ⊢ .const c ls : SExpr.mkInst ls ci.type
  | appDF : Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v →
    Γ ⊢ f ≡ f' : .forallE A B → Γ ⊢ a ≡ a' : A →
    Γ ⊢ B.inst a ≡ B.inst a' : .sort v →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | lamDF : Γ ⊢ A ≡ A' : .sort u → A::Γ ⊢ B : .sort v →
    A::Γ ⊢ body ≡ body' : B → A'::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF : Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : .sort v → A'::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta : A::Γ ⊢ e : B → Γ ⊢ e' : A →
    Γ ⊢ .app (.lam A e) e' : B.inst e' → Γ ⊢ e.inst e' : B.inst e' →
    Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta : Γ ⊢ e : .forallE A B → Γ ⊢ .lam A (.app e.lift (.bvar 0)) : .forallE A B →
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ h' : p
  | extra : env.defeqs df → ls.length = df.uvars →
    Γ ⊢ .mkInst ls df.lhs : .mkInst ls df.type →
    Γ ⊢ .mkInst ls df.rhs : .mkInst ls df.type →
    Γ ⊢ .mkInst ls df.lhs ≡ .mkInst ls df.rhs : .mkInst ls df.type
end

theorem IsDefEqStrong.defeq : IsDefEqStrong Γ e1 e2 A → Γ ⊢ e1 ≡ e2 : A := by
  intro h
  induction h with
  | bvar h _ _ => exact .bvar h
  | symm _ ih => exact .symm ih
  | trans _ _ _ _ ih1 ih2 => exact .trans ih1 ih2
  | trans' _ _ ih1 ih2 => exact .trans' ih1 ih2
  | sort => exact .sort
  | const h1 h2 _ _ _ _ _ => exact .const h1 h2
  | appDF _ _ _ _ _ _ _ ihf iha _ => exact .appDF ihf iha
  | lamDF _ _ _ _ ihA _ ihb _ => exact .lamDF ihA ihb
  | forallEDF _ _ _ ihA ihb _ => exact .forallEDF ihA ihb
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ _ _ ih1 ih2 _ _ => exact .beta ih1 ih2
  | eta _ _ ih _ => exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 _ _ _ _ => exact .extra h1 h2

theorem mk_instL_foldr_forallE (Ts : List VExpr) (X : VExpr) :
    mk ((Ts.foldr .forallE X).instL vs) =
      (Ts.map fun T => mk (T.instL vs)).foldr .forallE (mk (X.instL vs)) := by
  induction Ts with
  | nil => rfl
  | cons T Ts ih => simp only [List.foldr_cons, List.map_cons, VExpr.instL, mk, ih]

theorem mk_instL_foldr_app (args : List VExpr) (X : VExpr) :
    mk ((args.foldr (fun A acc => acc.app A) X).instL vs) =
      (args.map fun A => mk (A.instL vs)).foldr (fun A acc => acc.app A) (mk (X.instL vs)) := by
  induction args with
  | nil => rfl
  | cons A args ih => simp only [List.foldr_cons, List.map_cons, VExpr.instL, mk, ih]

/-- The `SExpr` form of `Params.ctor_tyV`, at any level list and in any context. -/
theorem _root_.Lean4Lean.Params.ctor_ty
    (hctor : cl matches .ctor .. | .etaCtor ..) (hcl : Params.classify c = some cl)
    (hci : env.constants c = some ci) (h_len : ls.length = ci.uvars) :
    ∃ (I : Name) (Ts args : List SExpr) (u : SLevel),
      Ts.length = cl.arity ∧ Params.classify I = some (.indTy args.length) ∧ u ≠ .zero ∧
      Γ ⊢ SExpr.mkInst ls ci.type ≡
        Ts.foldr .forallE (args.foldr (fun A acc => acc.app A) (.const I ls)) : .sort u := by
  obtain ⟨vs, hvs, rfl⟩ := SLevel.exists_map_mk ls
  obtain ⟨I, Ts, args, u, hTs, hI, hu, H⟩ := Params.ctor_tyV hctor hcl hci
  have hlen : vs.length = ci.uvars := by simpa using h_len
  refine ⟨I, Ts.map fun T => mk (T.instL vs), args.map fun A => mk (A.instL vs),
    .mk (u.inst vs), by simp [hTs], by simpa using hI, fun h => ?_, ?_⟩
  · rw [SLevel.mk_of_wf (VLevel.WF.inst hvs)] at h
    have := congrFun (congrArg Subtype.val h) []
    simp only [VLevel.eval_inst, SLevel.zero, VLevel.eval] at this
    exact hu _ this
  · have := IsDefEq.mkS0 (H.instL hvs) Γ
    rw [mk_instL_foldr_forallE, mk_instL_foldr_app] at this
    rw [mkInst_map_mk hvs]
    simpa only [VExpr.instL, mk, VLevel.inst_map_id hlen] using this

theorem IsDefEq.hasType (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ ⊢ e1 ≡ e1 : A ∧ Γ ⊢ e2 ≡ e2 : A := ⟨H.trans H.symm, H.symm.trans H⟩

section
set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A true n
local notation:65 Γ " ⊢ " e " :! " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A false n

/-- SExpr-side analog of `HasTypeStratified`: a typing derivation indexed by
its tree depth `n`, used for well-founded induction on stratification. -/
inductive HasTypeStratifiedS : List SExpr → SExpr → SExpr → Bool → Nat → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ A : .sort u !! n → Γ ⊢ .bvar i :! A !! n+1
  | sort' : Γ ⊢ .sort l :! .sort (.succ l) !! n
  | const :
    env.constants c = some ci →
    ls.length = ci.uvars →
    Γ ⊢ mkInst ls ci.type : .sort u !! n →
    Γ ⊢ .const c ls :! mkInst ls ci.type !! n+1
  | app :
    Γ ⊢ A : .sort u !! n →
    A::Γ ⊢ B : .sort v !! n →
    Γ ⊢ f : .forallE A B !! n →
    Γ ⊢ a : A !! n →
    Γ ⊢ B.inst a : .sort v !! n →
    Γ ⊢ .app f a :! B.inst a !! n+1
  | lam :
    Γ ⊢ A : .sort u !! n →
    A::Γ ⊢ B : .sort v !! n →
    A::Γ ⊢ body : B !! n →
    Γ ⊢ .forallE A B : .sort (.imax u v) !! n →
    Γ ⊢ .lam A body :! .forallE A B !! n+1
  | forallE :
    Γ ⊢ A : .sort u !! n →
    A::Γ ⊢ body : .sort v !! n →
    Γ ⊢ .forallE A body :! .sort (.imax u v) !! n+1
  | base : Γ ⊢ e :! A !! n → Γ ⊢ e : A !! n
  | defeq : Γ ⊢ A ≡ B : .sort u →
    Γ ⊢ A : .sort u !! n → Γ ⊢ B : .sort u !! n →
    Γ ⊢ e : A !! n → Γ ⊢ e : B !! n+1
end

scoped notation:65 Γ " ⊢ " e " : " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A true n
scoped notation:65 Γ " ⊢ " e " :! " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A false n

theorem HasTypeStratifiedS.to_core (H : Γ ⊢ e : A !! n) :
    ∃ A', Γ ⊢ e :! A' !! n := sorry

theorem HasTypeStratifiedS.isType (H : HasTypeStratifiedS Γ e A b n) :
    ∃ u, Γ ⊢ A : .sort u !! n - 1 := sorry

def Ctx.WF : List SExpr → Prop
  | [] => True
  | A::Γ => WF Γ ∧ ∃ u, Γ ⊢ A : .sort u
scoped notation:65 "⊢ " Γ:36 => Ctx.WF Γ

theorem Ctx.WF.cons (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) : ⊢ A :: Γ := ⟨hΓ, _, hA⟩

variable (HasType : List SExpr → SExpr → SExpr → Prop)
inductive Ctx.Subst (Γ : List SExpr) : SExpr.Subst → List SExpr → Prop where
  | nil : Ctx.Subst Γ σ []
  | cons : Ctx.Subst Γ σ.tail Δ → HasType Γ σ.head (A.subst σ.tail) → Ctx.Subst Γ σ (A::Δ)

variable {HasType}
theorem Ctx.Subst.head (H : Ctx.Subst HasType Γ σ (A::Δ)) : HasType Γ σ.head (A.subst σ.tail) :=
  let .cons _ H := H; H

theorem Ctx.Subst.tail (H : Ctx.Subst HasType Γ σ (A::Δ)) : Ctx.Subst HasType Γ σ.tail Δ :=
  let .cons H _ := H; H

theorem Ctx.Subst.cons' (H1 : Ctx.Subst HasType Γ σ Δ) (H2 : HasType Γ e (A.subst σ)) :
    Ctx.Subst HasType Γ (σ.cons e) (A::Δ) := .cons H1 H2

theorem Ctx.Subst.lift_r
    (weak : ∀ {ρ Γ Δ e A}, Ctx.Lift' ρ Γ Δ → HasType Γ e A → HasType Δ (e.lift' ρ) (A.lift' ρ))
    (H1 : Ctx.Subst HasType Θ σ Γ) (H2 : Ctx.Lift' ρ Θ Δ) :
    Ctx.Subst HasType Δ (σ.lift_r ρ) Γ := by
  induction H1 with
  | nil => exact .nil
  | cons _ h ih =>
    refine .cons ih ?_
    have := weak H2 h
    rw [lift'_subst] at this; exact this

theorem Subst.lift_tail_eq (σ : Subst) : σ.lift.tail = σ.lift_r (.skip .refl) := by
  funext i; simp [SExpr.Subst.tail, SExpr.Subst.lift, SExpr.Subst.lift_r]

theorem Ctx.Subst.lift (bvar : ∀ {Γ i A}, Lookup Γ i A → HasType Γ (bvar i) A)
    (weak : ∀ {ρ Γ Δ e A}, Ctx.Lift' ρ Γ Δ → HasType Γ e A → HasType Δ (e.lift' ρ) (A.lift' ρ))
    (H : Ctx.Subst HasType Γ σ Δ) : Ctx.Subst HasType (A.subst σ :: Γ) σ.lift (A :: Δ) := by
  have : σ.lift.tail = σ.lift_r (.skip .refl) := Subst.lift_tail_eq σ
  refine .cons (this ▸ .lift_r weak H .one) (this ▸ bvar ?_)
  rw [← lift'_subst, ← SExpr.lift]; exact .zero

theorem Subst.id_tail_eq : (SExpr.Subst.id).tail = SExpr.Subst.id.lift_r (.skip .refl) := by
  funext i; rfl

theorem Ctx.Subst.id (bvar : ∀ {Γ i A}, Lookup Γ i A → HasType Γ (bvar i) A)
    (weak : ∀ {ρ Γ Δ e A}, Ctx.Lift' ρ Γ Δ → HasType Γ e A → HasType Δ (e.lift' ρ) (A.lift' ρ)) :
    ∀ {Γ}, Ctx.Subst HasType Γ .id Γ
  | [] => .nil
  | A :: Γ => by
    refine .cons (Subst.id_tail_eq ▸ .lift_r weak (Ctx.Subst.id bvar weak) .one) (bvar ?_)
    show Lookup (A :: Γ) 0 (A.subst SExpr.Subst.id.tail)
    rw [Subst.id_tail_eq, ← lift'_subst, subst_id]; exact .zero

theorem Ctx.Subst.one (bvar : ∀ {Γ i A}, Lookup Γ i A → HasType Γ (bvar i) A)
    (weak : ∀ {ρ Γ Δ e A}, Ctx.Lift' ρ Γ Δ → HasType Γ e A → HasType Δ (e.lift' ρ) (A.lift' ρ))
    (H : HasType Γ e A) : Ctx.Subst HasType Γ (.one e) (A::Γ) :=
  .cons (.id bvar weak) (by simpa)


/-! ### Strong typing: every weak derivation in a well-formed context is strong -/
/-! ## Small syntactic lemmas -/

theorem lift'_sort {u : SLevel} {ρ : Lift} : (SExpr.sort u).lift' ρ = .sort u := rfl
theorem subst_sort {u : SLevel} {σ : Subst} : (SExpr.sort u).subst σ = .sort u := rfl
theorem lift'_const {ρ : Lift} : (SExpr.const c ls).lift' ρ = .const c ls := rfl
theorem subst_const {σ : Subst} : (SExpr.const c ls).subst σ = .const c ls := rfl

theorem Lookup.lt (H : Lookup Γ i A) : i < Γ.length := by
  induction H with
  | zero => exact Nat.succ_pos _
  | succ _ ih => exact Nat.succ_lt_succ ih

theorem Ctx.Lift'.nil : ∀ Γ : List SExpr, Ctx.Lift' (Lift.skipN .refl Γ.length) [] Γ
  | [] => .refl
  | _ :: Γ => .skip (nil Γ)

theorem Subst.lift_r_tail {σ : Subst} {ρ : Lift} :
    (σ.lift_r ρ).tail = σ.tail.lift_r ρ := rfl

theorem lift_subst_lift {e : SExpr} {σ : Subst} : e.lift.subst σ.lift = (e.subst σ).lift := by
  rw [lift_subst, Subst.lift_tail_eq, ← lift'_subst]

theorem lift_cons_skip_inst_bvar0 {X : SExpr} :
    (X.lift' (.cons (.skip .refl))).inst (.bvar 0) = X := by
  have hsub : (Subst.lift_l (.cons (.skip .refl)) (Subst.one (.bvar 0))) = (Subst.id : Subst) := by
    funext i; cases i <;> rfl
  show (X.lift' (.cons (.skip .refl))).subst (.one (.bvar 0)) = X
  rw [subst_lift', hsub, subst_id]

/-- Closedness of the constant-type expression. This is the only place the
expression `mkInst ls ci.type` is inspected. -/
theorem constType_closed (h1 : env.constants c = some ci) :
    ClosedN (mkInst ls ci.type) := (henv.closedC h1).mkInstS

/-- Closedness of the defeq lhs/rhs/type expressions. -/
theorem defeq_closed (h1 : env.defeqs df) :
    ClosedN (.mkInst ls df.lhs) ∧ ClosedN (.mkInst ls df.rhs) ∧
      ClosedN (.mkInst ls df.type) :=
  have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
  ⟨hA1.mkInstS, hA2.mkInstS, hA3.mkInstS⟩

/-! ## CtorBundle transport along `lift'`/`subst` -/

/-- A telescope `Ts.foldr forallE b` transported by any binder-aware map `F`
is again a telescope of the same length. -/
theorem foldr_forallE_map {α : Type} {F : α → SExpr → SExpr} {step : α → α}
    (hPi : ∀ x A B, F x (.forallE A B) = .forallE (F x A) (F (step x) B)) :
    ∀ (Ts : List SExpr) (x : α) (b : SExpr),
      ∃ (Ts' : List SExpr) (x' : α), Ts'.length = Ts.length ∧
        F x (Ts.foldr .forallE b) = Ts'.foldr .forallE (F x' b)
  | [], x, b => ⟨[], x, rfl, rfl⟩
  | T :: Ts, x, b => by
    have ⟨Ts', x', h1, h2⟩ := foldr_forallE_map hPi Ts (step x) b
    exact ⟨F x T :: Ts', x', by simp [h1], by simp [List.foldr, hPi, h2]⟩

theorem foldr_app_map {α : Type} {F : α → SExpr → SExpr}
    (hApp : ∀ x f a, F x (.app f a) = .app (F x f) (F x a))
    (hConst : ∀ x c ls, F x (.const c ls) = .const c ls) (x : α) :
    ∀ (args : List SExpr),
      F x (args.foldr (fun A acc => acc.app A) (.const I ls)) =
        (args.map (F x)).foldr (fun A acc => acc.app A) (.const I ls)
  | [] => hConst ..
  | a :: args => by simp [List.foldr, hApp, foldr_app_map hApp hConst x args]

theorem CtorBundle.exists_map {α : Type} {F : α → SExpr → SExpr} {step : α → α}
    (hPi : ∀ x A B, F x (.forallE A B) = .forallE (F x A) (F (step x) B))
    (hApp : ∀ x f a, F x (.app f a) = .app (F x f) (F x a))
    (hConst : ∀ x c ls, F x (.const c ls) = .const c ls)
    {c cl} (B : CtorBundle c cl) (x : α) (ls : List SLevel) :
    ∃ B' : CtorBundle c cl, B'.u = B.u ∧ B'.rhs ls = F x (B.rhs ls) := by
  have ⟨Ts', x', h1, h2⟩ := foldr_forallE_map hPi B.Ts x
    (B.args.foldr (fun A acc => acc.app A) (.const B.I ls))
  refine ⟨⟨B.I, Ts', B.args.map (F x'), B.u, h1.trans B.hlen, by simpa using B.hclI, B.hu0⟩,
    rfl, ?_⟩
  simp only [CtorBundle.rhs, h2, foldr_app_map hApp hConst]

theorem CtorBundle.exists_lift' {c cl} (B : CtorBundle c cl) (ρ : Lift) (ls : List SLevel) :
    ∃ B' : CtorBundle c cl, B'.u = B.u ∧ B'.rhs ls = (B.rhs ls).lift' ρ :=
  CtorBundle.exists_map (F := fun ρ e => e.lift' ρ) (step := Lift.cons)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) B ρ ls

theorem CtorBundle.exists_subst {c cl} (B : CtorBundle c cl) (σ : Subst) (ls : List SLevel) :
    ∃ B' : CtorBundle c cl, B'.u = B.u ∧ B'.rhs ls = (B.rhs ls).subst σ :=
  CtorBundle.exists_map (F := fun σ e => e.subst σ) (step := Subst.lift)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) B σ ls


local notation:65 Γ " ⊢ₛ " e1 " : " A:36 => IsDefEqStrong Γ e1 e1 A
local notation:65 Γ " ⊢ₛ " e1 " ≡ " e2 " : " A:36 => IsDefEqStrong Γ e1 e2 A

/-- `hasType` at a sort-typed judgment is free. -/
theorem IsDefEqStrong.hasTypeS (H : Γ ⊢ₛ e1 ≡ e2 : .sort u) :
    Γ ⊢ₛ e1 : .sort u ∧ Γ ⊢ₛ e2 : .sort u :=
  ⟨.trans .sort H H.symm, .trans .sort H.symm H⟩

theorem IsDefEqStrong.hasType' (hA : Γ ⊢ₛ A : .sort u) (H : Γ ⊢ₛ e1 ≡ e2 : A) :
    Γ ⊢ₛ e1 : A ∧ Γ ⊢ₛ e2 : A :=
  ⟨.trans hA H H.symm, .trans hA H.symm H⟩

/-- Every strong judgment has a sort-typed type (no context hypothesis needed). -/
theorem IsDefEqStrong.isType' (H : Γ ⊢ₛ e1 ≡ e2 : A) : ∃ u, Γ ⊢ₛ A : .sort u := by
  induction H with
  | bvar _ hA => exact ⟨_, hA⟩
  | symm _ ih => exact ih
  | trans hA => exact ⟨_, hA⟩
  | trans' => exact ⟨_, .sort⟩
  | sort => exact ⟨_, .sort⟩
  | const _ _ hT => exact ⟨_, hT⟩
  | appDF _ _ _ _ hBi => exact ⟨_, hBi.hasTypeS.1⟩
  | lamDF hA hB => exact ⟨_, .forallEDF hA.hasTypeS.1 hB hB⟩
  | forallEDF => exact ⟨_, .sort⟩
  | defeqDF hAB => exact ⟨_, hAB.hasTypeS.2⟩
  | beta _ _ _ _ _ _ _ ih => exact ih
  | eta _ _ ih => exact ih
  | proofIrrel hp => exact ⟨_, hp⟩
  | extra _ _ _ _ ih => exact ih

theorem IsDefEqStrong.hasType (H : Γ ⊢ₛ e1 ≡ e2 : A) : Γ ⊢ₛ e1 : A ∧ Γ ⊢ₛ e2 : A :=
  let ⟨_, hA⟩ := H.isType'; IsDefEqStrong.hasType' hA H

theorem IsDefEqStrong.closedN (H : Γ ⊢ₛ e1 ≡ e2 : A) :
    ClosedN e1 Γ.length ∧ ClosedN e2 Γ.length ∧ ClosedN A Γ.length := by
  induction H with
  | bvar h _ ih => exact ⟨h.lt, h.lt, ih.1⟩
  | symm _ ih => exact ⟨ih.2.1, ih.1, ih.2.2⟩
  | trans _ _ _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2.1, ih1.2.2⟩
  | trans' _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2.1, trivial⟩
  | sort => exact ⟨trivial, trivial, trivial⟩
  | const _ _ _ _ _ ihT => exact ⟨trivial, trivial, ihT.1⟩
  | appDF _ _ _ _ _ _ _ ihf iha ihB => exact ⟨⟨ihf.1, iha.1⟩, ⟨ihf.2.1, iha.2.1⟩, ihB.1⟩
  | lamDF _ _ _ _ ihA ihB ih1 _ => exact ⟨⟨ihA.1, ih1.1⟩, ⟨ihA.2.1, ih1.2.1⟩, ihA.1, ihB.1⟩
  | forallEDF _ _ _ ihA ih1 _ => exact ⟨⟨ihA.1, ih1.1⟩, ⟨ihA.2.1, ih1.2.1⟩, trivial⟩
  | defeqDF _ _ ih1 ih2 => exact ⟨ih2.1, ih2.2.1, ih1.2.1⟩
  | beta _ _ _ _ _ _ ih3 ih4 => exact ⟨ih3.1, ih4.1, ih3.2.2⟩
  | eta _ _ ih1 ih2 => exact ⟨ih2.1, ih1.1, ih1.2.2⟩
  | proofIrrel _ _ _ _ ih2 ih3 => exact ⟨ih2.1, ih3.1, ih2.2.2⟩
  | extra _ _ _ _ ih1 ih2 => exact ⟨ih1.1, ih2.1, ih1.2.2⟩

/-! ## Weakening -/

theorem IsDefEqStrong.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ₛ e1 ≡ e2 : A) :
    Γ' ⊢ₛ e1.lift' ρ ≡ e2.lift' ρ : A.lift' ρ := by
  induction H generalizing ρ Γ' with
  | bvar h _ ih => exact .bvar (h.weak' W) (ih W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ _ ih1 ih2 ih3 => exact .trans (ih1 W) (ih2 W) (ih3 W)
  | trans' _ _ ih1 ih2 => exact .trans' (ih1 W) (ih2 W)
  | sort => exact .sort
  | @const c ci Γ ls u h1 h2 _ F _ ihT ihF =>
    have eT := (constType_closed (ls := ls) h1).lift'_eq (ρ := ρ) .zero
    have ihT := ihT W; have ihF := fun cl => ihF cl W
    simp only [eT, lift'_sort] at ihT ihF
    rw [eT]
    refine .const h1 h2 ihT (fun cl => ((F cl).exists_lift' ρ ls).choose) fun cl => ?_
    have ⟨hu, hrhs⟩ := ((F cl).exists_lift' ρ ls).choose_spec
    rw [hu, hrhs]; exact ihF cl
  | appDF _ _ _ _ _ ihA ihB ihf iha ihBi =>
    exact lift'_inst_hi .. ▸ .appDF (ihA W) (ihB W.cons) (ihf W) (iha W)
      (lift'_inst_hi .. ▸ lift'_inst_hi .. ▸ ihBi W)
  | lamDF _ _ _ _ ihA ihB ih1 ih2 => exact .lamDF (ihA W) (ihB W.cons) (ih1 W.cons) (ih2 W.cons)
  | forallEDF _ _ _ ihA ih1 ih2 => exact .forallEDF (ihA W) (ih1 W.cons) (ih2 W.cons)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ _ _ ih1 ih2 ih3 ih4 =>
    rw [lift'_inst_hi, lift'_inst_hi]
    refine .beta (ih1 W.cons) (ih2 W) ?_ ?_
    · rw [← lift'_inst_hi]; exact ih3 W
    · rw [← lift'_inst_hi, ← lift'_inst_hi]; exact ih4 W
  | eta _ _ ih1 ih2 =>
    refine cast ?_ (IsDefEqStrong.eta (ih1 W) (cast ?_ (ih2 W)))
    all_goals simp [lift', ← lift'_comp]
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | @extra df Γ ls h1 h2 _ _ ih1 ih2 =>
    have ⟨hA1, hA2, hA3⟩ := defeq_closed (ls := ls) h1
    rw [hA1.lift'_eq .zero, hA2.lift'_eq .zero, hA3.lift'_eq .zero]
    have ih1 := ih1 W; have ih2 := ih2 W
    rw [hA1.lift'_eq .zero, hA3.lift'_eq .zero] at ih1
    rw [hA2.lift'_eq .zero, hA3.lift'_eq .zero] at ih2
    exact .extra h1 h2 ih1 ih2

theorem IsDefEqStrong.weak0 (H : [] ⊢ₛ e1 ≡ e2 : A) : Γ ⊢ₛ e1 ≡ e2 : A := by
  have ⟨h1, h2, h3⟩ := H.closedN
  have := H.weak' (Ctx.Lift'.nil Γ)
  rwa [h1.lift'_eq .zero, h2.lift'_eq .zero, h3.lift'_eq .zero] at this

/-! ## Inversion for Pi types -/

theorem IsDefEqStrong.forallE_inv' (H : Γ ⊢ₛ e1 ≡ e2 : V)
    (eq : e1 = A.forallE B ∨ e2 = A.forallE B) :
    (∃ u, Γ ⊢ₛ A : .sort u) ∧ ∃ v, A::Γ ⊢ₛ B : .sort v := by
  induction H generalizing A B with
  | symm _ ih => exact ih eq.symm
  | trans _ _ _ _ ih1 ih2
  | trans' _ _ ih1 ih2
  | proofIrrel _ _ _ _ ih1 ih2 =>
    obtain eq | eq := eq
    · exact ih1 (.inl eq)
    · exact ih2 (.inr eq)
  | forallEDF h1 h2 h3 =>
    obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq
    · exact ⟨⟨_, h1.hasTypeS.1⟩, _, h2.hasTypeS.1⟩
    · exact ⟨⟨_, h1.hasTypeS.2⟩, _, h3.hasTypeS.2⟩
  | defeqDF _ _ _ ih2 => exact ih2 eq
  | beta _ _ _ _ _ _ _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih (.inr eq)
  | eta _ _ ih _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih (.inr eq)
  | extra _ _ _ _ ih1 ih2 =>
    obtain eq | eq := eq
    · exact ih1 (.inl eq)
    · exact ih2 (.inl eq)
  | _ => nomatch eq

/-- `[bvar 5] ⊢ bvar 0 : bvar 6` holds weakly (ill-formed context), but no strong
derivation can have the non-closed type `bvar 6` in a context of length 1: the
well-formedness hypothesis of `IsDefEq.strong` cannot be dropped. -/
theorem IsDefEq.strong_counterexample :
    ¬ ∀ {Γ e1 e2 A}, Γ ⊢ e1 ≡ e2 : A → IsDefEqStrong Γ e1 e2 A := fun h =>
  have := (h (IsDefEq.bvar (Γ := [.bvar 5]) .zero)).closedN
  by simp [ClosedN, SExpr.lift] at this

/-! ## Strongly well-formed contexts -/

def CtxStrong : List SExpr → Prop
  | [] => True
  | A :: Γ => CtxStrong Γ ∧ ∃ u, Γ ⊢ₛ A : .sort u

theorem CtxStrong.lookup {Γ} (H : CtxStrong Γ) (h : Lookup Γ i A) : ∃ u, Γ ⊢ₛ A : .sort u := by
  induction h with
  | zero => let ⟨_, _, hA⟩ := H; exact ⟨_, hA.weak' .one⟩
  | succ _ ih => let ⟨H', _⟩ := H; let ⟨_, hA⟩ := ih H'; exact ⟨_, hA.weak' .one⟩

theorem CtxStrong.wf : ∀ {Γ}, CtxStrong Γ → ⊢ Γ
  | [], _ => trivial
  | _ :: _, ⟨h1, _, h2⟩ => ⟨h1.wf, _, h2.defeq⟩

/-! ## Simultaneous substitution for the strong judgment -/

/-- Strong version of `Ctx.SubstEq`: `σ`, `σ'` are pointwise strongly defeq
substitutions from `Γ` into `Γ₀`. The base case is the empty source context
(as in the DomainSemantics reference), so `Ctx.SubstEqS.id` needs `CtxStrong Γ`. -/
inductive Ctx.SubstEqS (Γ₀ : List SExpr) : SExpr.Subst → SExpr.Subst → List SExpr → Prop where
  | nil : Ctx.SubstEqS Γ₀ σ σ' []
  | cons : Ctx.SubstEqS Γ₀ σ.tail σ'.tail Γ →
    Γ ⊢ₛ A : .sort u →
    Γ₀ ⊢ₛ σ.head ≡ σ'.head : A.subst σ.tail →
    Ctx.SubstEqS Γ₀ σ σ' (A :: Γ)

theorem Ctx.SubstEqS.left (W : Ctx.SubstEqS Γ₀ σ σ' Γ) : Ctx.SubstEqS Γ₀ σ σ Γ := by
  induction W with
  | nil => exact .nil
  | cons _ hA hhead ih => exact .cons ih hA hhead.hasType.1

theorem Ctx.SubstEqS.wf (W : Ctx.SubstEqS Γ₀ σ σ' Γ) : CtxStrong Γ := by
  induction W with
  | nil => trivial
  | cons _ hA _ ih => exact ⟨ih, _, hA⟩

theorem Ctx.SubstEqS.lookup (W : Ctx.SubstEqS Γ₀ σ σ' Γ) :
    Lookup Γ i A → Γ₀ ⊢ₛ σ i ≡ σ' i : A.subst σ := by
  intro h
  induction W generalizing i A with
  | nil => nomatch h
  | cons _ _ hhead ih =>
    cases h with
    | zero => rw [lift_subst]; exact hhead
    | succ h => rw [lift_subst]; exact ih h

theorem Ctx.SubstEqS.skip (W : Ctx.SubstEqS Γ₀ σ σ' Γ) :
    Ctx.SubstEqS (B :: Γ₀) (σ.lift_r (.skip .refl)) (σ'.lift_r (.skip .refl)) Γ := by
  induction W with
  | nil => exact .nil
  | cons _ hA hhead ih =>
    refine .cons (Subst.lift_r_tail ▸ Subst.lift_r_tail ▸ ih) hA ?_
    rw [Subst.lift_r_tail]
    have := hhead.weak' (Ctx.Lift'.one (A := B))
    rwa [lift'_subst] at this

theorem Ctx.SubstEqS.lift (W : Ctx.SubstEqS Γ₀ σ σ' Γ)
    (hA : Γ ⊢ₛ A : .sort u) (hA' : Γ₀ ⊢ₛ A.subst σ : .sort u') :
    Ctx.SubstEqS (A.subst σ :: Γ₀) σ.lift σ'.lift (A :: Γ) := by
  refine .cons (Subst.lift_tail_eq σ ▸ Subst.lift_tail_eq σ' ▸ W.skip) hA ?_
  show A.subst σ :: Γ₀ ⊢ₛ .bvar 0 : A.subst σ.lift.tail
  rw [Subst.lift_tail_eq, ← lift'_subst]
  exact .bvar .zero (hA'.weak' .one)

theorem Ctx.SubstEqS.lift_at (W : Ctx.SubstEqS Γ₀ σ σ' Γ)
    (hA : Γ ⊢ₛ A : .sort u) (hX : Γ₀ ⊢ₛ X : .sort u')
    (hAX : Γ₀ ⊢ₛ A.subst σ ≡ X : .sort u'') :
    Ctx.SubstEqS (X :: Γ₀) σ.lift σ'.lift (A :: Γ) := by
  refine .cons (Subst.lift_tail_eq σ ▸ Subst.lift_tail_eq σ' ▸ W.skip) hA ?_
  show X :: Γ₀ ⊢ₛ .bvar 0 : A.subst σ.lift.tail
  rw [Subst.lift_tail_eq, ← lift'_subst]
  exact .defeqDF (hAX.symm.weak' .one) (.bvar .zero (hX.weak' .one))

theorem Ctx.SubstEqS.id : ∀ {Γ}, CtxStrong Γ → Ctx.SubstEqS Γ .id .id Γ
  | [], _ => .nil
  | A :: Γ, ⟨hΓ, _, hA⟩ => by
    refine .cons (Subst.id_tail_eq ▸ (id hΓ).skip) hA ?_
    show A :: Γ ⊢ₛ .bvar 0 : A.subst SExpr.Subst.id.tail
    rw [Subst.id_tail_eq, ← lift'_subst, subst_id]
    exact .bvar .zero (hA.weak' .one)

theorem Ctx.SubstEqS.one (hΓ : CtxStrong Γ) (hA : Γ ⊢ₛ A : .sort u) (ha : Γ ⊢ₛ a ≡ a' : A) :
    Ctx.SubstEqS Γ (.one a) (.one a') (A :: Γ) := by
  refine .cons (σ := .one a) (σ' := .one a') (.id hΓ) hA ?_
  show Γ ⊢ₛ a ≡ a' : A.subst .id
  rw [subst_id]; exact ha

/-- **Simultaneous substitution for the strong judgment**: left/right/cross bundle.
No context hypotheses needed. -/
theorem IsDefEqStrong.substEq' (W : Ctx.SubstEqS Γ₀ σ τ Γ) (H : Γ ⊢ₛ e1 ≡ e2 : A) :
    Γ₀ ⊢ₛ e1.subst σ ≡ e1.subst τ : A.subst σ ∧
    Γ₀ ⊢ₛ e2.subst σ ≡ e2.subst τ : A.subst σ ∧
    Γ₀ ⊢ₛ e1.subst σ ≡ e2.subst τ : A.subst σ := by
  induction H generalizing Γ₀ σ τ with
  | bvar h _ => exact ⟨W.lookup h, W.lookup h, W.lookup h⟩
  | sort => exact ⟨.sort, .sort, .sort⟩
  | symm _ ih =>
    let ⟨l, r, c⟩ := ih W
    let ⟨_, hA⟩ := l.isType'
    exact ⟨r, l, .trans hA r (.trans hA c.symm l)⟩
  | trans _ _ _ _ ih1 ih2 =>
    let ⟨l1, _, c1⟩ := ih1 W
    let ⟨l2, r2, c2⟩ := ih2 W
    let ⟨_, hA⟩ := l1.isType'
    exact ⟨l1, r2, .trans hA c1 (.trans hA l2.symm c2)⟩
  | trans' _ _ ih1 ih2 =>
    let ⟨l1, _, c1⟩ := ih1 W
    let ⟨l2, _, c2⟩ := ih2 W
    have cross := c1.trans' (.trans .sort l2.symm c2)
    exact ⟨l1, .trans .sort ((ih1 W.left).2.2.trans' (ih2 W.left).2.2).symm cross, cross⟩
  | defeqDF _ _ ih1 ih2 =>
    have := (ih1 W.left).2.2
    let ⟨l2, r2, c2⟩ := ih2 W
    exact ⟨.defeqDF this l2, .defeqDF this r2, .defeqDF this c2⟩
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    let ⟨ihp, _, _⟩ := ih1 W
    let ⟨ihh, _, _⟩ := ih2 W
    let ⟨ihh', _, _⟩ := ih3 W
    have hp := ihp.hasTypeS.1
    exact ⟨ihh, ihh', .proofIrrel hp (IsDefEqStrong.hasType' hp ihh).1 (IsDefEqStrong.hasType' hp ihh').2⟩
  | @const c ci Γ ls u h1 h2 _ F _ ihT ihF =>
    have eT := fun θ : Subst => (constType_closed (ls := ls) h1).subst_eq (σ := θ) .zero
    have ihT := (ihT W).1; have ihF := fun cl => (ihF cl W.left).2.2
    simp only [eT, subst_sort] at ihT ihF
    simp only [subst_const, eT]
    have C := IsDefEqStrong.const h1 h2 ihT (fun cl => ((F cl).exists_subst σ ls).choose)
      fun cl => by
        have ⟨hu, hrhs⟩ := ((F cl).exists_subst σ ls).choose_spec
        rw [hu, hrhs]; exact ihF cl
    exact ⟨C, C, C⟩
  | @extra df Γ ls h1 h2 _ _ ih1 ih2 =>
    have ⟨hA1, hA2, hA3⟩ := defeq_closed (ls := ls) h1
    have el : ∀ θ : Subst, (SExpr.mkInst ls df.lhs).subst θ = _ := fun _ => hA1.subst_eq .zero
    have er : ∀ θ : Subst, (SExpr.mkInst ls df.rhs).subst θ = _ := fun _ => hA2.subst_eq .zero
    have et : ∀ θ : Subst, (SExpr.mkInst ls df.type).subst θ = _ := fun _ => hA3.subst_eq .zero
    have ih1 := (ih1 W.left).1; have ih2 := (ih2 W.left).1
    simp only [el, er, et] at ih1 ih2 ⊢
    exact ⟨ih1, ih2, .extra h1 h2 ih1 ih2⟩
  | @appDF Γ A u B v f f' a a' hA _ _ _ _ ihA ihB ihf iha ihBi =>
    have hA' := (ihA W).1.hasTypeS.1
    have W_A_diag := W.left.lift hA hA'
    have hB' := (ihB W_A_diag).1.hasTypeS.1
    have ⟨ihf_l, ihf_r, ihf_c⟩ := ihf W
    have ⟨iha_l, iha_r, iha_c⟩ := iha W
    have ⟨_, _, iha_cleft⟩ := iha W.left
    have ih2_cons : ∀ {x y : SExpr}, Γ₀ ⊢ₛ x ≡ y : A.subst σ →
        Γ₀ ⊢ₛ (B.subst σ.lift).inst x ≡ (B.subst σ.lift).inst y : .sort v := by
      intro x y hxy
      have W_cons : Ctx.SubstEqS Γ₀ (σ.cons x) (σ.cons y) (A :: Γ) :=
        .cons (σ := σ.cons x) (σ' := σ.cons y) W.left hA hxy
      have := (ihB W_cons).1
      rwa [← inst_lift_cons, ← inst_lift_cons] at this
    refine subst_inst ▸ ⟨?_, .defeqDF (ih2_cons iha_cleft.symm) ?_, ?_⟩
    · exact .appDF hA' hB' ihf_l iha_l (ih2_cons iha_l)
    · exact .appDF hA' hB' ihf_r iha_r (ih2_cons iha_r)
    · exact .appDF hA' hB' ihf_c iha_c (ih2_cons iha_c)
  | @lamDF Γ A A' u B v body body' h1 _ _ _ ih1 ih2 ih3 ih4 =>
    let ⟨ihA_l, ihA_r, ihA_c⟩ := ih1 W
    have hA_in_Γ := h1.hasTypeS.1
    have hA'_in_Γ := h1.hasTypeS.2
    have hAA'_σ := (ih1 W.left).2.2
    have W_A := W.lift hA_in_Γ ihA_l.hasTypeS.1
    have W_A_τ := W.lift_at hA_in_Γ ihA_l.hasTypeS.2 ihA_l
    have W_A' := W.lift hA'_in_Γ ihA_r.hasTypeS.1
    have W_A'_τ := W.lift_at hA'_in_Γ ihA_r.hasTypeS.2 ihA_r
    have W_A_to_A'τ := W.lift_at hA_in_Γ ihA_r.hasTypeS.2 ihA_c
    have W_left_A'σ := W.left.lift_at hA_in_Γ ihA_r.hasTypeS.1 hAA'_σ
    have hB := (ih2 W_A).1.hasTypeS.1
    have hB_at_A'σ := (ih2 W_left_A'σ).1.hasTypeS.1
    let ⟨ih3body_l, _, ih3body_c⟩ := ih3 W_A
    have ih3body_l_at_Aτ := (ih3 W_A_τ).1
    have ih3body_c_at_A'τ := (ih3 W_A_to_A'τ).2.2
    let ⟨_, ih4body_r, _⟩ := ih4 W_A'
    have ih4body_r_at_A'τ := (ih4 W_A'_τ).2.1
    refine ⟨?_, .defeqDF (hAA'_σ.symm.forallEDF hB_at_A'σ hB) ?_, ?_⟩
    · exact .lamDF ihA_l hB ih3body_l ih3body_l_at_Aτ
    · exact .lamDF ihA_r hB_at_A'σ ih4body_r ih4body_r_at_A'τ
    · exact .lamDF ihA_c hB ih3body_c ih3body_c_at_A'τ
  | @forallEDF Γ A A' u body body' v h1 _ _ ih1 ih2 ih3 =>
    let ⟨ihA_l, ihA_r, ihA_c⟩ := ih1 W
    have hA_in_Γ := h1.hasTypeS.1
    have hA'_in_Γ := h1.hasTypeS.2
    have W_A := W.lift hA_in_Γ ihA_l.hasTypeS.1
    have W_A' := W.lift hA'_in_Γ ihA_r.hasTypeS.1
    have W_A_τ := W.lift_at hA_in_Γ ihA_l.hasTypeS.2 ihA_l
    have W_A'_τ := W.lift_at hA'_in_Γ ihA_r.hasTypeS.2 ihA_r
    have W_A_to_A'τ := W.lift_at hA_in_Γ ihA_r.hasTypeS.2 ihA_c
    let ⟨ihB_l, _, ihB_c⟩ := ih2 W_A
    have ihB_l_at_Aτ := (ih2 W_A_τ).1
    have ihB_c_at_A'τ := (ih2 W_A_to_A'τ).2.2
    let ⟨_, ihB'_r, _⟩ := ih3 W_A'
    have ihB'_r_at_A'τ := (ih3 W_A'_τ).2.1
    exact ⟨.forallEDF ihA_l ihB_l ihB_l_at_Aτ, .forallEDF ihA_r ihB'_r ihB'_r_at_A'τ,
      .forallEDF ihA_c ihB_c ihB_c_at_A'τ⟩
  | @beta A Γ e B e' _ he' _ _ ih2 ih3 ih4 ih5 =>
    have ⟨_, hA⟩ := he'.isType'
    have ih4_l := (ih4 W).1
    have ih5_l := (ih5 W).1
    have he'σ := (ih3 W.left).1
    have ⟨_, hAσ⟩ := he'σ.isType'
    have heσ := (ih2 (W.left.lift hA hAσ)).1
    have happσ := (ih4 W.left).1
    have heinstσ := (ih5 W.left).1
    have H_σ : Γ₀ ⊢ₛ (SExpr.app (.lam A e) e').subst σ ≡ (e.inst e').subst σ :
        (B.inst e').subst σ := by
      show Γ₀ ⊢ₛ SExpr.app (.lam (A.subst σ) (e.subst σ.lift)) (e'.subst σ) ≡ _ : _
      rw [show (e.inst e').subst σ = (e.subst σ.lift).inst (e'.subst σ) from subst_inst,
          show (B.inst e').subst σ = (B.subst σ.lift).inst (e'.subst σ) from subst_inst]
      refine .beta heσ he'σ ?_ ?_
      · rw [show (B.subst σ.lift).inst (e'.subst σ) = (B.inst e').subst σ from subst_inst.symm]
        exact happσ
      · rw [show (B.subst σ.lift).inst (e'.subst σ) = (B.inst e').subst σ from subst_inst.symm,
            show (e.subst σ.lift).inst (e'.subst σ) = (e.inst e').subst σ from subst_inst.symm]
        exact heinstσ
    have ⟨_, hT⟩ := ih4_l.isType'
    exact ⟨ih4_l, ih5_l, .trans hT H_σ ih5_l⟩
  | @eta Γ e A B _ _ ih1 ih2 =>
    have ih1_l := (ih1 W).1
    have ih2_l := (ih2 W).1
    have he_σ := (ih1 W.left).1
    have hlam_σ := (ih2 W.left).1
    have h_lam_eq : (SExpr.lam A (.app e.lift (.bvar 0))).subst σ =
        .lam (A.subst σ) (.app (e.subst σ).lift (.bvar 0)) := by
      show SExpr.lam (A.subst σ) (.app (e.lift.subst σ.lift) ((SExpr.bvar 0).subst σ.lift)) = _
      rw [lift_subst_lift]; rfl
    have H_σ : Γ₀ ⊢ₛ (SExpr.lam A (.app e.lift (.bvar 0))).subst σ ≡ e.subst σ :
        (SExpr.forallE A B).subst σ := h_lam_eq ▸ .eta he_σ (h_lam_eq ▸ hlam_σ)
    have ⟨_, hT⟩ := ih1_l.isType'
    exact ⟨ih2_l, ih1_l, .trans hT H_σ ih1_l⟩

theorem IsDefEqStrong.subst (W : Ctx.SubstEqS Γ₀ σ σ' Γ) (H : Γ ⊢ₛ e1 ≡ e2 : A) :
    Γ₀ ⊢ₛ e1.subst σ ≡ e2.subst σ' : A.subst σ :=
  (H.substEq' W).2.2

theorem IsDefEqStrong.instDF (hΓ : CtxStrong Γ) (hA : Γ ⊢ₛ A : .sort u)
    (hf : A::Γ ⊢ₛ f ≡ f' : B) (ha : Γ ⊢ₛ a ≡ a' : A) :
    Γ ⊢ₛ f.inst a ≡ f'.inst a' : B.inst a :=
  hf.subst (.one hΓ hA ha)

theorem IsDefEqStrong.defeqDF_l (hΓ : CtxStrong Γ)
    (h1 : Γ ⊢ₛ A ≡ A' : .sort u) (h2 : A::Γ ⊢ₛ e1 ≡ e2 : B) : A'::Γ ⊢ₛ e1 ≡ e2 : B := by
  have W : Ctx.SubstEqS (A'::Γ) .id .id (A::Γ) := by
    refine .cons (Subst.id_tail_eq ▸ (Ctx.SubstEqS.id hΓ).skip) h1.hasTypeS.1 ?_
    show A' :: Γ ⊢ₛ .bvar 0 : A.subst SExpr.Subst.id.tail
    rw [Subst.id_tail_eq, ← lift'_subst, subst_id]
    exact .defeqDF (h1.weak' .one).symm (.bvar .zero (h1.hasTypeS.2.weak' .one))
  have := h2.subst W
  rwa [subst_id, subst_id, subst_id] at this

/-! ## Derived rules with the weak premises -/

theorem IsDefEqStrong.appDF₀ (hΓ : CtxStrong Γ)
    (hf : Γ ⊢ₛ f ≡ f' : .forallE A B) (ha : Γ ⊢ₛ a ≡ a' : A) :
    Γ ⊢ₛ .app f a ≡ .app f' a' : B.inst a :=
  let ⟨_, h3⟩ := hf.isType'
  let ⟨⟨_, hA⟩, _, hB⟩ := h3.forallE_inv' (.inl rfl)
  .appDF hA hB hf ha (.instDF hΓ hA hB ha)

theorem IsDefEqStrong.lamDF₀ (hΓ : CtxStrong Γ)
    (hA : Γ ⊢ₛ A ≡ A' : .sort u) (hbody : A::Γ ⊢ₛ body ≡ body' : B) :
    Γ ⊢ₛ .lam A body ≡ .lam A' body' : .forallE A B :=
  let ⟨_, hB⟩ := hbody.isType'
  .lamDF hA hB hbody (hA.defeqDF_l hΓ hbody)

theorem IsDefEqStrong.forallEDF₀ (hΓ : CtxStrong Γ)
    (hA : Γ ⊢ₛ A ≡ A' : .sort u) (hbody : A::Γ ⊢ₛ body ≡ body' : .sort v) :
    Γ ⊢ₛ .forallE A body ≡ .forallE A' body' : .sort (.imax u v) :=
  .forallEDF hA hbody (hA.defeqDF_l hΓ hbody)

theorem IsDefEqStrong.beta₀ (hΓ : CtxStrong Γ) (he : A::Γ ⊢ₛ e : B) (he' : Γ ⊢ₛ e' : A) :
    Γ ⊢ₛ .app (.lam A e) e' ≡ e.inst e' : B.inst e' :=
  have ⟨_, hA⟩ := he'.isType'
  .beta he he' (.appDF₀ hΓ (.lamDF₀ hΓ hA he) he') (.instDF hΓ hA he he')

theorem IsDefEqStrong.eta₀ (hΓ : CtxStrong Γ) (he : Γ ⊢ₛ e : .forallE A B) :
    Γ ⊢ₛ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B := by
  let ⟨_, hAB⟩ := he.isType'
  let ⟨⟨_, hA⟩, _, _⟩ := hAB.forallE_inv' (.inl rfl)
  have : A::Γ ⊢ₛ .app e.lift (.bvar 0) : (B.lift' (.cons (.skip .refl))).inst (.bvar 0) :=
    .appDF₀ ⟨hΓ, _, hA⟩ (he.weak' .one) (.bvar .zero (hA.weak' .one))
  rw [lift_cons_skip_inst_bvar0] at this
  exact .eta he (.lamDF₀ hΓ hA this)

/-! ## Environment hypothesis and the main theorem -/

/-- Strong typing of the environment: the constant-type expression, its ctor
bundle equations, and the lhs/rhs of each defeq are strongly typed in `[]`. -/
structure EnvStrongS : Prop where
  const : ∀ {c ci ls}, env.constants c = some ci → ls.length = ci.uvars →
    ∃ u, [] ⊢ₛ mkInst ls ci.type : .sort u
  ctor : ∀ {c ci ls}, env.constants c = some ci → ls.length = ci.uvars →
    ∀ cl : CtorBundle.IsCtor c,
      ∃ B : CtorBundle c cl, [] ⊢ₛ mkInst ls ci.type ≡ B.rhs ls : .sort B.u
  defeq : ∀ {df ls}, env.defeqs df → ls.length = df.uvars →
    [] ⊢ₛ .mkInst ls df.lhs : .mkInst ls df.type ∧
    [] ⊢ₛ .mkInst ls df.rhs : .mkInst ls df.type

theorem IsDefEq.strongS (envIH : EnvStrongS) (hΓ : CtxStrong Γ) (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ ⊢ₛ e1 ≡ e2 : A := by
  induction H with
  | bvar h => let ⟨_, hA⟩ := hΓ.lookup h; exact .bvar h hA
  | symm _ ih => exact (ih hΓ).symm
  | trans _ _ ih1 ih2 => let ⟨_, hA⟩ := (ih1 hΓ).isType'; exact .trans hA (ih1 hΓ) (ih2 hΓ)
  | trans' _ _ ih1 ih2 => exact .trans' (ih1 hΓ) (ih2 hΓ)
  | sort => exact .sort
  | const h1 h2 =>
    have ⟨_, hT⟩ := envIH.const h1 h2
    exact .const h1 h2 hT.weak0 (fun cl => (envIH.ctor h1 h2 cl).choose)
      fun cl => (envIH.ctor h1 h2 cl).choose_spec.weak0
  | appDF _ _ ih1 ih2 => exact .appDF₀ hΓ (ih1 hΓ) (ih2 hΓ)
  | lamDF _ _ ih1 ih2 => exact .lamDF₀ hΓ (ih1 hΓ) (ih2 ⟨hΓ, _, (ih1 hΓ).hasTypeS.1⟩)
  | forallEDF _ _ ih1 ih2 => exact .forallEDF₀ hΓ (ih1 hΓ) (ih2 ⟨hΓ, _, (ih1 hΓ).hasTypeS.1⟩)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 hΓ) (ih2 hΓ)
  | beta _ _ ih1 ih2 => exact .beta₀ hΓ (ih1 ⟨hΓ, (ih2 hΓ).isType'⟩) (ih2 hΓ)
  | eta _ ih => exact .eta₀ hΓ (ih hΓ)
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 hΓ) (ih2 hΓ) (ih3 hΓ)
  | extra h1 h2 =>
    have ⟨hl, hr⟩ := envIH.defeq h1 h2
    exact .extra h1 h2 hl.weak0 hr.weak0

theorem CtxStrong.of_wf (envIH : EnvStrongS) : ∀ {Γ}, ⊢ Γ → CtxStrong Γ
  | [], _ => trivial
  | _ :: _, ⟨hΓ, _, hA⟩ => ⟨of_wf envIH hΓ, _, hA.strongS envIH (of_wf envIH hΓ)⟩

/-! ## Translating the VExpr strong judgment

`VEnv.IsDefEqStrong.constDF` carries the typing of the constant's type but nothing about
constructor telescopes, while `IsDefEqStrong.const` demands a *strong* `SExpr` equation
`T ≡ (F cl).rhs ls : sort (F cl).u` for every ctor classification. The translation is therefore
parameterized by a `CtorProvider` that produces this bundle from the data available at the
`constDF` case. -/

/-- What the translation needs at each `constDF`. `vs` are the (well-formed) `VLevel`
representatives of the `SLevel` list, `u` is the sort of the constant's type *in the derivation
being translated*. -/
def CtorProvider : Prop :=
  ∀ {Γ : List SExpr} {c : Name} {ci : VConstant} {vs : List VLevel} {u : VLevel},
    env.constants c = some ci → (∀ l ∈ vs, l.WF univs) → vs.length = ci.uvars →
    env.HasType univs [] (ci.type.instL vs) (.sort u) →
    Γ ⊢ₛ mkInst (vs.map SLevel.mk) ci.type : .sort (SLevel.mk u) →
    ∀ cl : CtorBundle.IsCtor c, ∃ B : CtorBundle c cl,
      Γ ⊢ₛ mkInst (vs.map SLevel.mk) ci.type ≡ B.rhs (vs.map SLevel.mk) : .sort B.u

omit [Params] in
theorem VExpr.liftN_one_one (B : VExpr) : B.liftN 1 1 = B.lift' (.cons (.skip .refl)) := by
  rw [← VExpr.lift'_consN_skipN]; rfl

/-- Strong-to-strong translation. -/
theorem _root_.Lean4Lean.VEnv.IsDefEqStrong.mkS (hctor : CtorProvider)
    (H : Params.env.IsDefEqStrong Params.univs Γ e₁ e₂ A)
    (hΓ : OnCtx Γ (fun _ A => A.LevelWF Params.univs)) :
    IsDefEqStrong (Γ.map mk) (mk e₁) (mk e₂) (mk A) := by
  induction H with
  | bvar h _ _ ih => exact .bvar (SExpr.Lookup.mkS h) (ih hΓ)
  | symm _ ih => exact .symm (ih hΓ)
  | trans _ _ ih1 ih2 => let ⟨_, hA⟩ := (ih1 hΓ).isType'; exact .trans hA (ih1 hΓ) (ih2 hΓ)
  | @sortDF l l' Γ hl hl' h =>
    change IsDefEqStrong _ (.sort (SLevel.mk _)) (.sort (SLevel.mk _)) (.sort (SLevel.mk _))
    have hu := SLevel.mk_eq hl hl' h
    have hus : SLevel.mk l.succ = (SLevel.mk l').succ := by rw [SLevel.mk_succ hl, hu]
    rw [hu, hus]
    exact .sort
  | @constDF c ci ls ls' u Γ h1 h2 h3 h4 h5 _ h7 _ _ ih8 =>
    change IsDefEqStrong _ (.const c (ls.map SLevel.mk)) (.const c (ls'.map SLevel.mk))
      (mk (ci.type.instL ls))
    have hls := SLevel.map_mk_eq h2 h3 h5
    have e1 : mk (ci.type.instL ls) = mkInst (ls.map SLevel.mk) ci.type := (mkInst_map_mk h2).symm
    have e2 : mk (ci.type.instL ls') = mkInst (ls.map SLevel.mk) ci.type := by
      rw [← mkInst_map_mk h3, hls]
    have hT := ih8 hΓ
    rw [e1, e2] at hT
    have hT' : _ ⊢ₛ mkInst (ls.map SLevel.mk) ci.type : .sort (SLevel.mk u) := hT.hasTypeS.1
    have hV : env.HasType univs [] (ci.type.instL ls) (.sort u) := h7.defeq.hasType.1
    rw [e1, ← hls]
    exact .const h1 (by simpa using h4) hT'
      (fun cl => (hctor h1 h2 h4 hV hT' cl).choose) fun cl => (hctor h1 h2 h4 hV hT' cl).choose_spec
  | appDF _ _ hA _ _ _ _ ihA ihB ihf iha ihBi =>
    have hAwf := (hA.defeq.levelWF hΓ).1
    have hBi := ihBi hΓ
    simp only [mk, mk_instExpr] at hBi
    simpa only [mk, mk_instExpr] using
      IsDefEqStrong.appDF (ihA hΓ) (ihB ⟨hΓ, hAwf⟩) (ihf hΓ) (iha hΓ) hBi
  | lamDF _ _ hAA' _ _ _ _ ihAA' ihB _ ihbody ihbody' =>
    have hAwf := (hAA'.defeq.levelWF hΓ).1
    have hA'wf := (hAA'.defeq.levelWF hΓ).2.1
    exact .lamDF (ihAA' hΓ) (ihB ⟨hΓ, hAwf⟩) (ihbody ⟨hΓ, hAwf⟩) (ihbody' ⟨hΓ, hA'wf⟩)
  | forallEDF hu hv hAA' _ _ ihAA' ih1 ih2 =>
    have hAwf := (hAA'.defeq.levelWF hΓ).1
    have hA'wf := (hAA'.defeq.levelWF hΓ).2.1
    simpa only [mk, SLevel.mk_imax hu hv] using
      IsDefEqStrong.forallEDF (ihAA' hΓ) (ih1 ⟨hΓ, hAwf⟩) (ih2 ⟨hΓ, hA'wf⟩)
  | defeqDF _ _ _ ih1 ih2 => exact .defeqDF (ih1 hΓ) (ih2 hΓ)
  | beta _ _ hA _ _ _ _ _ ihA ihB ihe ihe' ihBi ihei =>
    have hAwf := (hA.defeq.levelWF hΓ).1
    have hΓ' : OnCtx (_ :: _) (fun _ A => A.LevelWF Params.univs) := ⟨hΓ, hAwf⟩
    have hBi := ihBi hΓ; have hei := ihei hΓ
    simp only [mk, mk_instExpr] at hBi hei ⊢
    exact .beta (ihe hΓ') (ihe' hΓ)
      (.appDF (ihA hΓ) (ihB hΓ') (.lamDF (ihA hΓ) (ihB hΓ') (ihe hΓ') (ihe hΓ')) (ihe' hΓ) hBi) hei
  | @eta Γ A u B v e _ _ hA _ _ _ _ _ ihA ihB ihB' ihe ihe' ihA' =>
    have hAwf := (hA.defeq.levelWF hΓ).1
    have hΓ' : OnCtx (A :: Γ) (fun _ A => A.LevelWF Params.univs) := ⟨hΓ, hAwf⟩
    have hΓ'' : OnCtx (A.lift :: A :: Γ) (fun _ A => A.LevelWF Params.univs) := ⟨hΓ', hAwf.liftN⟩
    have h1 := ihA' hΓ'
    have h2 := ihB' hΓ''
    have h3 := ihe' hΓ'
    have h4 := ihB hΓ'
    simp only [List.map_cons, mk, mk_lift, VExpr.liftN_one_one, mk_lift'] at h1 h2 h3 h4 ⊢
    have hbody := IsDefEqStrong.appDF h1 h2 h3 (.bvar .zero h1)
      (lift_cons_skip_inst_bvar0.symm ▸ h4)
    rw [lift_cons_skip_inst_bvar0] at hbody
    exact .eta (ihe hΓ) (.lamDF (ihA hΓ) h4 hbody hbody)
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    simpa only [mk, SLevel.mk_zero] using IsDefEqStrong.proofIrrel (ih1 hΓ) (ih2 hΓ) (ih3 hΓ)
  | @extra df ls u Γ h1 h2 h3 _ _ _ _ _ _ _ _ _ ih8 ih9 =>
    have hl := ih8 hΓ; have hr := ih9 hΓ
    simp only [← mkInst_map_mk h2] at hl hr ⊢
    exact .extra h1 (by simpa using h3) hl hr

/-! ## `EnvStrongS` from `Params.henv` plus a ctor provider -/

/-- Strong typing of a constant's type at `VLevel` representatives, from `Params.henv`. -/
theorem constType_strong (hctor : CtorProvider) (h1 : env.constants c = some ci)
    (hvs : ∀ l ∈ vs, l.WF univs) :
    ∃ u : VLevel, env.HasType univs [] (ci.type.instL vs) (.sort u) ∧
      [] ⊢ₛ mkInst (vs.map SLevel.mk) ci.type : .sort (SLevel.mk u) := by
  have ⟨u, hu⟩ := Params.henv.constWF h1
  have hS := (VEnv.IsDefEq.strong Params.henv (by trivial) hu).instL hvs
  have := hS.mkS hctor (by trivial)
  rw [mkInst_map_mk hvs]
  exact ⟨_, VEnv.IsDefEq.instL hvs hu, this⟩

theorem EnvStrongS.of_provider (hctor : CtorProvider) : EnvStrongS where
  const := fun {c ci ls} h1 _ => by
    obtain ⟨vs, hvs, rfl⟩ := SLevel.exists_map_mk ls
    have ⟨_, _, h⟩ := constType_strong hctor h1 hvs
    exact ⟨_, h⟩
  ctor := fun {c ci ls} h1 h2 cl => by
    obtain ⟨vs, hvs, rfl⟩ := SLevel.exists_map_mk ls
    have ⟨_, hV, hT⟩ := constType_strong hctor h1 hvs
    exact hctor h1 hvs (by simpa using h2) hV hT cl
  defeq := fun {df ls} h1 _ => by
    obtain ⟨vs, hvs, rfl⟩ := SLevel.exists_map_mk ls
    have ⟨hl, hr⟩ := Params.henv.defEqWF h1
    have hl' := ((VEnv.IsDefEq.strong Params.henv (by trivial) hl).instL hvs).mkS hctor (by trivial)
    have hr' := ((VEnv.IsDefEq.strong Params.henv (by trivial) hr).instL hvs).mkS hctor (by trivial)
    simp only [mkInst_map_mk hvs]
    exact ⟨hl', hr'⟩

theorem SLevel.mk_ne_zero (hu : u.WF univs) (h : ∀ ns, u.eval ns ≠ 0) : SLevel.mk u ≠ .zero := by
  intro h'
  have := congrFun (congrArg Subtype.val h') []
  rw [SLevel.mk_val hu] at this
  exact h [] this

/-- The provider given by the syntactic `Params` fields: the ctor equation is reflexivity. -/
theorem CtorProvider.syn : CtorProvider := by
  intro Γ c ci vs u h1 hvs hlen hV hT cl
  obtain ⟨I, Ts, args, hTs, hI, heq⟩ := ctor_syn cl.cl.2.2 cl.cl.2.1 h1
  have hcl : cl.cl.1.arity = _ := rfl
  have hu : u.WF univs := (hV.levelWF ⟨⟩).2.2
  have hrhs : mkInst (vs.map SLevel.mk) ci.type =
      (Ts.map fun T => mk (T.instL vs)).foldr .forallE
        ((args.map fun A => mk (A.instL vs)).foldr (fun A acc => acc.app A)
          (.const I (vs.map SLevel.mk))) := by
    rw [mkInst_map_mk hvs, heq, mk_instL_foldr_forallE, mk_instL_foldr_app]
    simp only [VExpr.instL, mk, VLevel.inst_map_id hlen]
  refine ⟨⟨I, Ts.map fun T => mk (T.instL vs), args.map fun A => mk (A.instL vs), SLevel.mk u,
    by simp [hTs], by simpa using hI, SLevel.mk_ne_zero hu (ctor_sort cl.cl.2.2 cl.cl.2.1 h1 hvs hlen hV)⟩, ?_⟩
  show _ ⊢ₛ _ ≡ (Ts.map fun T => mk (T.instL vs)).foldr .forallE
    ((args.map fun A => mk (A.instL vs)).foldr (fun A acc => acc.app A)
      (.const I (vs.map SLevel.mk))) : _
  rw [← hrhs]; exact hT


/-- Strong typing of the whole environment, from `Params.henv` and the syntactic ctor fields. -/
theorem Params.envStrongS : EnvStrongS := .of_provider CtorProvider.syn

/-- Every weak derivation in a well-formed context is strong. -/
theorem IsDefEq.strong (hΓ : ⊢ Γ) (H : Γ ⊢ e1 ≡ e2 : A) : IsDefEqStrong Γ e1 e2 A :=
  H.strongS Params.envStrongS (.of_wf Params.envStrongS hΓ)

theorem IsDefEq.isType (hΓ : ⊢ Γ) (H : Γ ⊢ e1 ≡ e2 : A) : ∃ u, Γ ⊢ A : .sort u :=
  let ⟨u, h⟩ := (H.strong hΓ).isType'; ⟨u, h.defeq⟩

theorem IsDefEq.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ' ⊢ e1.lift' ρ ≡ e2.lift' ρ : A.lift' ρ := by
  induction H generalizing ρ Γ' with
  | bvar h => refine .bvar (h.weak' W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | trans' _ _ ih1 ih2 => exact .trans' (ih1 W) (ih2 W)
  | sort => exact .sort
  | const h1 h2 => rw [(henv.closedC h1).mkInstS.lift'_eq .zero]; exact .const h1 h2
  | appDF _ _ ih1 ih2 => exact SExpr.lift'_inst_hi .. ▸ .appDF (ih1 W) (ih2 W)
  | lamDF _ _ ih1 ih2 => exact .lamDF (ih1 W) (ih2 W.cons)
  | forallEDF _ _ ih1 ih2 => exact .forallEDF (ih1 W) (ih2 W.cons)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ ih1 ih2 =>
    rw [SExpr.lift'_inst_hi, SExpr.lift'_inst_hi]
    exact .beta (ih1 W.cons) (ih2 W)
  | eta _ ih => refine cast ?_ (IsDefEq.eta (ih W)); congr 1; simp [← SExpr.lift'_comp]
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
    rw [hA1.mkInstS.lift'_eq .zero, hA2.mkInstS.lift'_eq .zero, hA3.mkInstS.lift'_eq .zero]
    exact .extra h1 h2

/--
`Ctx.SubstEq Γ₀ σ σ' Γ`: `σ` and `σ'` are pointwise definitionally equal substitutions
from `Γ` into `Γ₀`. The base case is the identity on a common suffix, and `weak` lets the
target context grow, which is what makes `lift` (going under a binder) derivable.
-/
inductive Ctx.SubstEq : List SExpr → SExpr.Subst → SExpr.Subst → List SExpr → Prop where
  | nil : Ctx.SubstEq Γ₀ .id .id Γ₀
  | weak : Ctx.SubstEq Γ₀ σ σ' Γ →
    Ctx.SubstEq (B :: Γ₀) (σ.lift_r (.skip .refl)) (σ'.lift_r (.skip .refl)) Γ
  | cons : Ctx.SubstEq Γ₀ σ.tail σ'.tail Γ →
    Γ ⊢ A : .sort u →
    Γ₀ ⊢ σ.head ≡ σ'.head : A.subst σ.tail →
    Ctx.SubstEq Γ₀ σ σ' (A :: Γ)

theorem Ctx.SubstEq.left (W : Ctx.SubstEq Γ₀ σ σ' Γ) : Ctx.Subst (· ⊢ · : ·) Γ₀ σ Γ := by
  induction W with
  | nil => exact .id .bvar fun W h => h.weak' W
  | weak _ ih => exact ih.lift_r (fun W h => h.weak' W) .one
  | cons _ _ h ih => exact .cons ih h.hasType.1

theorem Ctx.SubstEq.lookup (W : Ctx.SubstEq Γ₀ σ σ' Γ) :
    Lookup Γ i A → Γ₀ ⊢ σ i ≡ σ' i : A.subst σ := by
  induction W generalizing i A with
  | nil => intro h; rw [subst_id]; exact IsDefEq.bvar h
  | @weak _ _ _ _ B _ ih =>
    intro h
    have := (ih h).weak' (Ctx.Lift'.one (A := B))
    rwa [lift'_subst] at this
  | cons _ _ h ih =>
    intro hl
    cases hl with
    | zero => rw [lift_subst]; exact h
    | succ hl => rw [lift_subst]; exact ih hl

theorem Ctx.SubstEq.lift (W : Ctx.SubstEq Γ₀ σ σ' Γ) (hA : Γ ⊢ A : .sort u) :
    Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift σ'.lift (A :: Γ) := by
  refine .cons (Subst.lift_tail_eq σ ▸ Subst.lift_tail_eq σ' ▸ W.weak) hA ?_
  show (A.subst σ :: Γ₀) ⊢ .bvar 0 ≡ .bvar 0 : A.subst σ.lift.tail
  rw [Subst.lift_tail_eq, ← lift'_subst]
  exact .bvar .zero

theorem Ctx.SubstEq.strong (W : Ctx.SubstEq Γ₀ σ σ' Γ)
    (hΓ : ⊢ Γ) (hΓ₀ : ⊢ Γ₀) : Ctx.SubstEqS Γ₀ σ σ' Γ := by
  induction W with
  | nil => exact .id (.of_wf Params.envStrongS hΓ)
  | weak _ ih => exact .skip (ih hΓ hΓ₀.1)
  | cons _ hA hhead ih =>
    exact .cons (ih hΓ.1 hΓ₀) (hA.strong hΓ.1)
      (hhead.strong hΓ₀)


/-- With the identity-based `nil`, well-formedness of the target context gives that of the
source context. -/
theorem Ctx.SubstEq.wf (W : Ctx.SubstEq Γ₀ σ σ' Γ) (hΓ₀ : ⊢ Γ₀) : ⊢ Γ := by
  induction W with
  | nil => exact hΓ₀
  | weak _ ih => exact ih hΓ₀.1
  | cons _ hA _ ih => exact ⟨ih hΓ₀, _, hA⟩

/-- Simultaneous substitution of a defeq pair of substitutions into a defeq. -/
theorem IsDefEq.subst (hΓ₀ : ⊢ Γ₀)
    (W : Ctx.SubstEq Γ₀ σ σ' Γ) (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ₀ ⊢ e1.subst σ ≡ e2.subst σ' : A.subst σ :=
  ((H.strong (W.wf hΓ₀)).subst (W.strong (W.wf hΓ₀) hΓ₀)).defeq

theorem Ctx.SubstEq.symm (W : Ctx.SubstEq Γ₀ σ σ' Γ) (hΓ₀ : ⊢ Γ₀) : Ctx.SubstEq Γ₀ σ' σ Γ := by
  induction W with
  | nil => exact .nil
  | weak _ ih => exact .weak (ih hΓ₀.1)
  | cons W hA h ih => exact .cons (ih hΓ₀) hA (.defeqDF (.subst hΓ₀ W hA) h.symm)


/-! ### `defeqDF_l'` directly, with no hypotheses -/

/-- `k`-fold `lift`. -/
def liftK (e : SExpr) : Nat → SExpr
  | 0 => e
  | k+1 => (liftK e k).lift

theorem liftK_lift (e : SExpr) : ∀ k, liftK e.lift k = liftK e (k+1)
  | 0 => rfl
  | k+1 => congrArg SExpr.lift (liftK_lift e k)

theorem liftK_sort : ∀ k, liftK (.sort u) k = .sort u
  | 0 => rfl
  | k+1 => congrArg SExpr.lift (liftK_sort k)

theorem IsDefEq.weak_append (H : Γ ⊢ e1 ≡ e2 : A) :
    ∀ Δ : List SExpr, Δ ++ Γ ⊢ liftK e1 Δ.length ≡ liftK e2 Δ.length : liftK A Δ.length
  | [] => H
  | _ :: Δ => (H.weak_append Δ).weak' .one

theorem Lookup.append_self : ∀ Δ : List SExpr, Lookup (Δ ++ A :: Γ) Δ.length (liftK A (Δ.length+1))
  | [] => .zero
  | _ :: Δ => .succ (append_self Δ)

theorem Lookup.append_cons : ∀ Δ : List SExpr, Lookup (Δ ++ A :: Γ) i B →
    Lookup (Δ ++ A' :: Γ) i B ∨ (i = Δ.length ∧ B = liftK A (Δ.length+1))
  | [], h => by
    cases h with
    | zero => exact .inr ⟨rfl, rfl⟩
    | succ h => exact .inl (.succ h)
  | _ :: Δ, h => by
    cases h with
    | zero => exact .inl .zero
    | succ h =>
      obtain h | ⟨rfl, rfl⟩ := append_cons Δ h
      · exact .inl (.succ h)
      · exact .inr ⟨rfl, rfl⟩

theorem IsDefEq.defeqDF_l' (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h2 : Δ ++ A :: Γ ⊢ e1 ≡ e2 : B) : Δ ++ A' :: Γ ⊢ e1 ≡ e2 : B := by
  generalize hΓ' : Δ ++ A :: Γ = Γ' at h2
  induction h2 generalizing Δ with
  | bvar h =>
    subst hΓ'
    obtain h | ⟨rfl, rfl⟩ := Lookup.append_cons Δ h
    · exact .bvar h
    · have := ((h1.weak' (Ctx.Lift'.one (A := A'))).weak_append Δ)
      rw [liftK_lift, liftK_lift, lift'_sort, liftK_sort] at this
      exact .defeqDF this.symm (.bvar (Lookup.append_self Δ))
  | symm _ ih => exact .symm (ih hΓ')
  | trans _ _ ih1 ih2 => exact .trans (ih1 hΓ') (ih2 hΓ')
  | trans' _ _ ih1 ih2 => exact .trans' (ih1 hΓ') (ih2 hΓ')
  | sort => exact .sort
  | const h1 h2 => exact .const h1 h2
  | appDF _ _ ih1 ih2 => exact .appDF (ih1 hΓ') (ih2 hΓ')
  | lamDF _ _ ih1 ih2 => exact .lamDF (ih1 hΓ') (ih2 (Δ := _ :: Δ) (by rw [← hΓ']; rfl))
  | forallEDF _ _ ih1 ih2 => exact .forallEDF (ih1 hΓ') (ih2 (Δ := _ :: Δ) (by rw [← hΓ']; rfl))
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 hΓ') (ih2 hΓ')
  | beta _ _ ih1 ih2 => exact .beta (ih1 (Δ := _ :: Δ) (by rw [← hΓ']; rfl)) (ih2 hΓ')
  | eta _ ih => exact .eta (ih hΓ')
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 hΓ') (ih2 hΓ') (ih3 hΓ')
  | extra h1 h2 => exact .extra h1 h2


theorem IsDefEq.defeqDF_l (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h2 : A::Γ ⊢ e1 ≡ e2 : B) : A'::Γ ⊢ e1 ≡ e2 : B :=
  .defeqDF_l' (Δ := []) h1 h2

theorem HasType.defeq_l (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h2 : A::Γ ⊢ e : B) : A'::Γ ⊢ e : B := h1.defeqDF_l h2

variable (DefEq : List SExpr → SExpr → SExpr → SExpr → Prop) in
structure WithLift (Γ : List SExpr) (e1 e2 A : SExpr) : Prop where
  defeq' {{Δ ρ e1' e2' A'}} : Ctx.Lift' ρ Δ Γ →
    e1 = .lift' e1' ρ → e2 = .lift' e2' ρ → A = .lift' A' ρ → DefEq Δ e1' e2' A'
  left' {{Δ ρ e1' A'}} : Ctx.Lift' ρ Δ Γ → e1 = .lift' e1' ρ → A = .lift' A' ρ → DefEq Δ e1' e1' A'
  right' {{Δ ρ e2' A'}} : Ctx.Lift' ρ Δ Γ → e2 = .lift' e2' ρ → A = .lift' A' ρ → DefEq Δ e2' e2' A'

def IsDefEqLift := WithLift IsDefEq
scoped notation:65 Γ " ⊢ " e " :↑ " A:36 => IsDefEqLift Γ e e A
scoped notation:65 Γ " ⊢ " e1 " ≡ " e2 " :↑ " A:36 => IsDefEqLift Γ e1 e2 A

theorem WithLift.imp
    (imp : ∀ {Γ e1 e2 A}, DefEq Γ e1 e2 A → DefEq' Γ e1 e2 A)
    (H : WithLift DefEq Γ e1 e2 A) : WithLift DefEq' Γ e1 e2 A where
  defeq' _ _ _ _ _ W' h1 h2 h3 := imp (H.defeq' W' h1 h2 h3)
  left' _ _ _ _ W' h1 hA := imp (H.left' W' h1 hA)
  right' _ _ _ _ W' h1 hA := imp (H.right' W' h1 hA)

theorem WithLift.refl
    (refl : ∀ {ρ Δ e' A'}, Ctx.Lift' ρ Δ Γ →
      e = .lift' e' ρ → A = .lift' A' ρ → DefEq Δ e' e' A')
    : WithLift DefEq Γ e e A where
  defeq' _ _ _ _ _ W := by rintro rfl he rfl; cases SExpr.lift'_inj.1 he; exact refl W rfl rfl
  left' _ _ _ _ W := by rintro rfl rfl; exact refl W rfl rfl
  right' _ _ _ _ W := by rintro rfl rfl; exact refl W rfl rfl

theorem WithLift.weak'
    (weak : ∀ {ρ Γ Δ e1 e2 A}, Ctx.Lift' ρ Γ Δ → DefEq Γ e1 e2 A →
      DefEq Δ (e1.lift' ρ) (e2.lift' ρ) (A.lift' ρ))
    (W : Ctx.Lift' ρ Γ Δ) (H : WithLift DefEq Γ e1 e2 A) :
    WithLift DefEq Δ (e1.lift' ρ) (e2.lift' ρ) (A.lift' ρ) where
  defeq' Δ' ρ' e1' e2' A' W' h1 h2 hA := by
    have ⟨Δ₀, I⟩ := Ctx.Inter.mk W W'
    obtain ⟨e1, rfl, rfl⟩ := lift_eq_lift h1
    obtain ⟨e2, rfl, rfl⟩ := lift_eq_lift h2
    obtain ⟨A, rfl, rfl⟩ := lift_eq_lift hA
    exact weak I.diff (H.defeq' I.symm.diff rfl rfl rfl)
  left' Δ' ρ' e1' A' W' h1 hA := by
    have ⟨Δ₀, I⟩ := Ctx.Inter.mk W W'
    obtain ⟨e1, rfl, rfl⟩ := lift_eq_lift h1
    obtain ⟨A, rfl, rfl⟩ := lift_eq_lift hA
    exact weak I.diff (H.left' I.symm.diff rfl rfl)
  right' Δ' ρ' e1' A' W' h1 hA := by
    have ⟨Δ₀, I⟩ := Ctx.Inter.mk W W'
    obtain ⟨e1, rfl, rfl⟩ := lift_eq_lift h1
    obtain ⟨A, rfl, rfl⟩ := lift_eq_lift hA
    exact weak I.diff (H.right' I.symm.diff rfl rfl)

theorem IsDefEqLift.weak' : Ctx.Lift' ρ Γ Δ → Γ ⊢ e1 ≡ e2 :↑ A →
    Δ ⊢ e1.lift' ρ ≡ e2.lift' ρ :↑ A.lift' ρ := WithLift.weak' IsDefEq.weak'

theorem IsDefEqLift.subst : Ctx.Subst HasType Δ σ Γ → Γ ⊢ e1 ≡ e2 :↑ A →
    Δ ⊢ e1.subst σ ≡ e2.subst σ :↑ A.subst σ := sorry

theorem WithLift.weak'_inv (W : Ctx.Lift' ρ Γ Δ)
    (H : WithLift DefEq Δ (e1.lift' ρ) (e2.lift' ρ) (A.lift' ρ)) : WithLift DefEq Γ e1 e2 A where
  defeq' Δ' ρ' _ _ _ W' := by
    rintro rfl rfl rfl
    simp only [← SExpr.lift'_comp] at H
    exact H.defeq' (W'.comp W) rfl rfl rfl
  left' Δ' ρ' _ _ W' := by
    rintro rfl rfl
    simp only [← SExpr.lift'_comp] at H
    exact H.left' (W'.comp W) rfl rfl
  right' Δ' ρ' _ _ W' := by
    rintro rfl rfl
    simp only [← SExpr.lift'_comp] at H
    exact H.right' (W'.comp W) rfl rfl

nonrec theorem IsDefEqLift.weak'_inv : Ctx.Lift' ρ Γ Δ →
    Δ ⊢ e1.lift' ρ ≡ e2.lift' ρ :↑ A.lift' ρ → Γ ⊢ e1 ≡ e2 :↑ A := .weak'_inv

theorem WithLift.symm
    (symm : ∀ {Γ e1 e2 A}, DefEq Γ e1 e2 A → DefEq Γ e2 e1 A)
    (H : WithLift DefEq Γ e1 e2 A) : WithLift DefEq Γ e2 e1 A where
  defeq' _ _ _ _ _ W' h1 h2 h3 := symm (H.defeq' W' h2 h1 h3)
  left' _ _ _ _ W' h1 hA := H.right' W' h1 hA
  right' _ _ _ _ W' h1 hA := H.left' W' h1 hA

nonrec theorem IsDefEqLift.symm : Γ ⊢ e1 ≡ e2 :↑ A → Γ ⊢ e2 ≡ e1 :↑ A := .symm .symm

theorem WithLift.left (H : WithLift DefEq Γ e1 e2 A) : WithLift DefEq Γ e1 e1 A :=
  .refl (H.left' ·)

theorem WithLift.right (H : WithLift DefEq Γ e1 e2 A) : WithLift DefEq Γ e2 e2 A :=
  .refl (H.right' ·)

theorem IsDefEqLift.left (H : Γ ⊢ e1 ≡ e2 :↑ A) : Γ ⊢ e1 :↑ A where
  defeq' _ _ _ _ _ W' := by rintro rfl he hA; exact SExpr.lift'_inj.1 he ▸ H.left' W' rfl hA
  left' := H.left'
  right' := H.left'

theorem WithLift.defeq (H : WithLift DefEq Γ e1 e2 A) : DefEq Γ e1 e2 A :=
  H.defeq' .refl SExpr.lift'_refl.symm SExpr.lift'_refl.symm SExpr.lift'_refl.symm

nonrec theorem IsDefEqLift.defeq (H : Γ ⊢ e1 ≡ e2 :↑ A) : Γ ⊢ e1 ≡ e2 : A := H.defeq

variable (Γ₀ : List SExpr) in
inductive IsDefEqCtx : List SExpr → List SExpr → Prop
  | zero : IsDefEqCtx Γ₀ Γ₀
  | succ :  IsDefEqCtx Γ₁ Γ₂ → Γ₁ ⊢ A₁ ≡ A₂ : .sort u → IsDefEqCtx (A₁ :: Γ₁) (A₂ :: Γ₂)

theorem IsDefEq.defeqDFC' (h1 : IsDefEqCtx Γ₀ Γ₁ Γ₂)
    (h2 : Δ ++ Γ₁ ⊢ e₁ ≡ e₂ : A) : Δ ++ Γ₂ ⊢ e₁ ≡ e₂ : A := by
  induction h1 generalizing e₁ e₂ A Δ with
  | zero => exact h2
  | @succ _ _ _ A₂ _ _ AA ih =>
    simpa using ih (Δ := Δ ++ [A₂]) (by simpa using AA.defeqDF_l' h2)

theorem IsDefEq.defeqDFC (h1 : IsDefEqCtx Γ₀ Γ₁ Γ₂)
    (h2 : Γ₁ ⊢ e₁ ≡ e₂ : A) : Γ₂ ⊢ e₁ ≡ e₂ : A := .defeqDFC' (Δ := []) h1 h2

omit [Params] in
theorem _root_.Lean4Lean.Subpattern.varN_const (H : Subpattern p (.varN (.const c) n)) :
    ∃ n, p = .varN (.const c) n := by
  generalize eq : Pattern.varN (.const c) n = p' at H
  induction H generalizing n with
  | refl => exact ⟨_, eq.symm⟩
  | appL | appR => cases n <;> cases eq
  | varL _ ih => cases n <;> cases eq; exact ih rfl

theorem _root_.Lean4Lean.Pattern.MatchesS.determ
    (h1 : Pattern.MatchesS p e m1 m2) (h2 : Pattern.MatchesS p e m1' m2') :
    m1 = m1' ∧ m2 = m2' := by
  induction h1 generalizing m1' with
  | const => let .const := h2; simp
  | app l1 l2 ih1 ih2 => let .app r1 r2 := h2; simp [ih1 r1, ih2 r2]; rfl
  | var l1 ih1 => let .var r1 := h2; simp [ih1 r1]

theorem _root_.Lean4Lean.Pattern.matchesS_inter {p q : Pattern} {e : SExpr}
    {m1 m3 : List SLevel} {m2 : p.Path → SExpr} {m4 : q.Path → SExpr}
    (hp : p.MatchesS e m1 m2) (hq : q.MatchesS e m3 m4) : ∃ r, p.inter q = some r := by
  induction hp generalizing q m3 m4 with
  | const => cases hq; simp [Pattern.inter]
  | var _ ih =>
    cases hq with
    | var h => obtain ⟨_, h⟩ := ih h; simp [Pattern.inter, h]
    | app h _ => obtain ⟨_, h⟩ := ih h; simp [Pattern.inter, h]
  | app _ _ ihf iha =>
    cases hq with
    | var h => obtain ⟨_, h⟩ := ihf h; simp [Pattern.inter, h]
    | app hf ha =>
      obtain ⟨_, hf⟩ := ihf hf; obtain ⟨_, ha⟩ := iha ha
      simp [Pattern.inter, hf, ha]

theorem _root_.Lean4Lean.Pattern.MatchesS.varN_const_lam
    (h : Pattern.MatchesS (.varN (.const c) n) (.lam A b) m1 m2) : False := by
  cases n <;> simp only [Pattern.varN] at h <;> nomatch h

omit [Params] in
theorem _root_.Lean4Lean.Pattern.ne_app_self {f a : Pattern} : f ≠ .app f a := by
  intro h; have := congrArg sizeOf h; simp at this; omega

omit [Params] in
theorem _root_.Lean4Lean.Pattern.ne_app_self_r {f a : Pattern} : a ≠ .app f a := by
  intro h; have := congrArg sizeOf h; simp at this

/-- In a simple pattern the only `app` subpattern is the pattern itself. -/
theorem Params.simple_app (H : Pat p r) (h : Subpattern (.app p₁ p₂) p) : .app p₁ p₂ = p := by
  obtain ⟨_|_, rfl⟩ := pat_simple H <;> cases h
  · rfl
  · obtain ⟨n, h⟩ := Subpattern.varN_const ‹_›; cases n <;> cases h
  · obtain ⟨n, h⟩ := Subpattern.varN_const ‹_›; cases n <;> cases h

theorem _root_.Lean4Lean.Pattern.matchesS_lift' {p : Pattern} {e : SExpr} {m1 m2'} :
    p.MatchesS (e.lift' ρ) m1 m2' ↔
    ∃ m2, p.MatchesS e m1 m2 ∧ ∀ x, m2' x = (m2 x).lift' ρ := by
  constructor
  · intro h; generalize eq : e.lift' ρ = e' at h
    induction h generalizing e with
    | const => cases e <;> cases eq; exact ⟨_, .const, nofun⟩
    | var _ ih =>
      cases e <;> cases eq
      have ⟨_, l1, l2⟩ := ih rfl
      refine ⟨_, .var l1, ?_⟩
      rintro (_|_) <;> solve_by_elim
    | app _ _ ih1 ih2 =>
      cases e <;> cases eq
      have ⟨_, l1, l2⟩ := ih1 rfl
      have ⟨_, r1, r2⟩ := ih2 rfl
      refine ⟨_, .app l1 r1, ?_⟩
      rintro (_|_) <;> solve_by_elim
  · intro ⟨m2, h1, h2⟩
    induction h1 with
    | const => exact Pattern.MatchesS.congr .const nofun
    | var _ ih =>
      refine Pattern.MatchesS.congr (ih (h2 <| some ·)).var fun x => ?_
      cases x <;> simp [h2 none]
    | app _ _ ih1 ih2 =>
      refine Pattern.MatchesS.congr ((ih1 (h2 <| .inl ·)).app (ih2 (h2 <| .inr ·))) fun x => ?_
      cases x <;> rfl

theorem _root_.Lean4Lean.Pattern.MatchesS.subst {p : Pattern} {e : SExpr} {m1 m2}
    (H : p.MatchesS e m1 m2) : p.MatchesS (e.subst σ) m1 fun x => (m2 x).subst σ := by
  induction H with
  | const => exact Pattern.MatchesS.congr .const nofun
  | var _ ih => refine Pattern.MatchesS.congr ih.var fun x => ?_; cases x <;> rfl
  | app _ _ ih1 ih2 => refine Pattern.MatchesS.congr (ih1.app ih2) fun x => ?_; cases x <;> rfl

theorem _root_.Lean4Lean.Pattern.RHS.applyS_lift' {p : Pattern} {m1 m2} (r : p.RHS) :
    (r.applyS m1 m2).lift' ρ = r.applyS m1 fun x => (m2 x).lift' ρ := by
  induction r with
  | fixed c h => exact h.mkInstS.lift'_eq .zero
  | var => rfl
  | app _ _ ih1 ih2 => simp only [Pattern.RHS.applyS, SExpr.lift', ih1, ih2]

theorem _root_.Lean4Lean.Pattern.RHS.applyS_subst {p : Pattern} {m1 m2} (r : p.RHS) :
    (r.applyS m1 m2).subst σ = r.applyS m1 fun x => (m2 x).subst σ := by
  induction r with
  | fixed c h => exact h.mkInstS.subst_eq nofun
  | var => rfl
  | app _ _ ih1 ih2 => simp only [Pattern.RHS.applyS, SExpr.subst, ih1, ih2]

theorem _root_.Lean4Lean.Pattern.Check.defeqsS_lift' {p : Pattern} {m1 m2} (ck : p.Check) :
    ck.defeqsS m1 (fun x => (m2 x).lift' ρ) =
    (ck.defeqsS m1 m2).map fun x => (x.1.lift' ρ, x.2.lift' ρ) := by
  induction ck <;> simp [Pattern.Check.defeqsS, Pattern.RHS.applyS_lift', *]

theorem _root_.Lean4Lean.Pattern.Check.defeqsS_subst {p : Pattern} {m1 m2} (ck : p.Check) :
    ck.defeqsS m1 (fun x => (m2 x).subst σ) =
    (ck.defeqsS m1 m2).map fun x => (x.1.subst σ, x.2.subst σ) := by
  induction ck <;> simp [Pattern.Check.defeqsS, Pattern.RHS.applyS_subst, *]

omit [Params] in
/-- Packaging the side-condition list of `WHRed.extra`: a list `dfs` of typed defeqs whose
untyped projection is `l` exists iff every pair in `l` is defeq at some type. -/
theorem exists_dfs {α β : Type} {P : β → α → Prop} :
    ∀ {l : List β}, (∀ x ∈ l, ∃ A, P x A) →
    ∃ dfs : List (α × β), dfs.map (·.2) = l ∧ ∀ A x, (A, x) ∈ dfs → P x A
  | [], _ => ⟨[], rfl, nofun⟩
  | x :: l, h => by
    obtain ⟨A, hA⟩ := h x (.head _)
    obtain ⟨dfs, h1, h2⟩ := exists_dfs fun y hy => h y (.tail _ hy)
    refine ⟨(A, x) :: dfs, by simp [h1], fun A' y h => ?_⟩
    rcases List.mem_cons.1 h with h | h
    · cases h; exact hA
    · exact h2 _ _ h

/-- `e` is a proper prefix of the left-hand side of some rewrite rule, whose next argument is
a pattern position (for a simple iota pattern `rec a₁ … aₘ (ctor b₁ … bₙ)`: `e = rec a₁ … aₘ`,
so the next argument is the major premise). -/
def IsMajorPremise (e : SExpr) : Prop :=
  ∃ p, (∃ r, Pat p r) ∧ ∃ p₁ p₂, Subpattern (.app p₁ p₂) p ∧ ∃ m1 m2, p₁.MatchesS e m1 m2

/-- The intended use: `f` matches the recursor prefix `p₁` of an iota rule `app p₁ p₂`. -/
theorem IsMajorPremise.mk {p₁ p₂ : Pattern} {r} {m1 : List SLevel} {m2 : p₁.Path → SExpr}
    (h : Pat (.app p₁ p₂) r) (hm : p₁.MatchesS f m1 m2) : IsMajorPremise f :=
  ⟨_, ⟨_, h⟩, _, _, .refl, _, _, hm⟩

theorem IsMajorPremise.lift' {e ρ} : IsMajorPremise (e.lift' ρ) ↔ IsMajorPremise e := by
  constructor <;> intro ⟨_, h1, _, _, h2, _, _, h3⟩
  · let ⟨_, h4, _⟩ := Pattern.matchesS_lift'.1 h3
    exact ⟨_, h1, _, _, h2, _, _, h4⟩
  · exact ⟨_, h1, _, _, h2, _, _, Pattern.matchesS_lift'.2 ⟨_, h3, fun _ => rfl⟩⟩

theorem IsMajorPremise.subst : IsMajorPremise e → IsMajorPremise (e.subst σ)
  | ⟨_, h1, _, _, h2, _, _, h3⟩ => ⟨_, h1, _, _, h2, _, _, h3.subst⟩

theorem IsMajorPremise.lam : ¬IsMajorPremise (.lam A e)
  | ⟨_, _, _, _, _, _, _, h⟩ => nomatch h

theorem IsMajorPremise.sort : ¬IsMajorPremise (.sort u)
  | ⟨_, _, _, _, _, _, _, h⟩ => nomatch h

theorem IsMajorPremise.forallE : ¬IsMajorPremise (.forallE A B)
  | ⟨_, _, _, _, _, _, _, h⟩ => nomatch h

scoped notation:65 Γ " ⊢ " e1 " ⤳ " e2:36 => WHRed Γ e1 e2
/-- Weak-head reduction: `app`/`beta`/`extra` plus the `major` rule, which reduces the
argument of a matched rule prefix (reduction in major-premise position). -/
inductive WHRed (Γ : List SExpr) : SExpr → SExpr → Prop where
  | app : Γ ⊢ f ⤳ f' → Γ ⊢ .app f a ⤳ .app f' a
  | major : IsMajorPremise f → Γ ⊢ a ⤳ a' → Γ ⊢ .app f a ⤳ .app f a'
  | beta : Γ ⊢ .app (.lam A e) a ⤳ e.inst a
  | extra : Pat p r → p.MatchesS e m1 m2 → (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 →
    (∀ a b A, (A, a, b) ∈ dfs → Γ ⊢ a ≡ b : A) → Γ ⊢ e ⤳ r.1.applyS m1 m2

/-- `extra` with the side conditions stated directly on `defeqsS`. -/
theorem WHRed.extra' {p : Pattern} {r : p.RHS × p.Check} {m1 : List SLevel} {m2 : p.Path → SExpr}
    (h1 : Pat p r) (h2 : p.MatchesS e m1 m2)
    (h3 : ∀ x : SExpr × SExpr, x ∈ r.2.defeqsS m1 m2 → ∃ A, Γ ⊢ x.1 ≡ x.2 : A) :
    Γ ⊢ e ⤳ r.1.applyS m1 m2 :=
  let ⟨_, h4, h5⟩ := exists_dfs h3
  .extra h1 h2 h4 fun _ _ _ h => h5 _ _ h

theorem WHRed.extra_inv {p : Pattern} {r : p.RHS × p.Check} {m1 : List SLevel} {m2 : p.Path → SExpr}
    {dfs : List (SExpr × SExpr × SExpr)} (h3 : dfs.map (·.2) = r.2.defeqsS m1 m2)
    (h4 : ∀ a b A, (A, a, b) ∈ dfs → Γ ⊢ a ≡ b : A) :
    ∀ x : SExpr × SExpr, x ∈ r.2.defeqsS m1 m2 → ∃ A, Γ ⊢ x.1 ≡ x.2 : A := by
  intro x hx; rw [← h3] at hx
  obtain ⟨⟨A, a, b⟩, hm, rfl⟩ := List.mem_map.1 hx
  exact ⟨A, h4 _ _ _ hm⟩

/-- Substitution. The `extra` case needs the side-condition defeqs to be substitutable, which
is abstracted as `hdf` (for `Ctx.SubstEq Δ σ σ Γ` it is `IsDefEq.subst`). -/
theorem WHRed.subst
    (hdf : ∀ {a b A}, Γ ⊢ a ≡ b : A → Δ ⊢ a.subst σ ≡ b.subst σ : A.subst σ)
    (H : Γ ⊢ e1 ⤳ e2) : Δ ⊢ e1.subst σ ⤳ e2.subst σ := by
  induction H with
  | app _ ih => exact .app ih
  | major h1 _ ih => exact .major h1.subst ih
  | beta => exact subst_inst ▸ .beta
  | extra h1 h2 h3 h4 =>
    rw [Pattern.RHS.applyS_subst]
    refine .extra' h1 h2.subst fun x hx => ?_
    rw [Pattern.Check.defeqsS_subst] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have ⟨A, h⟩ := WHRed.extra_inv h3 h4 y hy
    exact ⟨_, hdf h⟩

theorem WHRed.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ⤳ e2) :
    Γ' ⊢ e1.lift' ρ ⤳ e2.lift' ρ := by
  induction H with
  | app _ ih => exact .app ih
  | major h1 _ ih => exact .major (IsMajorPremise.lift'.2 h1) ih
  | beta => rw [SExpr.lift'_inst_hi]; exact .beta
  | extra h1 h2 h3 h4 =>
    rw [Pattern.RHS.applyS_lift']
    refine .extra' h1 (Pattern.matchesS_lift'.2 ⟨_, h2, fun _ => rfl⟩) fun x hx => ?_
    rw [Pattern.Check.defeqsS_lift'] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have ⟨A, h⟩ := WHRed.extra_inv h3 h4 y hy
    exact ⟨_, h.weak' W⟩

set_option linter.unusedVariables false in
/-- Inverse weakening. The `extra` case needs strengthening of the side-condition defeqs,
abstracted as `hinv` (the `SExpr` analogue of `IsDefEqU.weak'_iff` in the `VExpr` theory). -/
theorem WHRed.weakU_inv (W : Ctx.Lift' ρ Γ Γ')
    (hinv : ∀ {a b A}, Γ' ⊢ a.lift' ρ ≡ b.lift' ρ : A → ∃ A', Γ ⊢ a ≡ b : A')
    (H : Γ' ⊢ e1.lift' ρ ⤳ e2') : ∃ e2, e2' = e2.lift' ρ ∧ Γ ⊢ e1 ⤳ e2 := by
  generalize he : e1.lift' ρ = e1' at H
  induction H generalizing e1 with
  | app h1 ih => let .app .. := e1; cases he; obtain ⟨_, rfl, a1⟩ := ih rfl; exact ⟨_, rfl, .app a1⟩
  | major h1 h2 ih =>
    let .app .. := e1; cases he; obtain ⟨_, rfl, a1⟩ := ih rfl
    exact ⟨_, rfl, .major (IsMajorPremise.lift'.1 h1) a1⟩
  | beta =>
    let .app e1 _ := e1; let .lam .. := e1; cases he
    simp [← SExpr.lift'_inst_hi, SExpr.lift'_inj]; exact .beta
  | extra h1 h2 h3 h4 =>
    subst he
    obtain ⟨m2, h5, h6⟩ := Pattern.matchesS_lift'.1 h2; cases funext h6
    refine ⟨_, (Pattern.RHS.applyS_lift' _).symm, .extra' h1 h5 fun x hx => ?_⟩
    have ⟨A, h⟩ := WHRed.extra_inv h3 h4 (x.1.lift' ρ, x.2.lift' ρ) <| by
      rw [Pattern.Check.defeqsS_lift']; exact List.mem_map.2 ⟨x, hx, rfl⟩
    exact hinv h

def WHNF (Γ : List SExpr) (e : SExpr) := ∀ e', ¬Γ ⊢ e ⤳ e'

theorem WHNF.lam : WHNF Γ (.lam A e) := nofun
theorem WHNF.sort : WHNF Γ (.sort A) := nofun
theorem WHNF.forallE : WHNF Γ (.forallE A B) := nofun

/-- A term matching a *strict* subpattern of a rule is in whnf. The `major` case is closed by
`pat_uniq` alone: the major-premise prefix `f` matches the prefix `p₁'` of some rule
`p' = app p₁' p₂'`, and also `varN (const c) n`; so `p'` intersects the strict subpattern
`varN (const c) (n+1)` of `p`, forcing `p' = varN … (n+1)`, which is a `var`, contradicting
`p' = app _ _`. -/
theorem WHNF.subpattern
    (h1 : Pat p r) (h2 : Subpattern p₁ p) (h3 : p₁ ≠ p) (h4 : p₁.MatchesS e m1 m2) :
    WHNF Γ e := by
  intro _ H2
  obtain ⟨c, n, rfl⟩ : ∃ c n, p₁ = .varN (.const c) n := by
    obtain ⟨_|_, rfl⟩ := pat_simple h1 <;> cases h2 <;>
      first | cases h3 rfl | exact ⟨_, Subpattern.varN_const ‹_›⟩
  induction H2 generalizing n with
  | app r1 ih =>
    let n+1 := n; let .var h4 := h4
    refine ih _ (.trans (.varL .refl) h2) ?_ h4
    rintro rfl; have := h2.sizeOf_le; simp [Pattern.varN] at this; omega
  | major r1 r2 =>
    let n+1 := n; let .var h4 := h4
    obtain ⟨p', ⟨_, h1'⟩, p₁', p₂', h2', _, _, h3'⟩ := r1
    cases Params.simple_app h1' h2'
    have ⟨q, a1⟩ := Pattern.matchesS_inter h3' h4
    have a2 : (Pattern.app p₁' p₂').inter (.varN (.const c) (n+1)) = some (.app q p₂') := by
      simp [Pattern.varN, Pattern.inter, a1]
    obtain ⟨rfl, eq, -⟩ := pat_uniq h1 h1' h2 a2
    simp [Pattern.varN] at eq
  | beta => let n+1 := n; let .var h4 := h4; exact h4.varN_const_lam
  | extra r1 r2 =>
    have ⟨_, a1⟩ := Pattern.matchesS_inter r2 h4
    obtain ⟨rfl, eq, _⟩ := pat_uniq h1 r1 h2 a1
    exact h3 eq.symm

theorem IsMajorPremise.whnf : IsMajorPremise e → WHNF Γ e := by
  rintro ⟨p, ⟨_, h1⟩, p₁, p₂, h2, _, _, h3⟩
  refine .subpattern h1 (.trans (.appL .refl) h2) ?_ h3
  rintro rfl; exact Pattern.ne_app_self (h2.antisymm (.appL .refl))

theorem WHNF.pat_app_l (h1 : Pat p r) (h2 : p.MatchesS (.app f a) m1 m2) : WHNF Γ f := by
  obtain ⟨_|_, rfl⟩ := pat_simple h1
  · let .app h3 _ := h2
    exact WHNF.subpattern h1 (.appL .refl) Pattern.ne_app_self h3
  · nomatch h2

theorem WHNF.pat_app_r (h1 : Pat p r) (h2 : p.MatchesS (.app f a) m1 m2) : WHNF Γ a := by
  obtain ⟨_|_, rfl⟩ := pat_simple h1
  · let .app _ h3 := h2
    exact WHNF.subpattern h1 (.appR .refl) Pattern.ne_app_self_r h3
  · nomatch h2

theorem WHRed.determ (H1 : Γ ⊢ e ⤳ e₁) (H2 : Γ ⊢ e ⤳ e₂) : e₁ = e₂ := by
  induction H1 generalizing e₂ with
  | app l1 ih =>
    cases H2 with
    | app r1 => cases ih r1; rfl
    | major r1 => cases r1.whnf _ l1
    | beta => cases WHNF.lam _ l1
    | extra r1 r2 => cases WHNF.pat_app_l r1 r2 _ l1
  | major l1 l2 ih =>
    cases H2 with
    | app r1 => cases l1.whnf _ r1
    | major _ r2 => cases ih r2; rfl
    | beta => cases l1.lam
    | extra r1 r2 => cases WHNF.pat_app_r r1 r2 _ l2
  | beta =>
    cases H2 with
    | app r1 => cases WHNF.lam _ r1
    | major r1 => cases r1.lam
    | beta => rfl
    | extra r1 r2 =>
      obtain ⟨_|_, rfl⟩ := pat_simple r1
      · let .app r3 _ := r2; exact r3.varN_const_lam.elim
      · nomatch r2
  | extra l1 l2 =>
    cases H2 with
    | beta =>
      obtain ⟨_|_, rfl⟩ := pat_simple l1
      · let .app l3 _ := l2; exact l3.varN_const_lam.elim
      · nomatch l2
    | app r1 => cases WHNF.pat_app_l l1 l2 _ r1
    | major r1 r2 => cases WHNF.pat_app_r l1 l2 _ r2
    | extra r1 r2 =>
      have ⟨_, a1⟩ := Pattern.matchesS_inter r2 l2
      obtain ⟨rfl, -, ⟨⟩⟩ := pat_uniq l1 r1 .refl a1
      obtain ⟨rfl, rfl⟩ := l2.determ r2; rfl

def WHRedS (Γ : List SExpr) : SExpr → SExpr → Prop := ReflTransGen (WHRed Γ)
scoped notation:65 Γ " ⊢ " e1 " ⤳* " e2:36 => WHRedS Γ e1 e2

theorem WHRedS.subst
    (hdf : ∀ {a b A}, Γ ⊢ a ≡ b : A → Δ ⊢ a.subst σ ≡ b.subst σ : A.subst σ)
    (H : Γ ⊢ e1 ⤳* e2) : Δ ⊢ e1.subst σ ⤳* e2.subst σ := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.subst hdf)

theorem WHRedS.defeq (H : Γ ⊢ e1 ⤳* e2) (he : Γ ⊢ e1 : A) : Γ ⊢ e1 ≡ e2 : A := sorry

theorem WHRedS.weak' (W : Ctx.Lift' ρ Γ Δ) (H : Γ ⊢ e1 ⤳* e2) :
    Δ ⊢ e1.lift' ρ ⤳* e2.lift' ρ := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.weak' W)

theorem WHRedS.app (H : Γ ⊢ e1 ⤳* e2) : Γ ⊢ e1.app a ⤳* e2.app a := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih h2.app

theorem WHRedS.major (H1 : IsMajorPremise f) (H : Γ ⊢ a ⤳* a') :
    Γ ⊢ f.app a ⤳* f.app a' := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.major H1)

theorem WHRedS.weakU_inv (W : Ctx.Lift' ρ Γ Δ)
    (hinv : ∀ {a b A}, Δ ⊢ a.lift' ρ ≡ b.lift' ρ : A → ∃ A', Γ ⊢ a ≡ b : A')
    (H : Δ ⊢ e1.lift' ρ ⤳* e2') : ∃ e2, e2' = e2.lift' ρ ∧ Γ ⊢ e1 ⤳* e2 := by
  induction H with
  | rfl => exact ⟨_, rfl, .rfl⟩
  | tail _ h2 ih =>
    obtain ⟨_, rfl, a1⟩ := ih
    obtain ⟨_, rfl, a2⟩ := h2.weakU_inv W hinv
    exact ⟨_, rfl, .tail a1 a2⟩

theorem WHRedS.determ_l (H1 : Γ ⊢ e ⤳* e₁) (H2 : Γ ⊢ e ⤳* e₂) (W2 : WHNF Γ e₂) : Γ ⊢ e₁ ⤳* e₂ := by
  induction H1 using ReflTransGen.headIndOn generalizing e₂ with
  | rfl => exact H2
  | head l1 l2 ih =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => cases W2 _ l1
    | head r1 r2 => cases l1.determ r1; exact ih r2 W2

theorem WHNF.whRedS (W : WHNF Γ e) (H : Γ ⊢ e ⤳* e') : e = e' := by
  cases H using ReflTransGen.headIndOn with
  | rfl => rfl
  | head h1 => cases W _ h1

theorem WHRedS.determ
    (H1 : Γ ⊢ e ⤳* e₁) (W1 : WHNF Γ e₁)
    (H2 : Γ ⊢ e ⤳* e₂) (W2 : WHNF Γ e₂) : e₁ = e₂ := W1.whRedS (H1.determ_l H2 W2)

scoped notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
inductive ParRed : List SExpr → SExpr → SExpr → Prop where
  | bvar : Γ ⊢ .bvar i ≫ .bvar i
  | sort : Γ ⊢ .sort u ≫ .sort u
  | const : Γ ⊢ .const c ls ≫ .const c ls
  | app : Γ ⊢ f ≫ f' → Γ ⊢ a ≫ a' → Γ ⊢ .app f a ≫ .app f' a'
  | lam : Γ ⊢ A ≫ A' → A::Γ ⊢ body ≫ body' → Γ ⊢ .lam A body ≫ .lam A' body'
  | forallE : Γ ⊢ A ≫ A' → A::Γ ⊢ B ≫ B' → Γ ⊢ .forallE A B ≫ .forallE A' B'
  | beta : A::Γ ⊢ e₁ ≫ e₁' → Γ ⊢ e₂ ≫ e₂' → Γ ⊢ .app (.lam A e₁) e₂ ≫ e₁'.inst e₂'
  | extra : Pat p r → p.MatchesS e m1 m2 → (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 →
    (∀ a b A, (A, a, b) ∈ dfs → Γ ⊢ a ≡ b : A) →
    (∀ a, Γ ⊢ m2 a ≫ m2' a) → Γ ⊢ e ≫ r.1.applyS m1 m2'

theorem ParRed.weak' (W : Ctx.Lift' ρ Γ Γ') :
    Γ ⊢ e1 ≫ e2 → Γ' ⊢ e1.lift' ρ ≫ e2.lift' ρ
  | .bvar => .bvar
  | .sort => .sort
  | .const => .const
  | .app h1 h2 => .app (h1.weak' W) (h2.weak' W)
  | .lam h1 h2 => .lam (h1.weak' W) (h2.weak' W.cons)
  | .forallE h1 h2 => .forallE (h1.weak' W) (h2.weak' W.cons)
  | .beta h1 h2 => by rw [SExpr.lift'_inst_hi]; exact (h1.weak' W.cons).beta (h2.weak' W)
  | .extra h1 h2 h3 h4 h5 => sorry

def ParRedS (Γ : List SExpr) : SExpr → SExpr → Prop := ReflTransGen (ParRed Γ)
scoped notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => ParRedS Γ e1 e2

theorem ParRedS.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≫* e2) :
    Γ' ⊢ e1.lift' ρ ≫* e2.lift' ρ := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.weak' W)

scoped notation:65 Γ " ⊢ " e1 " ▷ " e2:36 => InferType Γ e1 e2
inductive InferType : List SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ .bvar i ▷ A
  | sort : Γ ⊢ .sort u ▷ .sort (.succ u)
  | const : env.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ .const c ls ▷ SExpr.mkInst ls ci.type
  | app : Γ ⊢ f ▷ F → Γ ⊢ F ⤳* .forallE A B → Γ ⊢ a :↑ A → Γ ⊢ .app f a ▷ B.inst a
  | lam : Γ ⊢ A :↑ .sort u → A::Γ ⊢ body ▷ B → Γ ⊢ .lam A body ▷ .forallE A B
  | forallE : Γ ⊢ A ▷ U → Γ ⊢ U ⤳* .sort u →
    A::Γ ⊢ B ▷ V → A::Γ ⊢ V ⤳* .sort v → Γ ⊢ .forallE A B ▷ .sort (.imax u v)

theorem InferType.hasType (H : Γ ⊢ e ▷ A) : Γ ⊢ e : A := sorry

theorem InferType.determ (H1 : Γ ⊢ e ▷ A) (H2 : Γ ⊢ e ▷ A') : A = A' := by
  induction H1 generalizing A' with
  | bvar h1 => cases H2 with | bvar h2 => exact h1.determ h2
  | sort => cases H2; rfl
  | const l1 l2 => cases H2 with | const r1 r2 => cases l1.symm.trans r1; rfl
  | app l1 l2 _ ih =>
    cases H2 with | app r1 r2 => cases ih r1; cases l2.determ .forallE r2 .forallE; rfl
  | lam _ l2 ih => cases H2 with | lam _ r2 => cases ih r2; rfl
  | forallE l1 l2 l3 l4 ih1 ih2 =>
    cases H2 with | forallE r1 r2 r3 r4
    cases ih1 r1; cases l2.determ .sort r2 .sort
    cases ih2 r3; cases l4.determ .sort r4 .sort; rfl

theorem InferType.weak' (W : Ctx.Lift' ρ Γ Δ) : Γ ⊢ e ▷ A → Δ ⊢ e.lift' ρ ▷ A.lift' ρ
  | .bvar h => .bvar (h.weak' W)
  | .sort => .sort
  | .const h1 h2 => by rw [(henv.closedC h1).mkInstS.lift'_eq .zero]; exact .const h1 h2
  | .app h1 h2 h3 => SExpr.lift'_inst_hi .. ▸ .app (h1.weak' W) (h2.weak' W) (h3.weak' W)
  | .lam h1 h2 => .lam (h1.weak' W) (h2.weak' W.cons)
  | .forallE h1 h2 h3 h4 => .forallE (h1.weak' W) (h2.weak' W) (h3.weak' W.cons) (h4.weak' W.cons)

/-- Strengthening of a defeq along a context lift (the `SExpr` analogue of `IsDefEqU.weak'_iff`).
Pre-existing sorry: this obligation was the `extra` case of `WHRed.weakU_inv` (now its `hinv`
hypothesis). Only used by the `InferType` lemmas below, which are not on the unique-typing chain. -/
theorem IsDefEq.weakU_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ a.lift' ρ ≡ b.lift' ρ : A) :
    ∃ A', Γ ⊢ a ≡ b : A' := sorry

theorem InferType.weakU_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e.lift' ρ ▷ A') :
    ∃ A, A' = A.lift' ρ ∧ Γ ⊢ e ▷ A := by
  generalize he : e.lift' ρ = e' at H
  induction H generalizing Γ ρ e with
  | bvar h => let .bvar _ := e; cases he; let ⟨_, h1, h2⟩ := h.weakU_inv W; exact ⟨_, h1, .bvar h2⟩
  | sort => let .sort _ := e; cases he; exact ⟨_, rfl, .sort⟩
  | const h1 h2 =>
    let .const .. := e; cases he
    exact ⟨_, ((henv.closedC h1).mkInstS.lift'_eq .zero).symm, .const h1 h2⟩
  | app h1 h2 h3 ih =>
    let .app .. := e; cases he
    obtain ⟨_, rfl, a1⟩ := ih W rfl
    obtain ⟨F, a2, a3⟩ := h2.weakU_inv W (IsDefEq.weakU_inv W); cases F <;> cases a2
    refine ⟨_, by rw [SExpr.lift'_inst_hi], .app a1 a3 (h3.weak'_inv W)⟩
  | lam h1 h2 ih =>
    let .lam .. := e; cases he
    obtain ⟨_, rfl, a2⟩ := ih W.cons rfl
    exact ⟨_, rfl, .lam (h1.weak'_inv W) a2⟩
  | forallE h1 h2 h3 h4 ih1 ih2 =>
    let .forallE .. := e; cases he
    obtain ⟨_, rfl, a1⟩ := ih1 W rfl
    obtain ⟨U, a2, a3⟩ := h2.weakU_inv W (IsDefEq.weakU_inv W); cases U <;> cases a2
    obtain ⟨_, rfl, b1⟩ := ih2 W.cons rfl
    obtain ⟨V, b2, b3⟩ := h4.weakU_inv W.cons (IsDefEq.weakU_inv W.cons); cases V <;> cases b2
    exact ⟨_, rfl, .forallE a1 a3 b1 b3⟩

theorem InferType.weak'_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e.lift' ρ ▷ A.lift' ρ) : Γ ⊢ e ▷ A := by
  obtain ⟨_, h1, h2⟩ := H.weakU_inv W
  exact SExpr.lift'_inj.1 h1 ▸ h2

/-- Substitution of an `InferType`-typed substitution into a defeq. Pre-existing sorry: this
obligation was the `extra` case of `WHRed.subst` (now its `hdf` hypothesis); it would follow from
`IsDefEq.subst` given `InferType.hasType` (itself a sorry). Only used by `InferType.subst`. -/
theorem IsDefEq.subst_inferType (W : Ctx.Subst InferType Δ σ Γ) (H : Γ ⊢ a ≡ b : A) :
    Δ ⊢ a.subst σ ≡ b.subst σ : A.subst σ := sorry

theorem InferType.subst (W : Ctx.Subst InferType Δ σ Γ)
    (H : Γ ⊢ e ▷ A) : Δ ⊢ e.subst σ ▷ A.subst σ := by
  induction H generalizing Δ σ with
  | @bvar Γ i A h =>
    simp [SExpr.subst]
    induction W generalizing i A with | nil | @cons Γ σ B W h' ih <;> cases h
    case zero => rw [SExpr.lift, SExpr.subst_lift']; exact h'
    case succ i C h => rw [SExpr.lift, SExpr.subst_lift']; exact ih h
  | sort => exact .sort
  | const h1 h2 =>
    rw [(henv.closedC h1).mkInstS.subst_eq .zero]
    exact .const h1 h2
  | app h1 h2 h3 ih =>
    exact subst_inst ▸ .app (ih W) (h2.subst (IsDefEq.subst_inferType W)) (h3.subst W)
  | lam h1 h2 ih => exact .lam (h1.subst W) (ih (W.lift .bvar fun W h => h.weak' W))
  | forallE h1 h2 h3 h4 ih1 ih2 =>
    exact .forallE (ih1 W) (h2.subst (IsDefEq.subst_inferType W))
      (ih2 (W.lift .bvar fun W h => h.weak' W))
      (h4.subst (IsDefEq.subst_inferType (W.lift .bvar fun W h => h.weak' W)))

theorem InferType.inst (H₀ : Γ ⊢ a ▷ A₀) (H : A₀::Γ ⊢ e ▷ A) :
    Γ ⊢ e.inst a ▷ A.inst a := .subst (.one .bvar (fun W h => h.weak' W) H₀) H

def InferTypeS (Γ : List SExpr) (e A : SExpr) := ∃ A', Γ ⊢ e ▷ A' ∧ Γ ⊢ A' ⤳* A
scoped notation:65 Γ " ⊢ " e1 " ▷* " e2:36 => InferTypeS Γ e1 e2

theorem InferTypeS.hasType : Γ ⊢ e ▷* A → Γ ⊢ e : A := sorry

theorem WHRedS.inferType
    (H1 : Γ ⊢ e ⤳* e₁) (W1 : WHNF Γ e₁)
    (H2 : Γ ⊢ e ⤳* e₂) (W2 : WHNF Γ e₂) : e₁ = e₂ := by
  induction H1 using ReflTransGen.headIndOn generalizing e₂ with
  | rfl =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => rfl
    | head r1 => cases W1 _ r1
  | head l1 l2 ih =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => cases W2 _ l1
    | head r1 r2 => cases l1.determ r1; exact ih r2 W2

theorem WHRedS.parRedS (H : Γ ⊢ e ⤳* e') : Γ ⊢ e ≫* e' := sorry

theorem InferTypeS.determ
    (H1 : Γ ⊢ e ▷* A) (W1 : WHNF Γ A)
    (H2 : Γ ⊢ e ▷* A') (W2 : WHNF Γ A') : A = A' := by
  let ⟨_, h1, h2⟩ := H1; let ⟨_, h3, h4⟩ := H2
  cases h1.determ h3; exact h2.determ W1 h4 W2

theorem InferTypeS.weak' (W : Ctx.Lift' ρ Γ Δ) : Γ ⊢ e ▷* A → Δ ⊢ e.lift' ρ ▷* A.lift' ρ
  | ⟨_, h1, h2⟩ => ⟨_, h1.weak' W, h2.weak' W⟩

theorem InferTypeS.weakU_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e.lift' ρ ▷* A') :
    ∃ A, A' = A.lift' ρ ∧ Γ ⊢ e ▷* A := by
  let ⟨_, h1, h2⟩ := H
  obtain ⟨_, rfl, a1⟩ := h1.weakU_inv W
  obtain ⟨_, rfl, a2⟩ := h2.weakU_inv W (IsDefEq.weakU_inv W)
  exact ⟨_, rfl, _, a1, a2⟩

scoped notation:65 Γ " ⊢ " e1 " ≡ₚ " e2 " : " A:36 => NormalEq Γ e1 e2 A
inductive NormalEq : List SExpr → SExpr → SExpr → SExpr → Prop where
  | refl : Γ ⊢ e : A → Γ ⊢ e ≡ₚ e : A
  | appDF : Γ ⊢ f₁ ≡ₚ f₂ : .forallE A B → Γ ⊢ a₁ ≡ₚ a₂ : A →
    Γ ⊢ .app f₁ a₁ ≡ₚ .app f₂ a₂ : B.inst a₁
  | lamDF : Γ ⊢ A₁ ≡ A : .sort u → Γ ⊢ A₂ ≡ A : .sort u → A::Γ ⊢ B : .sort v →
    A::Γ ⊢ body₁ ≡ₚ body₂ : B → Γ ⊢ .lam A₁ body₁ ≡ₚ .lam A₂ body₂ : .forallE A B
  | forallEDF : Γ ⊢ A₁ ≡ A : .sort u → Γ ⊢ A₂ ≡ A : .sort u →
    Γ ⊢ A₁ ≡ₚ A₂ : .sort u → A::Γ ⊢ B₁ ≡ₚ B₂ : .sort v →
    Γ ⊢ .forallE A₁ B₁ ≡ₚ .forallE A₂ B₂ : .sort (.imax u v)
  | etaL : Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v → Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ e ≡ₚ .app e'.lift (.bvar 0) : B → Γ ⊢ .lam A e ≡ₚ e' : .forallE A B
  | etaR : Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v → Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ .app e'.lift (.bvar 0) ≡ₚ e : B → Γ ⊢ e' ≡ₚ .lam A e : .forallE A B
  | proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ₚ h' : p
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ₚ e2 : A → Γ ⊢ e1 ≡ₚ e2 : B

theorem NormalEq.defeqDFC (W : IsDefEqCtx Γ₀ Γ₁ Γ₂)
    (H : Γ₁ ⊢ e1 ≡ₚ e2 : A) : Γ₂ ⊢ e1 ≡ₚ e2 : A := by
  induction H generalizing Γ₂ with
  | refl h => refine .refl (h.defeqDFC W)
  | appDF h1 h2 ih1 ih2 => exact .appDF (ih1 W) (ih2 W)
  | lamDF h1 h2 h3 _ ih2 =>
    exact .lamDF (h1.defeqDFC W) (h2.defeqDFC W)
      (h3.defeqDFC (W.succ h1.hasType.2)) (ih2 (W.succ h1.hasType.2))
  | forallEDF h1 h2 _ _ ih1 ih2 =>
    exact .forallEDF (h1.defeqDFC W) (h2.defeqDFC W) (ih1 W) (ih2 (W.succ h1.hasType.2))
  | etaL h1 h2 h3 _ ih =>
    exact .etaL (h1.defeqDFC W) (h2.defeqDFC (W.succ h1)) (h3.defeqDFC W) (ih (W.succ h1))
  | etaR h1 h2 h3 _ ih =>
    exact .etaR (h1.defeqDFC W) (h2.defeqDFC (W.succ h1)) (h3.defeqDFC W) (ih (W.succ h1))
  | proofIrrel h1 h2 h3 => exact .proofIrrel (h1.defeqDFC W) (h2.defeqDFC W) (h3.defeqDFC W)
  | defeqDF h1 _ ih => exact .defeqDF (h1.defeqDFC W) (ih W)

theorem NormalEq.defeq (H : Γ ⊢ e1 ≡ₚ e2 : A) : Γ ⊢ e1 ≡ e2 : A := by
  induction H with
  | refl h => exact h
  | appDF h1 h2 ih1 ih2 => exact .appDF ih1 ih2
  | lamDF hA₁ hA₂ hB _ ihB =>
    exact have W := .succ .zero hA₁.symm
      .defeqDF (.forallEDF hA₁ (hB.defeqDFC W)) (.lamDF (hA₁.trans hA₂.symm) (ihB.defeqDFC W))
  | forallEDF hA₁ hA₂ _ _ ihA ihB =>
    exact .forallEDF (hA₁.trans hA₂.symm) (ihB.defeqDFC (.succ .zero hA₁.symm))
  | etaL hA _ h1 _ ih => exact .trans (.lamDF hA ih) (.eta h1)
  | etaR hA _ h1 _ ih => exact .trans (.symm (.eta h1)) (.lamDF hA ih)
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h2 h3
  | defeqDF h1 _ ih => exact .defeqDF h1 ih

theorem NormalEq.symm (H : Γ ⊢ e1 ≡ₚ e2 : A) : Γ ⊢ e2 ≡ₚ e1 : A := by
  induction H with
  | refl h => exact .refl h
  | appDF h1 h2 ih1 ih2 => exact .defeqDF sorry (u := sorry) <| .appDF ih1 ih2
  | lamDF h1 h2 h3 _ ih2 => exact .lamDF h2 h1 h3 ih2
  | forallEDF h1 h2 _ _ ih1 ih2 => exact .forallEDF h2 h1 ih1 ih2
  | etaL h1 h2 h3 _ ih => exact .etaR h1 h2 h3 ih
  | etaR h1 h2 h3 _ ih => exact .etaL h1 h2 h3 ih
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h3 h2
  | defeqDF h1 _ ih => exact .defeqDF h1 ih

theorem NormalEq.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≡ₚ e2 : A) :
    Γ' ⊢ e1.lift' ρ ≡ₚ e2.lift' ρ : A.lift' ρ := by
  induction H generalizing Γ' ρ with
  | refl h => exact .refl (h.weak' W)
  | appDF h1 h2 ih1 ih2 => exact .defeqDF sorry (u := sorry) <| .appDF (ih1 W) (ih2 W)
  | lamDF h1 h2 h3 _ ih2 => exact .lamDF (h1.weak' W) (h2.weak' W) (h3.weak' W.cons) (ih2 W.cons)
  | forallEDF h1 h2 _ _ ih1 ih2 => exact .forallEDF (h1.weak' W) (h2.weak' W) (ih1 W) (ih2 W.cons)
  | etaL h1 h2 h3 _ ih =>
    refine .etaL (h1.weak' W) (h2.weak' W.cons) (h3.weak' W) ?_
    simpa [← SExpr.lift'_comp] using ih W.cons
  | etaR h1 h2 h3 _ ih =>
    refine .etaR (h1.weak' W) (h2.weak' W.cons) (h3.weak' W) ?_
    simpa [← SExpr.lift'_comp] using ih W.cons
  | proofIrrel h1 h2 h3 => exact .proofIrrel (h1.weak' W) (h2.weak' W) (h3.weak' W)
  | defeqDF h1 _ ih => exact .defeqDF (h1.weak' W) (ih W)

def CRDefEq (Γ : List SExpr) (e₁ e₂ A : SExpr) : Prop :=
  Γ ⊢ e₁ ≡ e₂ : A ∧
  ∃ e₁' e₂', Γ ⊢ e₁ ≫* e₁' ∧ Γ ⊢ e₂ ≫* e₂' ∧ Γ ⊢ e₁' ≡ₚ e₂' : A
scoped notation:65 Γ " ⊢ " e1 " ≫≪ " e2 " : " A:36 => CRDefEq Γ e1 e2 A

def CRDefEqLift := WithLift CRDefEq
scoped notation:65 Γ " ⊢ " e1 " ≫≪ " e2 " :↑ " A:36 => CRDefEqLift Γ e1 e2 A

theorem CRDefEq.normalEq (H : Γ ⊢ e₁ ≡ₚ e₂ : A) : Γ ⊢ e₁ ≫≪ e₂ : A :=
  ⟨H.defeq, _, _, .rfl, .rfl, H⟩

theorem CRDefEq.refl (H : Γ ⊢ e : A) : Γ ⊢ e ≫≪ e : A :=
  .normalEq (.refl H)

theorem CRDefEq.defeq : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ e₁ ≡ e₂ : A := (·.1)

theorem CRDefEq.symm : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ e₂ ≫≪ e₁ : A
  | ⟨h1, _, _, h3, h4, h5⟩ => ⟨h1.symm, _, _, h4, h3, h5.symm⟩

theorem CRDefEq.trans : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ e₂ ≫≪ e₃ : A → Γ ⊢ e₁ ≫≪ e₃ : A
  | ⟨l1, _, _, l3, l4, l5⟩, ⟨r1, _, _, r3, r4, r5⟩ => sorry

theorem CRDefEq.defeqDF : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ A ≡ B : .sort u → Γ ⊢ e₁ ≫≪ e₂ : B
  | ⟨l1, _, _, l3, l4, l5⟩, H => ⟨H.defeqDF l1, _, _, l3, l4, l5.defeqDF H⟩

theorem CRDefEq.weak' (W : Ctx.Lift' ρ Γ Γ') :
    Γ ⊢ e1 ≫≪ e2 : A → Γ' ⊢ e1.lift' ρ ≫≪ e2.lift' ρ : A.lift' ρ
  | ⟨h1, _, _, h3, h4, h5⟩ => ⟨h1.weak' W, _, _, h3.weak' W, h4.weak' W, h5.weak' W⟩

theorem WHRedS.crDefEq (H1 : Γ ⊢ e1 : A) (H2 : Γ ⊢ e1 ⤳* e2) : Γ ⊢ e1 ≫≪ e2 : A :=
  ⟨H2.defeq H1, _, _, H2.parRedS, .rfl, .refl (H2.defeq H1).hasType.2⟩

nonrec theorem CRDefEqLift.symm : Γ ⊢ e1 ≫≪ e2 :↑ A → Γ ⊢ e2 ≫≪ e1 :↑ A := .symm .symm

theorem CRDefEqLift.defeq (H : Γ ⊢ e1 ≫≪ e2 :↑ A) : Γ ⊢ e1 ≡ e2 :↑ A := H.imp (·.1)

theorem CRDefEqLift.left (H : Γ ⊢ e1 ≫≪ e2 :↑ A) : Γ ⊢ e1 :↑ A := H.defeq.left

nonrec theorem CRDefEqLift.refl (H : Γ ⊢ e :↑ A) : Γ ⊢ e ≫≪ e :↑ A :=
  .refl (.refl <| H.left' · · ·)

theorem InferType.whRed (H1 : Γ ⊢ e ⤳ e') (H2 : Γ ⊢ e ▷ A) : Γ ⊢ e' ▷ A := by
  induction H1 generalizing A with
  | app h1 ih => let .app r1 r2 r3 := H2; exact .app (ih r1) r2 r3
  | beta =>
    let .app a1 a2 a3 := H2
    let .lam b1 b2 := a1
    cases WHNF.forallE.whRedS a2
    exact .inst sorry b2
  | major =>
    -- Not provable as stated: `InferType.app` infers `B.inst a'` for the reduct, which is defeq
    -- but not equal to `B.inst a`; the lemma would need restating up to defeq.
    sorry
  | extra => sorry
