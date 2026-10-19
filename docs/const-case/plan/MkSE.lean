import Lean4Lean.Experimental.ShapeLogRelAdequacy
/-! Completeness audit 3: `mkSE` (R4) needs env-generic `isType'`/`hasTypeS`, which R4 does
not list. The repo's versions (SExpr.lean:1338-1365) are stated with `⊢ₛ` (= `Params.env`).
Here: `IsDefEqStrongE` copied from `audit-complete-1/WeakE.lean`; `hasTypeS`/`isType'`
re-proved for any `E` (the proofs are env-agnostic, no `hE`); `CtorProviderE`, `mkSE`
ported from `mkS` (SExpr.lean:1818-1885). Sorry-free. -/
namespace Lean4Lean
namespace SExpr
open _root_.Lean4Lean.Params
variable [Params]
section
set_option hygiene false
local notation:65 Γ " ⊢ₑ " e1 " : " A:36 => IsDefEqStrongE Γ e1 e1 A
local notation:65 Γ " ⊢ₑ " e1 " ≡ " e2 " : " A:36 => IsDefEqStrongE Γ e1 e2 A
variable (E : VEnv)
/-- `IsDefEqStrong` with the environment explicit; `IsDefEqStrong = IsDefEqStrongE Params.env`.
In the real refactor this is a new first parameter of `IsDefEqStrong`, not a copy. -/
inductive IsDefEqStrongE : List SExpr → SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ₑ A : .sort u → Γ ⊢ₑ .bvar i : A
  | symm : Γ ⊢ₑ e ≡ e' : A → Γ ⊢ₑ e' ≡ e : A
  | trans : Γ ⊢ₑ A : .sort u → Γ ⊢ₑ e₁ ≡ e₂ : A → Γ ⊢ₑ e₂ ≡ e₃ : A → Γ ⊢ₑ e₁ ≡ e₃ : A
  | trans' : Γ ⊢ₑ A ≡ B : .sort u → Γ ⊢ₑ B ≡ C : .sort v → Γ ⊢ₑ A ≡ C : .sort u
  | sort : Γ ⊢ₑ .sort l : .sort (.succ l)
  | const : E.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ₑ SExpr.mkInst ls ci.type : .sort u →
    (F : ∀ cl, CtorBundle c cl) →
    (∀ cl, Γ ⊢ₑ SExpr.mkInst ls ci.type ≡ (F cl).rhs ls : .sort (F cl).u) →
    Γ ⊢ₑ .const c ls : SExpr.mkInst ls ci.type
  | appDF : Γ ⊢ₑ A : .sort u → A::Γ ⊢ₑ B : .sort v →
    Γ ⊢ₑ f ≡ f' : .forallE A B → Γ ⊢ₑ a ≡ a' : A →
    Γ ⊢ₑ B.inst a ≡ B.inst a' : .sort v →
    Γ ⊢ₑ .app f a ≡ .app f' a' : B.inst a
  | lamDF : Γ ⊢ₑ A ≡ A' : .sort u → A::Γ ⊢ₑ B : .sort v →
    A::Γ ⊢ₑ body ≡ body' : B → A'::Γ ⊢ₑ body ≡ body' : B →
    Γ ⊢ₑ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF : Γ ⊢ₑ A ≡ A' : .sort u →
    A::Γ ⊢ₑ body ≡ body' : .sort v → A'::Γ ⊢ₑ body ≡ body' : .sort v →
    Γ ⊢ₑ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF : Γ ⊢ₑ A ≡ B : .sort u → Γ ⊢ₑ e1 ≡ e2 : A → Γ ⊢ₑ e1 ≡ e2 : B
  | beta : A::Γ ⊢ₑ e : B → Γ ⊢ₑ e' : A →
    Γ ⊢ₑ .app (.lam A e) e' : B.inst e' → Γ ⊢ₑ e.inst e' : B.inst e' →
    Γ ⊢ₑ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta : Γ ⊢ₑ e : .forallE A B → Γ ⊢ₑ .lam A (.app e.lift (.bvar 0)) : .forallE A B →
    Γ ⊢ₑ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel : Γ ⊢ₑ p : .sort .zero → Γ ⊢ₑ h : p → Γ ⊢ₑ h' : p → Γ ⊢ₑ h ≡ h' : p
  | extra : E.defeqs df → ls.length = df.uvars →
    Γ ⊢ₑ .mkInst ls df.lhs : .mkInst ls df.type →
    Γ ⊢ₑ .mkInst ls df.rhs : .mkInst ls df.type →
    Γ ⊢ₑ .mkInst ls df.lhs ≡ .mkInst ls df.rhs : .mkInst ls df.type
end

theorem IsDefEqStrongE.mono {E E' : VEnv} (hle : E ≤ E') {Γ e1 e2 A}
    (H : IsDefEqStrongE E Γ e1 e2 A) : IsDefEqStrongE E' Γ e1 e2 A := by
  induction H with
  | bvar h _ ih => exact .bvar h ih
  | symm _ ih => exact .symm ih
  | trans _ _ _ ih1 ih2 ih3 => exact .trans ih1 ih2 ih3
  | trans' _ _ ih1 ih2 => exact .trans' ih1 ih2
  | sort => exact .sort
  | const h1 h2 _ F _ ih3 ih5 => exact .const (hle.1 h1) h2 ih3 F ih5
  | appDF _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 => exact .appDF ih1 ih2 ih3 ih4 ih5
  | lamDF _ _ _ _ ih1 ih2 ih3 ih4 => exact .lamDF ih1 ih2 ih3 ih4
  | forallEDF _ _ _ ih1 ih2 ih3 => exact .forallEDF ih1 ih2 ih3
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ _ _ ih1 ih2 ih3 ih4 => exact .beta ih1 ih2 ih3 ih4
  | eta _ _ ih1 ih2 => exact .eta ih1 ih2
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 _ _ ih1 ih2 => exact .extra (hle.2 h1) h2 ih1 ih2

theorem IsDefEqStrongE.hasTypeS {E : VEnv} {Γ e1 e2 u} (H : IsDefEqStrongE E Γ e1 e2 (.sort u)) :
    IsDefEqStrongE E Γ e1 e1 (.sort u) ∧ IsDefEqStrongE E Γ e2 e2 (.sort u) :=
  ⟨.trans .sort H H.symm, .trans .sort H.symm H⟩

theorem IsDefEqStrongE.isType' {E : VEnv} {Γ e1 e2 A} (H : IsDefEqStrongE E Γ e1 e2 A) :
    ∃ u, IsDefEqStrongE E Γ A A (.sort u) := by
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

/-- `CtorProvider` (SExpr.lean:1805) over `E`. -/
def CtorProviderE (E : VEnv) : Prop :=
  ∀ {Γ : List SExpr} {c : Name} {ci : VConstant} {vs : List VLevel} {u : VLevel},
    E.constants c = some ci → (∀ l ∈ vs, l.WF univs) → vs.length = ci.uvars →
    E.HasType univs [] (ci.type.instL vs) (.sort u) →
    IsDefEqStrongE E Γ (mkInst (vs.map SLevel.mk) ci.type) (mkInst (vs.map SLevel.mk) ci.type)
      (.sort (SLevel.mk u)) →
    ∀ cl : CtorBundle.IsCtor c, ∃ B : CtorBundle c cl,
      IsDefEqStrongE E Γ (mkInst (vs.map SLevel.mk) ci.type) (B.rhs (vs.map SLevel.mk)) (.sort B.u)

/-- `mkS` over `E`; only `isType'`/`hasTypeS` had to be made env-generic. -/
theorem _root_.Lean4Lean.VEnv.IsDefEqStrong.mkSE {E : VEnv} (hctor : CtorProviderE E)
    (H : E.IsDefEqStrong Params.univs Γ e₁ e₂ A)
    (hΓ : OnCtx Γ (fun _ A => A.LevelWF Params.univs)) :
    IsDefEqStrongE E (Γ.map mk) (mk e₁) (mk e₂) (mk A) := by
  induction H with
  | bvar h _ _ ih => exact .bvar (SExpr.Lookup.mkS h) (ih hΓ)
  | symm _ ih => exact .symm (ih hΓ)
  | trans _ _ ih1 ih2 => let ⟨_, hA⟩ := (ih1 hΓ).isType'; exact .trans hA (ih1 hΓ) (ih2 hΓ)
  | @sortDF l l' Γ hl hl' h =>
    change IsDefEqStrongE E _ (.sort (SLevel.mk _)) (.sort (SLevel.mk _)) (.sort (SLevel.mk _))
    have hu := SLevel.mk_eq hl hl' h
    have hus : SLevel.mk l.succ = (SLevel.mk l').succ := by rw [SLevel.mk_succ hl, hu]
    rw [hu, hus]
    exact .sort
  | @constDF c ci ls ls' u Γ h1 h2 h3 h4 h5 _ h7 _ _ ih8 =>
    change IsDefEqStrongE E _ (.const c (ls.map SLevel.mk)) (.const c (ls'.map SLevel.mk))
      (mk (ci.type.instL ls))
    have hls := SLevel.map_mk_eq h2 h3 h5
    have e1 : mk (ci.type.instL ls) = mkInst (ls.map SLevel.mk) ci.type := (mkInst_map_mk h2).symm
    have e2 : mk (ci.type.instL ls') = mkInst (ls.map SLevel.mk) ci.type := by
      rw [← mkInst_map_mk h3, hls]
    have hT := ih8 hΓ
    rw [e1, e2] at hT
    have hT' := hT.hasTypeS.1
    have hV : E.HasType univs [] (ci.type.instL ls) (.sort u) := h7.defeq.hasType.1
    rw [e1, ← hls]
    exact .const h1 (by simpa using h4) hT'
      (fun cl => (hctor h1 h2 h4 hV hT' cl).choose) fun cl => (hctor h1 h2 h4 hV hT' cl).choose_spec
  | appDF _ _ hA _ _ _ _ ihA ihB ihf iha ihBi =>
    have hAwf := (hA.defeq.levelWF hΓ).1
    have hBi := ihBi hΓ
    simp only [mk, mk_instExpr] at hBi
    simpa only [mk, mk_instExpr] using
      IsDefEqStrongE.appDF (ihA hΓ) (ihB ⟨hΓ, hAwf⟩) (ihf hΓ) (iha hΓ) hBi
  | lamDF _ _ hAA' _ _ _ _ ihAA' ihB _ ihbody ihbody' =>
    have hAwf := (hAA'.defeq.levelWF hΓ).1
    have hA'wf := (hAA'.defeq.levelWF hΓ).2.1
    exact .lamDF (ihAA' hΓ) (ihB ⟨hΓ, hAwf⟩) (ihbody ⟨hΓ, hAwf⟩) (ihbody' ⟨hΓ, hA'wf⟩)
  | forallEDF hu hv hAA' _ _ ihAA' ih1 ih2 =>
    have hAwf := (hAA'.defeq.levelWF hΓ).1
    have hA'wf := (hAA'.defeq.levelWF hΓ).2.1
    simpa only [mk, SLevel.mk_imax hu hv] using
      IsDefEqStrongE.forallEDF (ihAA' hΓ) (ih1 ⟨hΓ, hAwf⟩) (ih2 ⟨hΓ, hA'wf⟩)
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
    have hbody := IsDefEqStrongE.appDF h1 h2 h3 (.bvar .zero h1)
      (lift_cons_skip_inst_bvar0.symm ▸ h4)
    rw [lift_cons_skip_inst_bvar0] at hbody
    exact .eta (ihe hΓ) (.lamDF (ihA hΓ) h4 hbody hbody)
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    simpa only [mk, SLevel.mk_zero] using IsDefEqStrongE.proofIrrel (ih1 hΓ) (ih2 hΓ) (ih3 hΓ)
  | @extra df ls u Γ h1 h2 h3 _ _ _ _ _ _ _ _ _ ih8 ih9 =>
    have hl := ih8 hΓ; have hr := ih9 hΓ
    simp only [← mkInst_map_mk h2] at hl hr ⊢
    exact .extra h1 (by simpa using h3) hl hr

/-- `CtorProvider.syn` (SExpr.lean:1902) over `E ≤ Params.env`. -/
theorem CtorProviderE.synE {E : VEnv} (hE : E ≤ Params.env) : CtorProviderE E := by
  intro Γ c ci vs u h1 hvs hlen hV hT cl
  obtain ⟨I, Ts, args, hTs, hI, heq⟩ := ctor_syn cl.cl.2.2 cl.cl.2.1 (hE.1 h1)
  have hu : u.WF univs := (hV.levelWF ⟨⟩).2.2
  have hrhs : mkInst (vs.map SLevel.mk) ci.type =
      (Ts.map fun T => mk (T.instL vs)).foldr .forallE
        ((args.map fun A => mk (A.instL vs)).foldr (fun A acc => acc.app A)
          (.const I (vs.map SLevel.mk))) := by
    rw [mkInst_map_mk hvs, heq, mk_instL_foldr_forallE, mk_instL_foldr_app]
    simp only [VExpr.instL, mk, VLevel.inst_map_id hlen]
  refine ⟨⟨I, Ts.map fun T => mk (T.instL vs), args.map fun A => mk (A.instL vs), SLevel.mk u,
    by simp [hTs], by simpa using hI,
    SLevel.mk_ne_zero hu (ctor_sort cl.cl.2.2 cl.cl.2.1 (hE.1 h1) hvs hlen (hV.mono hE))⟩, ?_⟩
  show IsDefEqStrongE E _ _ ((Ts.map fun T => mk (T.instL vs)).foldr .forallE
    ((args.map fun A => mk (A.instL vs)).foldr (fun A acc => acc.app A)
      (.const I (vs.map SLevel.mk)))) _
  rw [← hrhs]; exact hT

#print axioms CtorProviderE.synE

#print axioms VEnv.IsDefEqStrong.mkSE
