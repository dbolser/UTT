import Lean4Lean.Experimental.ShapeLogRel

namespace Lean4Lean.SExpr.T
variable [Params]

structure LogRelBase (Γ : List SExpr) (n : Nat) where
  /-- Term validity: `M ≡ N : A` at element-shape `m` and type-shape `a`. -/
  DefEq (M N A : SExpr) (m a : WShape n) : Prop
  /-- Type validity: `A ≡ B` are valid types at type-shape `a`. -/
  TyDefEq (A B : SExpr) (a : WShape n) : Prop

structure LogRel (Γ : List SExpr) (n : Nat) extends LogRelBase Γ n where
  sort_iff : DefEq M N A (.sort r) (.sort r') ↔
    AmbSort Γ A ∧ ∃ u, TyRedS Γ M (.sort u) ∧ TyRedS Γ N (.sort u)
  sort_iff_ty : TyDefEq M N (.sort r) ↔ ∃ u, TyRedS Γ M (.sort u) ∧ TyRedS Γ N (.sort u)
  bot : a.HasType .type → DefEq M N A .bot a
  toType : DefEq M N A m (.sort r) → TyDefEq M N m
  left : DefEq M N A m a → DefEq M M A m a
  left_ty : TyDefEq M N m → TyDefEq M M m
  symm : DefEq M N A m a → DefEq N M A m a
  symm_ty : TyDefEq M N m → TyDefEq N M m
  trans : DefEq M₁ M₂ A m a → DefEq M₂ M₃ A m a → DefEq M₁ M₃ A m a
  trans' : DefEq A₁ A₂ (.sort u) a s → DefEq A₂ A₃ (.sort v) a (.sort r) → DefEq A₁ A₃ (.sort u) a s
  trans_ty : TyDefEq M₁ M₂ m → TyDefEq M₂ M₃ m → TyDefEq M₁ M₃ m
  conv : TyDefEq A B a → DefEq M N A m a → DefEq M N B m a
  mono_r_2 : a ≤ a' → m.HasType a → a'.HasType .type → DefEq M N A m a' → DefEq M N A m a
  mono_r_2_ty : a ≤ a' → a.HasType .type → a'.HasType .type → TyDefEq A B a' → TyDefEq A B a
  mono_r_1 : a ≤ a' → m.HasType a → m.HasType a' → TyDefEq A A a' → DefEq M N A m a → DefEq M N A m a'
  mono_l : m ≤ m' → m.HasType a → m'.HasType a → DefEq M N A m' a → DefEq M N A m a
  join_ty : m₁.Compat m₂ → m₁.HasType .type → m₂.HasType .type →
    TyDefEq A B m₁ → TyDefEq A B m₂ → TyDefEq A B (m₁.join m₂)
  whr : TWHRedS Γ M M' A → TWHRedS Γ N N' A → (DefEq M N A m a ↔ DefEq M' N' A m a)
  whr_ty : TyRedS Γ A A' → TyRedS Γ B B' → (TyDefEq A B m ↔ TyDefEq A' B' m)

theorem TyRedS.sort : TyRedS Γ (.sort u) (.sort u) := ⟨⟨_, .sort⟩, .rfl⟩

theorem LogRelBase.TyDefEq.sort {R : LogRel Γ n} : R.TyDefEq (.sort u) (.sort u) (.sort r) :=
  R.sort_iff_ty.2 ⟨_, .sort, .sort⟩

/-! #### Concrete definitions at level 0 -/

def LR0.TyDefEq (Γ : List SExpr) (M N : SExpr) : WShape 0 → Prop
  | ⟨.bot, _⟩ => True
  | ⟨.sort _, _⟩ => ∃ u, TyRedS Γ M (.sort u) ∧ TyRedS Γ N (.sort u)

def LR0.DefEq (Γ : List SExpr) (M N A : SExpr) (m a : WShape 0) : Prop :=
  match a.1 with
  | .bot => True
  | .sort _ => match m.1 with
    | .bot => True
    | _ => AmbSort Γ A ∧ LR0.TyDefEq Γ M N m

/-! #### Composition of typed reductions (D6 helpers) -/

/-- a typed reduction to a whnf can be continued from the reduct (`determ_l` + `trans'`) -/
theorem TyRedS.whnf_l (h : TyRedS Γ A A') (h2 : TyRedS Γ A X) (W : WHNF Γ X) : TyRedS Γ A' X :=
  let ⟨⟨_, e1⟩, r1⟩ := h; let ⟨⟨_, e2⟩, r2⟩ := h2
  ⟨⟨_, e1.symm.trans' e2⟩, r1.determ_l r2 W⟩

theorem TyRedS.trans (h : TyRedS Γ A A') (h2 : TyRedS Γ A' X) : TyRedS Γ A X :=
  let ⟨⟨_, e1⟩, r1⟩ := h; let ⟨⟨_, e2⟩, r2⟩ := h2
  ⟨⟨_, e1.trans' e2⟩, .trans r1 r2⟩

theorem TyRedS.ambSort (h : TyRedS Γ B (.sort u)) : AmbSort Γ B :=
  let ⟨⟨w, e⟩, _⟩ := h; ⟨u, w, e⟩

/-- at a sort ambient, a typed term reduction is a typed type reduction -/
theorem TWHRedS.toTyRedS (h : TWHRedS Γ M M' A) (hA : AmbSort Γ A) : TyRedS Γ M M' :=
  let ⟨_, _, e⟩ := hA; ⟨⟨_, e.defeqDF h.1⟩, h.2⟩

theorem LR0.TyDefEq.left : LR0.TyDefEq Γ M N m → LR0.TyDefEq Γ M M m := by
  dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
  intro ⟨u, hM, _⟩; exact ⟨u, hM, hM⟩

theorem LR0.TyDefEq.symm : LR0.TyDefEq Γ M N m → LR0.TyDefEq Γ N M m := by
  dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
  intro ⟨u, hM, hN⟩; exact ⟨u, hN, hM⟩

theorem LR0.TyDefEq.trans :
    LR0.TyDefEq Γ M₁ M₂ m → LR0.TyDefEq Γ M₂ M₃ m → LR0.TyDefEq Γ M₁ M₃ m := by
  dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
  intro ⟨u, h1, h2⟩ ⟨u', h2', h3⟩
  cases h2.2.determ .sort h2'.2 .sort; exact ⟨u, h1, h3⟩

theorem LR0.TyDefEq.whr (hA : TyRedS Γ A A') (hB : TyRedS Γ B B') :
    LR0.TyDefEq Γ A B m ↔ LR0.TyDefEq Γ A' B' m := by
  dsimp [LR0.TyDefEq]; split <;> [exact .rfl; skip]
  constructor <;> intro ⟨u, r1, r2⟩
  · exact ⟨u, hA.whnf_l r1 .sort, hB.whnf_l r2 .sort⟩
  · exact ⟨u, hA.trans r1, hB.trans r2⟩

def LR0 : LogRel Γ 0 where
  DefEq := LR0.DefEq Γ
  TyDefEq := LR0.TyDefEq Γ
  sort_iff := by simp [LR0.DefEq, LR0.TyDefEq, WShape.sort]
  sort_iff_ty := by simp [LR0.TyDefEq, WShape.sort]
  bot {_ _ _ _} _ := by simp only [LR0.DefEq, WShape.bot]; split <;> trivial
  toType {M N A m r} h := by
    obtain ⟨⟨⟩, _⟩ := m
    · trivial
    · exact And.right h
  left {M N A m a} := by
    dsimp only [LR0.DefEq]; split <;> [trivial; skip]
    split <;> [trivial; skip]
    exact fun ⟨hA, h⟩ => ⟨hA, LR0.TyDefEq.left h⟩
  left_ty := LR0.TyDefEq.left
  symm {M N A m a} := by
    dsimp only [LR0.DefEq]; split <;> [trivial; skip]
    split <;> [trivial; skip]
    exact fun ⟨hA, h⟩ => ⟨hA, LR0.TyDefEq.symm h⟩
  symm_ty := LR0.TyDefEq.symm
  trans {M₁ M₂ A m a M₃} := by
    dsimp only [LR0.DefEq]; split <;> [trivial; skip]
    split <;> [trivial; skip]
    exact fun ⟨hA, h⟩ ⟨_, h'⟩ => ⟨hA, LR0.TyDefEq.trans h h'⟩
  trans' {A₁ A₂ u a s A₃ v r} := by
    dsimp only [LR0.DefEq]; split <;> [(intros; trivial); skip]
    split <;> [(intros; trivial); skip]
    exact fun ⟨hA, h⟩ ⟨_, h'⟩ => ⟨hA, LR0.TyDefEq.trans h h'⟩
  trans_ty := LR0.TyDefEq.trans
  conv {A B a M N m} h := by
    obtain ⟨⟨⟩, _⟩ := a
    · exact fun _ => trivial
    · obtain ⟨u, -, hB⟩ := h
      dsimp only [LR0.DefEq]; split <;> [exact id; skip]
      exact fun ⟨_, h⟩ => ⟨hB.ambSort, h⟩
  mono_r_2 {a a' _ _ _ _} le _ _ := by
    obtain ⟨⟨⟩, _⟩ := a <;> obtain ⟨⟨⟩, _⟩ := a' <;> simp [LR0.DefEq]; cases le
  mono_r_2_ty {a a' _ _} le _ _ := by
    obtain ⟨⟨⟩, _⟩ := a <;> obtain ⟨⟨⟩, _⟩ := a' <;> simp [LR0.TyDefEq]; cases le
  mono_r_1 {a a' _ _ _ b} le h1 _ h2 := by
    obtain ⟨⟨⟩, _⟩ := a <;> obtain ⟨⟨⟩, _⟩ := a' <;>
      (try exact id) <;> [cases h1.bot_r; cases le]; exact id
  mono_l {m m' M N A a} le _ _ := by
    simp only [LR0.DefEq]; split <;> [trivial; skip]
    obtain ⟨⟨⟩, _⟩ := m <;> obtain ⟨⟨⟩, _⟩ := m' <;>
      (try exact id) <;> [exact fun _ => trivial; cases le]
  join_ty {A B m₁ m₂} hC hm₁ hm₂ := by
    obtain ⟨⟨⟩, _⟩ := m₁ <;> obtain ⟨⟨⟩, _⟩ := m₂ <;>
      simp [LR0.TyDefEq, WShape.join, Shape.join, dif_pos hC]
    simp [WShape.Compat, Shape.Compat] at hC; subst hC; simp
    intro u h1 h2 _ h3 h4; exact ⟨u, h1, h2⟩
  whr {M M' A N N' m a} hM hN := by
    dsimp only [LR0.DefEq]; split <;> [exact .rfl; skip]
    split <;> [exact .rfl; skip]
    constructor <;> intro ⟨hA, h⟩ <;> refine ⟨hA, ?_⟩
    · exact (LR0.TyDefEq.whr (hM.toTyRedS hA) (hN.toTyRedS hA)).1 h
    · exact (LR0.TyDefEq.whr (hM.toTyRedS hA) (hN.toTyRedS hA)).2 h
  whr_ty := LR0.TyDefEq.whr

/-! #### Concrete definitions at level n+1 -/

/-- Pi edge validity (merged `PiEdgeDefEq` / `PiEdgeEq2`).
For each argument `a ≡ b : A₁`, the substituted codomains are valid types.
For each argument `a : A₁`, the codomains `A₂[a]` and `B₂[a]` are equal types. -/
def LRS.PiDefEq (IH : LogRel Γ n)
    (B F₁ F₂ : SExpr) (b : WShape n) (f : WShapeFun n) : Prop :=
  (∀ {{a b' p}}, p.HasType b → Γ ⊢ a ≡ b' : B → IH.DefEq a b' B p b →
    IH.TyDefEq (F₁.inst a) (F₁.inst b') (f.app p) ∧
    IH.TyDefEq (F₂.inst a) (F₂.inst b') (f.app p)) ∧
  ∀ {{a p}}, p.HasType b → Γ ⊢ a : B → IH.DefEq a a B p b →
    IH.TyDefEq (F₁.inst a) (F₂.inst a) (f.app p)

theorem LRS.PiDefEq.left {IH : LogRel Γ n} :
    LRS.PiDefEq IH B F₁ F₂ b f → LRS.PiDefEq IH B F₁ F₁ b f := fun ⟨h1, _⟩ =>
  ⟨fun _ _ _ hp ha a1 => ⟨(h1 hp ha a1).1, (h1 hp ha a1).1⟩, fun _ _ hp ha a1 => (h1 hp ha a1).1⟩

def LRS.ValTyPi2 (IH : LogRel Γ n) (M₁ M₂ : SExpr) (b : WShape n) (f : WShapeFun n) : Prop :=
  ∃ B₁ F₁ B₂ F₂ u v,
    TyRedS Γ M₁ (.forallE B₁ F₁) ∧ TyRedS Γ M₂ (.forallE B₂ F₂) ∧
    Γ ⊢ B₁ ≡ B₂ : .sort u ∧ B₁::Γ ⊢ F₁ ≡ F₂ : .sort v ∧ IH.TyDefEq B₁ B₂ b ∧
    LRS.PiDefEq IH B₁ F₁ F₂ b f

def LRS.LamDefEq (IH : LogRel Γ n)
    (M N A₁ A₂ : SExpr) (m : WShapeFun n) (a₁ : WShape n) (a₂ : WShapeFun n) : Prop :=
  (∀ {{a b p}}, WShape.HasType p a₁ → Γ ⊢ a ≡ b : A₁ → IH.DefEq a b A₁ p a₁ →
    IH.DefEq (M.app a) (M.app b) (A₂.inst a) (m.app p) (a₂.app p) ∧
    IH.DefEq (N.app a) (N.app b) (A₂.inst a) (m.app p) (a₂.app p)) ∧
  (∀ {{a p}}, WShape.HasType p a₁ → Γ ⊢ a : A₁ → IH.DefEq a a A₁ p a₁ →
    IH.DefEq (M.app a) (N.app a) (A₂.inst a) (m.app p) (a₂.app p))

/-! #### The stage-1a constructor clause (PLAN D1), over an abstract `IH : LogRel Γ n` -/

/-- A field whose declared type is a closed inductive constant: related at the canonical
type shape `indTy`, at every typed element shape below the recorded one (artifact `TmEqNat`). -/
def LRS.FieldRel {Γ} : ∀ {n}, LogRel Γ n → SExpr → SExpr → SExpr → WShape n → Prop
  | 0, _, _, _, _, _ => True
  | _+1, IH, X, Y, T, p => ∀ q, q ≤ p → q.HasType .indTy → IH.DefEq X Y T q .indTy

inductive LRS.FieldsEq {Γ} {n} (IH : LogRel Γ n) :
    List SExpr → List SExpr → List SExpr → List (WShape n) → Prop
  | nil : FieldsEq IH [] [] [] []
  | cons : Γ ⊢ X ≡ Y : T → LRS.FieldRel IH X Y T p → FieldsEq IH Ts Xs Ys l →
      FieldsEq IH (T :: Ts) (X :: Xs) (Y :: Ys) (p :: l)

def LRS.CtorDefEq {Γ} {n} (IH : LogRel Γ n) (M N A : SExpr) (c : Name) (l : List (WShape n)) : Prop :=
  ∃ (I : Name) (ls : List SLevel) (ci : VConstant) (Ts Xs Ys : List SExpr),
    Params.classify c = some (.ctor l.length) ∧ Params.classify I = some (.indTy 0) ∧
    Params.env.constants c = some ci ∧ SExpr.mkInst ls ci.type = Ts.foldr .forallE (.const I ls) ∧
    TyRedS Γ A (.const I ls) ∧
    TWHRedS Γ M (spine (.const c ls) Xs) A ∧ TWHRedS Γ N (spine (.const c ls) Ys) A ∧
    LRS.FieldsEq IH Ts Xs Ys l

theorem foldr_forallE_const_inj : ∀ {Ts Ts' : List SExpr} {I I' : Name} {ls ls' : List SLevel},
    Ts.foldr SExpr.forallE (SExpr.const I ls) = Ts'.foldr SExpr.forallE (SExpr.const I' ls') →
    Ts = Ts' ∧ I = I' ∧ ls = ls'
  | [], [], _, _, _, _, h => by cases h; exact ⟨rfl, rfl, rfl⟩
  | _ :: _, [], _, _, _, _, h | [], _ :: _, _, _, _, _, h => by cases h
  | _ :: _, _ :: _, _, _, _, _, h => by
    simp only [List.foldr_cons, SExpr.forallE.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := foldr_forallE_const_inj h
    exact ⟨rfl, rfl, rfl⟩

theorem LRS.FieldRel.left : ∀ {n} {IH : LogRel Γ n} {X Y T p},
    LRS.FieldRel IH X Y T p → LRS.FieldRel IH X X T p
  | 0, _, _, _, _, _, _ => trivial
  | _+1, IH, _, _, _, _, h => fun q hq ht => IH.left (h q hq ht)
theorem LRS.FieldRel.symm : ∀ {n} {IH : LogRel Γ n} {X Y T p},
    LRS.FieldRel IH X Y T p → LRS.FieldRel IH Y X T p
  | 0, _, _, _, _, _, _ => trivial
  | _+1, IH, _, _, _, _, h => fun q hq ht => IH.symm (h q hq ht)
theorem LRS.FieldRel.trans : ∀ {n} {IH : LogRel Γ n} {X Y Z T p},
    LRS.FieldRel IH X Y T p → LRS.FieldRel IH Y Z T p → LRS.FieldRel IH X Z T p
  | 0, _, _, _, _, _, _, _, _ => trivial
  | _+1, IH, _, _, _, _, _, h, g => fun q hq ht => IH.trans (h q hq ht) (g q hq ht)
theorem LRS.FieldRel.mono : ∀ {n} {IH : LogRel Γ n} {X Y T} {p p' : WShape n},
    p ≤ p' → LRS.FieldRel IH X Y T p' → LRS.FieldRel IH X Y T p
  | 0, _, _, _, _, _, _, _, _ => trivial
  | _+1, _, _, _, _, _, _, le, h => fun q hq ht => h q (hq.trans le) ht

theorem LRS.FieldsEq.left {IH : LogRel Γ n} : LRS.FieldsEq IH Ts Xs Ys l → LRS.FieldsEq IH Ts Xs Xs l := by
  intro H; induction H with
  | nil => exact .nil
  | cons h1 h2 _ ih => exact .cons h1.hasType.1 h2.left ih
theorem LRS.FieldsEq.symm {IH : LogRel Γ n} : LRS.FieldsEq IH Ts Xs Ys l → LRS.FieldsEq IH Ts Ys Xs l := by
  intro H; induction H with
  | nil => exact .nil
  | cons h1 h2 _ ih => exact .cons h1.symm h2.symm ih
theorem LRS.FieldsEq.trans {IH : LogRel Γ n} :
    LRS.FieldsEq IH Ts Xs Ys l → LRS.FieldsEq IH Ts Ys Zs l → LRS.FieldsEq IH Ts Xs Zs l := by
  intro H1 H2; induction H1 generalizing Zs with
  | nil => cases H2; exact .nil
  | cons h1 h2 _ ih => cases H2 with | cons g1 g2 g3 => exact .cons (h1.trans g1) (h2.trans g2) (ih g3)
theorem LRS.FieldsEq.mono {IH : LogRel Γ n} :
    List.Forall₂ (· ≤ ·) l l' → LRS.FieldsEq IH Ts Xs Ys l' → LRS.FieldsEq IH Ts Xs Ys l := by
  intro hle H; induction H generalizing l with
  | nil => cases hle; exact .nil
  | cons h1 h2 _ ih => cases hle with | cons a b => exact .cons h1 (h2.mono a) (ih b)

theorem LRS.CtorDefEq.left {IH : LogRel Γ n} : LRS.CtorDefEq IH M N A c l → LRS.CtorDefEq IH M M A c l
  | ⟨I, ls, ci, Ts, Xs, _, hc, hI, hci, hty, hA, hM, _, hF⟩ =>
    ⟨I, ls, ci, Ts, Xs, Xs, hc, hI, hci, hty, hA, hM, hM, hF.left⟩
theorem LRS.CtorDefEq.symm {IH : LogRel Γ n} : LRS.CtorDefEq IH M N A c l → LRS.CtorDefEq IH N M A c l
  | ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, hA, hM, hN, hF⟩ =>
    ⟨I, ls, ci, Ts, Ys, Xs, hc, hI, hci, hty, hA, hN, hM, hF.symm⟩
/-- `trans`: the middle term's two constructor spines agree (`WHRedS.ctorSpine_determ`), and
the telescopes agree by `foldr_forallE_const_inj`. -/
theorem LRS.CtorDefEq.trans {IH : LogRel Γ n} : LRS.CtorDefEq IH M₁ M₂ A c l → LRS.CtorDefEq IH M₂ M₃ A c l →
    LRS.CtorDefEq IH M₁ M₃ A c l
  | ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, hA, hM₁, hM₂, hF⟩,
    ⟨_, ls', ci', Ts', Ys', Zs, _, _, hci', hty', _, hM₂', hM₃, hF'⟩ => by
    obtain ⟨rfl, rfl⟩ := WHRedS.ctorSpine_determ hc hM₂.2 hM₂'.2
    cases hci.symm.trans hci'
    obtain ⟨rfl, rfl, -⟩ := foldr_forallE_const_inj (hty.symm.trans hty')
    exact ⟨I, ls, ci, Ts, Xs, Zs, hc, hI, hci, hty, hA, hM₁, hM₃, hF.trans hF'⟩
theorem LRS.CtorDefEq.mono_l {IH : LogRel Γ n} (hle : List.Forall₂ (· ≤ ·) l l') :
    LRS.CtorDefEq IH M N A c l' → LRS.CtorDefEq IH M N A c l
  | ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, hA, hM, hN, hF⟩ =>
    ⟨I, ls, ci, Ts, Xs, Ys, (Lean4Lean.List.Forall₂.length_eq hle).symm ▸ hc, hI, hci, hty, hA,
      hM, hN, hF.mono hle⟩

/-- `whr` with typed reductions at the ambient type. -/
theorem LRS.CtorDefEq.whr {IH : LogRel Γ n} (hM : TWHRedS Γ M M' A) (hN : TWHRedS Γ N N' A) :
    LRS.CtorDefEq IH M N A c l ↔ LRS.CtorDefEq IH M' N' A c l := by
  constructor
  · intro ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, hA, hMs, hNs, hF⟩
    refine ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, hA, ⟨hM.1.symm.trans hMs.1, ?_⟩,
      ⟨hN.1.symm.trans hNs.1, ?_⟩, hF⟩
    · exact hM.2.determ_l hMs.2 (WHNF.ctorSpine hc Xs)
    · exact hN.2.determ_l hNs.2 (WHNF.ctorSpine hc Ys)
  · intro ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, hA, hMs, hNs, hF⟩
    exact ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, hA, ⟨hM.1.trans hMs.1, hM.2.trans hMs.2⟩,
      ⟨hN.1.trans hNs.1, hN.2.trans hNs.2⟩, hF⟩

/-- `conv` along the stage-1a `TyDefEq` at `indTy` (PLAN D2); the typed `A ≡ B` comes from
the clause's own `TyRedS Γ A (.const I ls)` and determinism of the whnf. -/
theorem LRS.CtorDefEq.conv {IH : LogRel Γ n}
    (hAB : ∃ (I : Name) (ls : List SLevel), Params.classify I = some (.indTy 0) ∧
      TyRedS Γ A (.const I ls) ∧ TyRedS Γ B (.const I ls)) :
    LRS.CtorDefEq IH M N A c l → LRS.CtorDefEq IH M N B c l
  | ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, hA, hM, hN, hF⟩ => by
    obtain ⟨I', ls', hI', ⟨⟨w₁, eA⟩, rA⟩, ⟨⟨w₂, eB⟩, rB⟩⟩ := hAB
    have e := hA.2.determ (WHNF.indTySpine (Xs := []) hI) rA (WHNF.indTySpine (Xs := []) hI')
    cases e
    have hAB' : Γ ⊢ A ≡ B : .sort w₁ := eA.trans' eB.symm
    exact ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, ⟨⟨w₂, eB⟩, rB⟩,
      ⟨hAB'.defeqDF hM.1, hM.2⟩, ⟨hAB'.defeqDF hN.1, hN.2⟩, hF⟩

/-- `trans'` needs no new premise: a sort ambient cannot reduce to an inductive constant. -/
theorem LRS.CtorDefEq.not_sort {IH : LogRel Γ n} : ¬ LRS.CtorDefEq IH M N (.sort u) c l
  | ⟨_, _, _, _, _, _, _, _, _, _, ⟨_, rA⟩, _⟩ => by cases WHNF.sort.whRedS rA

/-- Monotonicity of `LamDefEq` in the type-shape: increase. -/
theorem LRS.LamDefEq.mono_r_1 {IH : LogRel Γ n}
    (le₁ : a₁ ≤ a₁') (le₂ : a₂ ≤ a₂') (hm : WShape.HasTypeLam m a₁ a₂)
    (hm' : WShape.HasTypeLam m a₁' a₂') (piEV : LRS.PiDefEq IH A₁ A₂ A₂ a₁' a₂') :
    LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ → LRS.LamDefEq IH M N A₁ A₂ m a₁' a₂' := by
  have hm_d := WShape.HasDom.iff.1 hm.2.1
  have hm_f := WShape.HasTypeLam.iff.1 hm |>.2.2
  intro ⟨pav, pae⟩
  refine ⟨fun _ _ x hx ha a1 => ?_, fun _ x hx ha a1 => ?_⟩
  all_goals
    have ⟨x', le', hax, h1⟩ := hm_d x
    have hax' := hx.isType.mono_r le₁ hax
    have a1_x := IH.mono_l le' hax' hx a1
    have a1_down := IH.mono_r_2 le₁ hax hx.isType a1_x
    have hg_x := hm_f x' hax
    have hg_p := hg_x.mono_l (WShapeFun.app_mono_r le') h1
    have le_cod := (WShapeFun.app_mono_r le').trans (WShapeFun.app_mono_l le₂ _)
    have ht_cod := (WShape.HasTypePi.iff.1 hm'.1).2 x hx
    have hm_target := ht_cod.mono_r le_cod hg_p
  · have ⟨p1, p2⟩ := pav hax ha a1_down
    have tyA₂ := (piEV.1 hx ha.hasType.1 (IH.left a1)).1
    exact ⟨IH.mono_r_1 le_cod hg_p hm_target tyA₂ (IH.mono_l h1 hg_p hg_x p1),
           IH.mono_r_1 le_cod hg_p hm_target tyA₂ (IH.mono_l h1 hg_p hg_x p2)⟩
  · have q := pae hax ha a1_down
    have tyA₂ := piEV.2 hx ha a1
    exact IH.mono_r_1 le_cod hg_p hm_target tyA₂ (IH.mono_l h1 hg_p hg_x q)

/-- Type validity at element-shape `m` (merged `TyDefEq` / `EqTyDefEq`).
Non-trivial at `.forallE` (Pi injectivity) and `.sort` (sort injectivity). -/
def LRS.TyDefEq (IH : LogRel Γ n) (M N : SExpr) : WShape (n+1) → Prop
  | ⟨.bot, _⟩ | ⟨.lam _, _⟩ | ⟨.ctor _ _, _⟩ => True
  | ⟨.sort _, _⟩ => ∃ u, TyRedS Γ M (.sort u) ∧ TyRedS Γ N (.sort u)
  | ⟨.forallE b f, wf⟩ => LRS.ValTyPi2 IH M N ⟨b, wf.1⟩ ⟨f, wf.2⟩
  | ⟨.indTy, _⟩ => ∃ (I : Name) (ls : List SLevel), Params.classify I = some (.indTy 0) ∧
      TyRedS Γ M (.const I ls) ∧ TyRedS Γ N (.const I ls)

@[simp] theorem LRS.TyDefEq.bot : LRS.TyDefEq IH M N .bot := trivial
@[simp] theorem LRS.TyDefEq.sort_iff :
    LRS.TyDefEq (Γ := Γ) IH M N (.sort r) ↔ ∃ u, TyRedS Γ M (.sort u) ∧ TyRedS Γ N (.sort u) :=
  .rfl
@[simp] theorem LRS.TyDefEq.lam' : LRS.TyDefEq IH M N (.lam' f) := by
  unfold WShape.lam'; split <;> trivial
@[simp] theorem LRS.TyDefEq.ctor' : LRS.TyDefEq IH M N (.ctor' c l) := by
  unfold WShape.ctor'; split <;> trivial
@[simp] theorem LRS.TyDefEq.forallE_iff :
    LRS.TyDefEq (Γ := Γ) IH M N (.forallE b f) ↔ LRS.ValTyPi2 (Γ := Γ) IH M N b f := .rfl

theorem LRS.TyDefEq.left {IH : LogRel Γ n} :
    LRS.TyDefEq IH M N m → LRS.TyDefEq IH M M m := by
  dsimp [LRS.TyDefEq]; split <;> try trivial
  · intro ⟨u, hM, _⟩; exact ⟨u, hM, hM⟩
  · intro ⟨B₁, F₁, _, _, u, v, rM, _, hB, hF, hValB, hE⟩
    exact ⟨B₁, F₁, B₁, F₁, u, v, rM, rM, hB.hasType.1, hF.hasType.1, IH.left_ty hValB, hE.left⟩
  · intro ⟨I, ls, hI, hM, _⟩; exact ⟨I, ls, hI, hM, hM⟩

theorem LRS.TyDefEq.symm {IH : LogRel Γ n} :
    LRS.TyDefEq IH M N m → LRS.TyDefEq IH N M m := by
  dsimp [LRS.TyDefEq]; split <;> try trivial
  · intro ⟨u, hM, hN⟩; exact ⟨u, hN, hM⟩
  · intro ⟨_, _, _, _, _, _, rM, rN, hB, hF, hValB, hE1, hE2⟩
    have hValB' := IH.symm_ty hValB
    refine ⟨_, _, _, _, _, _, rN, rM, hB.symm, hB.defeqDF_l hF.symm,
      hValB', fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
    · exact (hE1 hp (hB.symm.defeqDF ha) (IH.conv hValB' a1)).symm
    · exact IH.symm_ty (hE2 hp (hB.symm.defeqDF ha) (IH.conv hValB' a1))
  · intro ⟨I, ls, hI, hM, hN⟩; exact ⟨I, ls, hI, hN, hM⟩

theorem LRS.TyDefEq.trans {IH : LogRel Γ n} :
    LRS.TyDefEq IH M₁ M₂ m → LRS.TyDefEq IH M₂ M₃ m → LRS.TyDefEq IH M₁ M₃ m := by
  dsimp [LRS.TyDefEq]; split <;> try trivial
  · intro ⟨u, hM₁, hM₂⟩ ⟨u', hM₂', hM₃⟩
    cases hM₂.2.determ .sort hM₂'.2 .sort; exact ⟨u, hM₁, hM₃⟩
  · intro ⟨B₁, F₁, B₂, F₂, u, v, rM₁, rM₂, hB₁₂, hF₁₂, hValB₁₂, hE1⟩
          ⟨_, _, B₃, F₃, u', v', rM₂', rM₃, hB₂₃, hF₂₃, hValB₂₃, hE2⟩
    cases rM₂.2.determ .forallE rM₂'.2 .forallE
    have hF₂₃' := hB₁₂.symm.defeqDF_l hF₂₃
    refine ⟨_, _, _, _, _, _, rM₁, rM₃, hB₁₂.trans' hB₂₃, hF₁₂.trans' hF₂₃',
      IH.trans_ty hValB₁₂ hValB₂₃, fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
    · exact ⟨(hE1.1 hp ha a1).1, (hE2.1 hp (hB₁₂.defeqDF ha) (IH.conv hValB₁₂ a1)).2⟩
    · exact IH.trans_ty (hE1.2 hp ha a1) (hE2.2 hp (hB₁₂.defeqDF ha) (IH.conv hValB₁₂ a1))
  · intro ⟨I, ls, hI, h₁, h₂⟩ ⟨I', ls', hI', h₂', h₃⟩
    cases h₂.2.determ (WHNF.indTySpine (Xs := []) hI) h₂'.2 (WHNF.indTySpine (Xs := []) hI')
    exact ⟨I, ls, hI, h₁, h₃⟩

/-- typed head reduction of both sides preserves `TyDefEq` (D6: the old `whr_ty` field proof,
with the reductions composed by `TyRedS.whnf_l`/`TyRedS.trans`) -/
theorem LRS.TyDefEq.whr {IH : LogRel Γ n} (hA : TyRedS Γ A A') (hB : TyRedS Γ B B') :
    LRS.TyDefEq IH A B m ↔ LRS.TyDefEq IH A' B' m := by
  cases m using WShape.casesOn' with
  | sort =>
    constructor <;> intro ⟨u, r1, r2⟩
    · exact ⟨u, hA.whnf_l r1 .sort, hB.whnf_l r2 .sort⟩
    · exact ⟨u, hA.trans r1, hB.trans r2⟩
  | forallE =>
    constructor <;> intro ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, rest⟩
    · exact ⟨B₁, F₁, B₂, F₂, u, v, hA.whnf_l rM .forallE, hB.whnf_l rN .forallE, rest⟩
    · exact ⟨B₁, F₁, B₂, F₂, u, v, hA.trans rM, hB.trans rN, rest⟩
  | indTy =>
    constructor <;> intro ⟨I, ls, hI, r1, r2⟩
    · exact ⟨I, ls, hI, hA.whnf_l r1 (WHNF.indTySpine (Xs := []) hI),
        hB.whnf_l r2 (WHNF.indTySpine (Xs := []) hI)⟩
    · exact ⟨I, ls, hI, hA.trans r1, hB.trans r2⟩
  | _ => rfl

theorem LRS.LamDefEq.left {IH : LogRel Γ n} :
    LRS.LamDefEq IH M N B F m m₁ m₂ → LRS.LamDefEq IH M M B F m m₁ m₂ := by
  refine fun hP => ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hP.1 hp ha a1).1, (hP.1 hp ha a1).1⟩
  · exact (hP.1 hp ha a1).1

theorem LRS.LamDefEq.symm {IH : LogRel Γ n} :
    LRS.LamDefEq IH M N B F m m₁ m₂ → LRS.LamDefEq IH N M B F m m₁ m₂ := by
  refine fun hP => ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hP.1 hp ha a1).2, (hP.1 hp ha a1).1⟩
  · exact IH.symm (hP.2 hp ha a1)

theorem LRS.LamDefEq.trans {IH : LogRel Γ n} :
    LRS.LamDefEq IH M₁ M₂ B F m m₁ m₂ →
    LRS.LamDefEq IH M₂ M₃ B F m m₁ m₂ → LRS.LamDefEq IH M₁ M₃ B F m m₁ m₂ := by
  refine fun ⟨hP1, hP2⟩ ⟨hP1', hP2'⟩ => ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hP1 hp ha a1).1, (hP1' hp ha a1).2⟩
  · exact IH.trans (hP2 hp ha a1) (hP2' hp ha a1)

theorem LRS.PiDefEq.mono_r_2 {IH : LogRel Γ n}
    (le₁ : b ≤ b') (le₂ : f ≤ f')
    (htpi : WShape.HasTypePi f b r) (htpi' : WShape.HasTypePi f' b' r')
    (hValA₁ : IH.TyDefEq A₁ A₁ b') :
    LRS.PiDefEq IH A₁ A₂ B₂ b' f' → LRS.PiDefEq IH A₁ A₂ B₂ b f
  | ⟨h1, h2⟩ => by
    have htpi_w := WShape.HasTypePi.iff.1 htpi
    have htpi'_w := WShape.HasTypePi.iff.1 htpi'
    refine ⟨fun _ _ x hp ha a1 => ?_, fun _ x hp ha a1 => ?_⟩
    all_goals
      have hp' := WShape.HasType.mono_r le₁ (WShape.HasDom.isType htpi'.1) hp
      have a2 := IH.mono_r_1 le₁ hp hp' hValA₁ a1
      have hm_tgt := (htpi_w.2 _ hp).toType; have hm_src := (htpi'_w.2 _ hp').toType
    · let ⟨t1, t2⟩ := h1 hp' ha a2
      exact ⟨IH.mono_r_2_ty (WShapeFun.app_mono_l le₂ x) hm_tgt hm_src t1,
             IH.mono_r_2_ty (WShapeFun.app_mono_l le₂ x) hm_tgt hm_src t2⟩
    · exact IH.mono_r_2_ty (WShapeFun.app_mono_l le₂ x) hm_tgt hm_src (h2 hp' ha a2)

theorem LRS.LamDefEq.mono_r_2 {IH : LogRel Γ n}
    (le₁ : a₁ ≤ a₁') (le₂ : a₂ ≤ a₂') (hm : WShape.HasTypeLam m a₁ a₂)
    (hValA₁ : IH.TyDefEq A₁ A₁ a₁') (htpi' : WShape.HasTypePi a₂' a₁' r') :
    LRS.LamDefEq IH M N A₁ A₂ m a₁' a₂' → LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ := by
  have hm_w := WShape.HasTypeLam.iff.1 hm
  have htpi'_w := WShape.HasTypePi.iff.1 htpi'
  intro ⟨h1, h2⟩
  refine ⟨fun _ _ x hp ha a1 => ?_, fun _ x hp ha a1 => ?_⟩
  all_goals
    have hp' := WShape.HasType.mono_r le₁ (WShape.HasDom.isType htpi'.1) hp
    have a1' := IH.mono_r_1 le₁ hp hp' hValA₁ a1
    have hm_tgt := hm_w.2.2 _ hp
    have ht_src := (htpi'_w.2 _ hp').toType
  · have ⟨d1, d2⟩ := h1 hp' ha a1'
    exact ⟨IH.mono_r_2 (WShapeFun.app_mono_l le₂ x) hm_tgt ht_src d1,
           IH.mono_r_2 (WShapeFun.app_mono_l le₂ x) hm_tgt ht_src d2⟩
  · have q := h2 hp' ha a1'
    exact IH.mono_r_2 (WShapeFun.app_mono_l le₂ _) hm_tgt ht_src q

/-- Monotonicity of `LamDefEq` in the element-shape: decrease. -/
theorem LRS.LamDefEq.mono_l {IH : LogRel Γ n}
    (le : m ≤ m') (hm : WShape.HasTypeLam m a₁ a₂)
    (hm' : WShape.HasTypeLam m' a₁ a₂) :
    LRS.LamDefEq IH M N A₁ A₂ m' a₁ a₂ → LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ := by
  have hm_w := WShape.HasTypeLam.iff.1 hm
  have hm'_w := WShape.HasTypeLam.iff.1 hm'
  intro ⟨pav, pae⟩
  refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  all_goals
    have hm_tgt := hm_w.2.2 _ hp
    have hm_src := hm'_w.2.2 _ hp
  · have ⟨d1, d2⟩ := pav hp ha a1
    exact ⟨IH.mono_l (WShapeFun.app_mono_l le _) hm_tgt hm_src d1,
           IH.mono_l (WShapeFun.app_mono_l le _) hm_tgt hm_src d2⟩
  · have q := pae hp ha a1
    exact IH.mono_l (WShapeFun.app_mono_l le _) hm_tgt hm_src q

/-- Join of `PiDefEq`: given edge validity at `(b₁, f₁)` and `(b₂, f₂)`,
produce edge validity at `(b₁.join b₂, f₁.join f₂)`.
Follows the same representative-based strategy as old `LRS.join`. -/
theorem LRS.PiDefEq.join {IH : LogRel Γ n}
    (htB₁ : b₁.HasType .type) (htB₂ : b₂.HasType .type)
    (hC_b : b₁.Compat b₂)
    (ht₁ : WShape.HasTypePi f₁ b₁ r₁) (ht₂ : WShape.HasTypePi f₂ b₂ r₂)
    (hC_f : WShapeFun.Compat f₁ f₂)
    (hE₁ : LRS.PiDefEq IH B₁ F₁ F₂ b₁ f₁)
    (hE₂ : LRS.PiDefEq IH B₁ F₁ F₂ b₂ f₂) :
    LRS.PiDefEq IH B₁ F₁ F₂ (b₁.join b₂) (f₁.join f₂) := by
  have hJ_b := WShape.Join.mk hC_b
  have htB_join := htB₁.join hC_b htB₂
  have hJ_f := WShapeFun.Join.mk hC_f
  have ht₁_w := WShape.HasTypePi.iff.1 ht₁
  have ht₂_w := WShape.HasTypePi.iff.1 ht₂
  have hd₁ := WShape.HasDom.iff.1 ht₁.1
  have hd₂ := WShape.HasDom.iff.1 ht₂.1
  refine ⟨fun _ _ p hp ha a1 => ?_, fun _ p hp ha a1 => ?_⟩
  all_goals
    obtain ⟨d_x, d_le, d_ht, d_app⟩ := hd₁ p
    have c2 := IH.mono_r_2 hJ_b.le.1 d_ht htB_join
      (IH.mono_l d_le (WShape.HasType.mono_r hJ_b.le.1 htB_join d_ht) hp a1)
    obtain ⟨e_x, e_le, e_ht, e_app⟩ := hd₂ p
    have c3 := IH.mono_r_2 hJ_b.le.2 e_ht htB_join
      (IH.mono_l e_le (WShape.HasType.mono_r hJ_b.le.2 htB_join e_ht) hp a1)
    have ht_f1 : (f₁.app p).HasType .type :=
      have ⟨_, _, hm⟩ := f₁.app_eq p; (ht₁.2 _ _ hm).toType
    have ht_f2 : (f₂.app p).HasType .type :=
      have ⟨_, _, hm⟩ := f₂.app_eq p; (ht₂.2 _ _ hm).toType
    have hJ_fp := hJ_f.app_l p
    have ⟨hC_fp, _, hC_fJ⟩ := WShape.Join.iff.1 hJ_fp
    have ht_fJ := ht_f1.join' hJ_fp ht_f2
    have ht_fJ' := ht_f1.join hC_fp ht_f2
    have cvt_d {A B} (h : IH.TyDefEq A B (f₁.app d_x)) : IH.TyDefEq A B (f₁.app p) :=
      IH.mono_r_2_ty d_app ht_f1 (ht₁_w.2 d_x d_ht).toType h
    have cvt_e {A B} (h : IH.TyDefEq A B (f₂.app e_x)) : IH.TyDefEq A B (f₂.app p) :=
      IH.mono_r_2_ty e_app ht_f2 (ht₂_w.2 e_x e_ht).toType h
  · constructor
    · exact IH.mono_r_2_ty hC_fJ ht_fJ ht_fJ' <| IH.join_ty hC_fp ht_f1 ht_f2
        (cvt_d (hE₁.1 d_ht ha c2).1) (cvt_e (hE₂.1 e_ht ha c3).1)
    · exact IH.mono_r_2_ty hC_fJ ht_fJ ht_fJ' <| IH.join_ty hC_fp ht_f1 ht_f2
        (cvt_d (hE₁.1 d_ht ha c2).2) (cvt_e (hE₂.1 e_ht ha c3).2)
  · exact IH.mono_r_2_ty hC_fJ ht_fJ ht_fJ' <| IH.join_ty hC_fp ht_f1 ht_f2
      (cvt_d (hE₁.2 d_ht ha c2)) (cvt_e (hE₂.2 e_ht ha c3))

/-- Typed head reduction on M, N preserves `LamDefEq` (D6; `TypedWhr.lean`'s
`LRS.LamDefEq.whr_typed`, with the typed `IH.whr` field in place of its `IHwhr` hypothesis).
The typed app congruences come from `hA` without `⊢ Γ`; the `X b` side uses `appDF` with the
pair `(a, b)`. -/
theorem LRS.LamDefEq.whr_typed {IH : LogRel Γ n}
    (hA : Γ ⊢ A ≡ .forallE A₁ A₂ : .sort w)
    (hM : TWHRedS Γ M M' A) (hN : TWHRedS Γ N N' A) :
    LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ ↔ LRS.LamDefEq IH M' N' A₁ A₂ m a₁ a₂ := by
  have hMP : Γ ⊢ M ≡ M' : .forallE A₁ A₂ := hA.defeqDF hM.1
  have hNP : Γ ⊢ N ≡ N' : .forallE A₁ A₂ := hA.defeqDF hN.1
  -- typed reductions of `X a` and `X b` at `A₂.inst a`, from `X ≡ X'` and `a ≡ b`
  have tyL {X X' : SExpr} (h : Γ ⊢ X ≡ X' : .forallE A₁ A₂) (r : Γ ⊢ X ⤳* X') {x y : SExpr}
      (hxy : Γ ⊢ x ≡ y : A₁) : TWHRedS Γ (X.app x) (X'.app x) (A₂.inst x) :=
    ⟨.appDF h hxy.hasType.1, .app r⟩
  have tyR {X X' : SExpr} (h : Γ ⊢ X ≡ X' : .forallE A₁ A₂) (r : Γ ⊢ X ⤳* X') {x y : SExpr}
      (hxy : Γ ⊢ x ≡ y : A₁) : TWHRedS Γ (X.app y) (X'.app y) (A₂.inst x) :=
    ⟨.trans (.symm (.appDF (.symm h) hxy)) (.appDF h.hasType.2 hxy), .app r⟩
  constructor <;> intro ⟨pav, pae⟩ <;> refine ⟨fun x y p hp hxy a1 => ?_, fun x p hp hx a1 => ?_⟩
  · have ⟨d1, d2⟩ := pav hp hxy a1
    exact ⟨(IH.whr (tyL hMP hM.2 hxy) (tyR hMP hM.2 hxy)).1 d1,
           (IH.whr (tyL hNP hN.2 hxy) (tyR hNP hN.2 hxy)).1 d2⟩
  · exact (IH.whr (tyL hMP hM.2 hx) (tyL hNP hN.2 hx)).1 (pae hp hx a1)
  · have ⟨d1, d2⟩ := pav hp hxy a1
    exact ⟨(IH.whr (tyL hMP hM.2 hxy) (tyR hMP hM.2 hxy)).2 d1,
           (IH.whr (tyL hNP hN.2 hxy) (tyR hNP hN.2 hxy)).2 d2⟩
  · exact (IH.whr (tyL hMP hM.2 hx) (tyL hNP hN.2 hx)).2 (pae hp hx a1)

/-- Term validity at `(m, a)`. -/
def LRS.DefEq (IH : LogRel Γ n) (M N A : SExpr) (m a : WShape (n+1)) : Prop :=
  match ha : a.1 with
  | .bot => True
  | .sort _ => match m.1 with
    | .bot => True
    | _ => AmbSort Γ A ∧ LRS.TyDefEq IH M N m
  | .forallE a₁ a₂ =>
    have wfa1 := (ha ▸ a.2).1; have wfa2 := (ha ▸ a.2).2
    match hm : m.1 with
    | .bot => True
    | .lam mg =>
      ∃ A₁ A₂ u v, TyRedS Γ A (.forallE A₁ A₂) ∧
      Γ ⊢ A₁ : .sort u ∧ IH.TyDefEq A₁ A₁ ⟨a₁, wfa1⟩ ∧ A₁::Γ ⊢ A₂ : sort v ∧
      LRS.PiDefEq IH A₁ A₂ A₂ ⟨a₁, wfa1⟩ ⟨a₂, wfa2⟩ ∧
      LRS.LamDefEq IH M N A₁ A₂ ⟨mg, (hm ▸ m.2).1⟩ ⟨a₁, wfa1⟩ ⟨a₂, wfa2⟩
    | _ => False
  | .indTy => match hm : m.1 with
    | .bot => True
    | .ctor c l => LRS.CtorDefEq IH M N A c (l.pmap Subtype.mk (hm ▸ m.2).1)
    | _ => False
  | _ => False

@[simp] theorem LRS.DefEq.bot_a : LRS.DefEq IH M N A m .bot = True := rfl
/-- D6 replaces the old `rfl` lemma `LRS.DefEq.sort_a` (false now) by two:
the `(⊥, sort)` row stays `True` ... -/
@[simp] theorem LRS.DefEq.bot_sort : LRS.DefEq IH M N A .bot (.sort r) = True := rfl
/-- ... and every other `(m, sort)` row carries the typed ambient `AmbSort Γ A`. -/
@[simp] theorem LRS.DefEq.sort_a {IH : LogRel Γ n} (hm : m ≠ .bot) :
    LRS.DefEq IH M N A m (.sort r) ↔ AmbSort Γ A ∧ LRS.TyDefEq IH M N m := by
  obtain ⟨⟨⟩, _⟩ := m <;> first | exact (hm rfl).elim | exact .rfl
/-- lifting a non-`⊥` shape up gives a non-`⊥` shape (D6 helper, for `LR.lift_succ_aux`) -/
theorem lift_ne_bot {s : WShape n} (le : n ≤ m) (h : s ≠ .bot) : s.lift m ≠ .bot := fun e =>
  h <| WShape.le_bot.1 <| (WShape.lift_le_lift (t := .bot) le).1 <| by
    rw [e, WShape.lift_bot]; exact WShape.le_bot.2 rfl
@[simp] theorem LRS.DefEq.bot_m : LRS.DefEq IH M N A .bot (.forallE a₁ a₂) = True := rfl
@[simp] theorem LRS.DefEq.lam_forallE (IH : LogRel Γ n) :
    LRS.DefEq IH M N A (.lam f hf) (.forallE a₁ a₂) ↔
    (∃ A₁ A₂ u v, TyRedS Γ A (.forallE A₁ A₂) ∧
      Γ ⊢ A₁ : .sort u ∧ IH.TyDefEq A₁ A₁ a₁ ∧ A₁::Γ ⊢ A₂ : sort v ∧
      LRS.PiDefEq IH A₁ A₂ A₂ a₁ a₂ ∧
      LRS.LamDefEq IH M N A₁ A₂ f a₁ a₂) := by
  show (∃ A₁ A₂ u v, _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ LRS.LamDefEq IH _ _ _ _ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩) ↔ _
  simp only [Subtype.eta]
@[simp] theorem LRS.DefEq.sort_forallE :
    LRS.DefEq IH M N A (.sort r) (.forallE a₁ a₂) ↔ False := .rfl
@[simp] theorem LRS.DefEq.forallE_forallE :
    LRS.DefEq IH M N A (.forallE b g) (.forallE a₁ a₂) ↔ False := .rfl
@[simp] theorem LRS.DefEq.ctor_forallE :
    LRS.DefEq IH M N A (.ctor c l h) (.forallE a₁ a₂) ↔ False := .rfl
@[simp] theorem LRS.DefEq.indTy_forallE :
    LRS.DefEq IH M N A .indTy (.forallE a₁ a₂) ↔ False := .rfl
@[simp] theorem LRS.DefEq.lam_a : LRS.DefEq IH M N A m (.lam f hf) ↔ False := .rfl
@[simp] theorem LRS.DefEq.ctor_a {c l h} :
    LRS.DefEq (n := n) IH M N A m (.ctor c l h) ↔ False := .rfl
@[simp] theorem LRS.TyDefEq.lam_m : LRS.TyDefEq IH M N (.lam f hf) ↔ True := .rfl
@[simp] theorem LRS.TyDefEq.ctor_m {c l h} :
    LRS.TyDefEq (n := n) IH M N (.ctor c l h) ↔ True := .rfl
/-- D2 replaces the old `rfl` lemma `LRS.TyDefEq.indTy_m` (`↔ True`, false now). -/
@[simp] theorem LRS.TyDefEq.indTy_m : LRS.TyDefEq (Γ := Γ) (n := n) IH M N .indTy ↔
    ∃ (I : Name) (ls : List SLevel), Params.classify I = some (.indTy 0) ∧
      TyRedS Γ M (.const I ls) ∧ TyRedS Γ N (.const I ls) := .rfl
/-- D1 replaces the old `rfl` lemma `LRS.DefEq.indTy_a` (`↔ True`, false now) by three:
the `(⊥, indTy)` row stays `True` ... -/
@[simp] theorem LRS.DefEq.bot_indTy : LRS.DefEq (n := n) IH M N A .bot .indTy = True := rfl
/-- ... the `(ctor c l, indTy)` row is the constructor clause ... -/
@[simp] theorem LRS.DefEq.ctor_indTy {IH : LogRel Γ n} {c l h} :
    LRS.DefEq IH M N A (.ctor c l h) .indTy ↔ LRS.CtorDefEq IH M N A c l := by
  show LRS.CtorDefEq IH M N A c ((l.map (·.1)).pmap Subtype.mk _) ↔ _
  rw [List.pmap_map]; simp only [Subtype.eta, List.pmap_eq_map, List.map_id']
/-- ... and every other row at `indTy` is `False`. -/
theorem LRS.DefEq.indTy_a {IH : LogRel Γ n} (h1 : m ≠ .bot) (h2 : ∀ c l h, m ≠ .ctor c l h) :
    LRS.DefEq IH M N A m .indTy ↔ False := by
  cases m using WShape.casesOn' with
  | bot => exact (h1 rfl).elim
  | ctor => exact (h2 _ _ _ rfl).elim
  | _ => exact .rfl

def LRS (IH : LogRel Γ n) : LogRel Γ (n+1) where
  DefEq := LRS.DefEq IH
  TyDefEq := LRS.TyDefEq IH
  sort_iff := .rfl
  sort_iff_ty := .rfl
  bot ha := by cases ha.unfold <;> trivial
  left_ty := .left
  left {M N A m a} := by
    dsimp [LRS.DefEq]; split <;> try trivial
    · split <;> try trivial
      exact fun ⟨hA, h⟩ => ⟨hA, h.left⟩
    · cases m using WShape.casesOn' with | lam => ?_ | _ => exact id
      intro ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩
      exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP.left⟩
    · split <;> try trivial
      exact LRS.CtorDefEq.left
  symm_ty := .symm
  symm {M N A m a} := by
    dsimp [LRS.DefEq]; split <;> try trivial
    · split <;> try trivial
      exact fun ⟨hA, h⟩ => ⟨hA, h.symm⟩
    · cases m using WShape.casesOn' with | lam => ?_ | _ => exact id
      intro ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩
      exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP.symm⟩
    · split <;> try trivial
      exact LRS.CtorDefEq.symm
  trans_ty := .trans
  trans {M₁ M₂ A m a M₃} := by
    dsimp [LRS.DefEq]; split <;> try trivial
    · split <;> try trivial
      exact fun ⟨hA, h⟩ ⟨_, h'⟩ => ⟨hA, h.trans h'⟩
    · split <;> try trivial
      intro ⟨B, F, u, v, rA, hA1, hA2, hA₂, hE, hP⟩ ⟨_, _, _, _, rA', _, _, _, _, hP'⟩
      cases rA.2.determ .forallE rA'.2 .forallE
      exact ⟨_, _, _, _, rA, hA1, hA2, hA₂, hE, hP.trans hP'⟩
    · split <;> try trivial
      exact LRS.CtorDefEq.trans
  trans' {A₁ A₂ u a s A₃ v r} := by
    dsimp [LRS.DefEq]; split <;> try intros; trivial
    · split <;> try intros; trivial
      exact fun ⟨hA, h⟩ ⟨_, h'⟩ => ⟨hA, h.trans h'⟩
    · split <;> try intros; trivial
      intro ⟨_, _, _, _, rA, _⟩; cases WHNF.sort.whRedS rA.2
    · split <;> try intros; trivial
      intro h; exact (LRS.CtorDefEq.not_sort h).elim
  conv {A A' a M N m} := by
    cases a using WShape.casesOn' with
    | sort r =>
      intro ⟨u, _, hA'⟩
      cases m using WShape.casesOn' with
      | bot => exact id
      | _ => exact fun ⟨_, h⟩ => ⟨hA'.ambSort, h⟩
    | forallE b f => ?_
    | indTy =>
      intro hAB
      cases m using WShape.casesOn' with
      | ctor c l h =>
        rw [LRS.DefEq.ctor_indTy, LRS.DefEq.ctor_indTy]; exact LRS.CtorDefEq.conv hAB
      | _ => exact id
    | _ => exact fun _ => id
    intro ⟨B, F, B', F', u, v, rA, rA', hBB', hFF', hValB, hEdge⟩
    cases m using WShape.casesOn' with | lam => ?_ | _ => exact id
    intro ⟨_, _, _, v', rA₁, hA1, hValA, hA₂, hEdge₁, hP⟩
    cases rA.2.determ .forallE rA₁.2 .forallE
    refine ⟨_, _, _, _, rA', hBB'.hasType.2, IH.left_ty (IH.symm_ty hValB),
      hBB'.defeqDF_l hFF'.hasType.2, ?_, ?_⟩
    · refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩ <;>
        have ha' := hBB'.symm.defeqDF ha
      · exact and_self_iff.2 (hEdge.1 hp ha' (IH.conv (IH.symm_ty hValB) a1)).2
      · exact (hEdge.1 hp ha' (IH.conv (IH.symm_ty hValB) a1)).2
    refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩ <;> (
      have a2 := IH.conv (IH.symm_ty hValB) a1
      have ha' := hBB'.symm.defeqDF ha
      have c := hEdge.2 hp ha'.hasType.1 (IH.left a2))
    · have ⟨v1, v2⟩ := hP.1 hp ha' a2; exact ⟨IH.conv c v1, IH.conv c v2⟩
    · exact IH.conv c (hP.2 hp ha' a2)
  toType {M N A m r} h := by
    cases m using WShape.casesOn' with
    | bot => trivial
    | _ => exact And.right h
  mono_r_2 {a a' M N A m} le hm ht h := by
    cases a using WShape.casesOn' with
    | bot => trivial
    | sort => cases WShape.sort_le.1 le; exact h
    | forallE a₁ a₂ =>
      obtain ⟨a₁', a₂', le1, le2, rfl⟩ := WShape.forallE_le.1 le
      cases m using WShape.casesOn' with
      | bot => simp [LRS.DefEq.bot_m]
      | lam f hf =>
        simp only [LRS.DefEq.lam_forallE] at h ⊢
        have ⟨_, hp, _⟩ := WShape.HasType.forallE_l.1 hm.isType
        have ⟨_, hp', _⟩ := WShape.HasType.forallE_l.1 ht
        obtain ⟨g, hg, hm'⟩ := WShape.HasType.forallE_inv hm
        have hgf : g = f := by
          have := congrArg (·.1) hg; simp only [WShape.lam, WShape.lam'] at this
          split at this
          · injection this with this; exact WShapeFun.ext this.symm
          · cases this
        subst hgf
        let ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hEdge, hP⟩ := h
        have ht := (WShape.HasTypePi.iff.1 hp).1.isType
        have ht' := (WShape.HasTypePi.iff.1 hp').1.isType
        refine ⟨A₁, A₂, u, v, rA, hA1, IH.mono_r_2_ty le1 ht ht' hA2, hA₂, ?_⟩
        exact ⟨hEdge.mono_r_2 le1 le2 hp hp' hA2, hP.mono_r_2 le1 le2 hm' hA2 hp'⟩
      | sort => simp [LRS.DefEq.sort_forallE] at h
      | forallE => simp [LRS.DefEq.forallE_forallE] at h
      | ctor => simp [LRS.DefEq.ctor_forallE] at h
      | indTy => simp [LRS.DefEq.indTy_forallE] at h
    | lam f hf => exact absurd hm.isType WShape.HasType.lam_isType
    | ctor => exact absurd hm.isType WShape.HasType.ctor_isType
    | indTy => cases WShape.indTy_le.1 le; exact h
  mono_r_2_ty {a a' A B} le ha ha' h := by
    cases a using WShape.casesOn' with
    | bot => trivial
    | sort => simp [LRS.TyDefEq] at h ⊢; cases WShape.sort_le.1 le; exact h
    | forallE a₁ a₂ =>
      simp [LRS.TyDefEq] at h ⊢
      obtain ⟨a₁', a₂', le1, le2, rfl⟩ := WShape.forallE_le.1 le
      have ⟨_, hp, _⟩ := WShape.HasType.forallE_l.1 ha
      have ⟨_, hp', _⟩ := WShape.HasType.forallE_l.1 ha'
      let ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, hBB', hFF', hValB, hEdge⟩ := h
      have ht := (WShape.HasTypePi.iff.1 hp).1.isType
      have ht' := (WShape.HasTypePi.iff.1 hp').1.isType
      refine ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, hBB', hFF', IH.mono_r_2_ty le1 ht ht' hValB, ?_⟩
      exact hEdge.mono_r_2 le1 le2 hp hp' (IH.left_ty hValB)
    | lam f hf => simp [LRS.TyDefEq.lam_m]
    | ctor => simp [LRS.TyDefEq.ctor_m]
    | indTy => cases WShape.indTy_le.1 le; exact h
  mono_r_1 {a a' A M N m} le ha ha' hA h := by
    cases a' using WShape.casesOn' with
    | bot => simp only [LRS.DefEq.bot_a]
    | sort r =>
      obtain rfl | rfl := WShape.le_sort.1 le
      · have := ha.bot_r; subst this; simp only [LRS.DefEq.bot_sort]
      · exact h
    | forallE a₁' a₂' =>
      obtain rfl | ⟨a₁, a₂, rfl, le1, le2⟩ := WShape.le_forallE_iff.1 le
      · have := ha.bot_r; subst this; simp only [LRS.DefEq.bot_m]
      · cases m using WShape.casesOn' with
        | bot => simp only [LRS.DefEq.bot_m]
        | lam f hf =>
          simp only [LRS.DefEq.lam_forallE] at h ⊢
          obtain ⟨g, hg, hm_lam⟩ := WShape.HasType.forallE_inv ha
          have hgf' : (WShape.lam f hf).1 = (WShape.lam' g).1 := congrArg (·.1) hg
          simp only [WShape.lam, WShape.lam'] at hgf'; split at hgf'
          · injection hgf' with hgf'
            have := WShapeFun.ext hgf'.symm; subst this  -- now f = g
            obtain ⟨g', hg', hm'_lam⟩ := WShape.HasType.forallE_inv ha'
            have hgf2 : (WShape.lam g hf).1 = (WShape.lam' g').1 := congrArg (·.1) hg'
            simp only [WShape.lam, WShape.lam'] at hgf2; split at hgf2
            · injection hgf2 with hgf2; have := WShapeFun.ext hgf2.symm; subst this
              let ⟨A₁, A₂, u, v, rA, hA1, hValA, hA₂, hEdge_src, hP⟩ := h
              let ⟨B₁, F₁, B₂, F₂, u', v', rA', rA'', hBB_tgt, hFF_tgt, hValB_tgt, hEdge_tgt⟩ := hA
              cases rA.2.determ .forallE rA'.2 .forallE
              cases rA.2.determ .forallE rA''.2 .forallE
              refine ⟨_, _, _, _, rA, hBB_tgt.hasType.1, hValB_tgt, hA₂, hEdge_tgt, ?_⟩
              exact hP.mono_r_1 le1 le2 hm_lam hm'_lam hEdge_tgt
            · cases hgf2
          · cases hgf'
        | sort => exact (LRS.DefEq.sort_forallE.1 h).elim
        | forallE => exact (LRS.DefEq.forallE_forallE.1 h).elim
        | ctor => exact (LRS.DefEq.ctor_forallE.1 h).elim
        | indTy => exact (LRS.DefEq.indTy_forallE.1 h).elim
    | lam f hf => exact absurd ha'.isType WShape.HasType.lam_isType
    | ctor => exact absurd ha'.isType WShape.HasType.ctor_isType
    | indTy =>
      obtain rfl | rfl := WShape.le_indTy.1 le
      · have := ha.bot_r; subst this; simp only [LRS.DefEq.bot_indTy]
      · exact h
  mono_l {m m' M N A a} le hm hm' h := by
    cases a using WShape.casesOn' with
    | bot => simp only [LRS.DefEq.bot_a]
    | sort r =>
      by_cases hm0 : m = .bot
      · subst hm0; simp only [LRS.DefEq.bot_sort]
      -- `m ≠ ⊥` and `m ≤ m'`, so `m' ≠ ⊥`: the ambient `AmbSort Γ A` is copied
      have hne : m' ≠ .bot := fun e => by subst e; exact hm0 (WShape.le_bot.1 le)
      obtain ⟨hA, h⟩ := (LRS.DefEq.sort_a hne).1 h
      refine (LRS.DefEq.sort_a hm0).2 ⟨hA, ?_⟩
      cases m using WShape.casesOn' with
      | bot => exact absurd rfl hm0
      | sort => cases WShape.sort_le.1 le; exact h
      | forallE s f =>
        obtain ⟨s', f', h1, h2, rfl⟩ := WShape.forallE_le.1 le
        simp only [LRS.TyDefEq.forallE_iff] at h ⊢
        have ⟨_, hm_pi, _⟩ := WShape.HasType.forallE_l.1 hm
        have ⟨_, hm'_pi, _⟩ := WShape.HasType.forallE_l.1 hm'
        let ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hBB', hFF', hValB, hEdge⟩ := h
        have ht := (WShape.HasTypePi.iff.1 hm_pi).1.isType
        have ht' := (WShape.HasTypePi.iff.1 hm'_pi).1.isType
        exact ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hBB', hFF', IH.mono_r_2_ty h1 ht ht' hValB,
          hEdge.mono_r_2 h1 h2 hm_pi hm'_pi (IH.left_ty hValB)⟩
      | lam => simp only [LRS.TyDefEq.lam_m]
      | ctor => simp only [LRS.TyDefEq.ctor_m]
      | indTy => cases WShape.indTy_le.1 le; exact h
    | forallE a₁ a₂ =>
      cases m using WShape.casesOn' with
      | bot => simp only [LRS.DefEq.bot_m]
      | lam f hf =>
        obtain ⟨g, hg, hm_lam⟩ := WShape.HasType.forallE_inv hm
        have hgf' : (WShape.lam f hf).1 = (WShape.lam' g).1 := congrArg (·.1) hg
        simp only [WShape.lam, WShape.lam'] at hgf'; split at hgf'
        · injection hgf' with hgf'; have := WShapeFun.ext hgf'.symm; subst this
          obtain ⟨g'', hg'', hm'_lam⟩ := WShape.HasType.forallE_inv hm'
          rw [hg''] at h
          by_cases hg''nz : g''.NonZero
          · rw [show WShape.lam' g'' = WShape.lam g'' hg''nz from
              (WShape.lam_eq_lam' (hl := hg''nz)).symm] at h
            simp only [LRS.DefEq.lam_forallE] at h ⊢
            rw [WShape.lam_eq_lam' (hl := hf), hg''] at le
            have le_g := WShape.lam'_le_lam'.1 le
            let ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩ := h
            exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP.mono_l le_g hm_lam hm'_lam⟩
          · simp only [WShape.lam', dif_neg hg''nz] at hg''
            cases WShape.le_bot.1 (hg'' ▸ le)
        · cases hgf'
      | _ => cases hm
    | indTy =>
      cases hm.unfold with
      | bot => simp only [LRS.DefEq.bot_indTy]
      | ctor =>
        obtain ⟨l', h', rfl, hle⟩ := WShape.ctor_le.1 le
        rw [LRS.DefEq.ctor_indTy] at h ⊢
        exact h.mono_l hle
    | _ => cases hm.isType
  join_ty {A B m₁ m₂} hC hm₁ hm₂ h1 h2 := by
    cases hm₁.unfold with
    | bot h₁ => rwa [WShape.bot_join]
    | sort =>
      cases hm₂.unfold with
      | bot => rwa [WShape.join_bot]
      | sort =>
        simp only [WShape.sort_join_sort] at h1 h2 ⊢
        split <;> simp_all only [LRS.TyDefEq.sort_iff, WShape.Compat.sort_sort]
      | _ => cases hC
    | forallE hp₁ =>
      cases hm₂.unfold with | bot => rwa [WShape.join_bot] | forallE hp₂ => ?_ | _ => cases hC
      simp only [LRS.TyDefEq.forallE_iff] at h1 h2
      simp [WShape.Compat, WShape.forallE, Shape.Compat] at hC
      let ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, hBB, hFF, hValB₁, hEdge₁⟩ := h1
      let ⟨_, _, _, _, u', v', rA', rB', hBB', hFF', hValB₂, hEdge₂⟩ := h2
      cases rA.2.determ .forallE rA'.2 .forallE
      cases rB.2.determ .forallE rB'.2 .forallE
      simp only [LRS.TyDefEq.forallE_iff, WShape.forallE_join_forallE hC.1 hC.2]
      have ht₁ := (WShape.HasTypePi.iff.1 hp₁).1.isType
      have ht₂ := (WShape.HasTypePi.iff.1 hp₂).1.isType
      refine ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, hBB, hFF, IH.join_ty hC.1 ht₁ ht₂ hValB₁ hValB₂, ?_⟩
      exact .join ht₁ ht₂ hC.1 hp₁ hp₂ hC.2 hEdge₁ hEdge₂
    | indTy => cases m₂ using WShape.casesOn' <;> trivial
  whr {M M' A N N' m a} hM hN := by
    cases a using WShape.casesOn' with
    | sort =>
      -- `(⊥, sort)` is `True`; elsewhere `AmbSort Γ A` turns `M ≡ M' : A` into a typed type
      -- reduction `TyRedS Γ M M'`, and the old `whr_ty` argument applies (`LRS.TyDefEq.whr`)
      by_cases hm : m = .bot
      · subst hm; exact .rfl
      · rw [LRS.DefEq.sort_a hm, LRS.DefEq.sort_a hm]
        exact and_congr_right fun hA => LRS.TyDefEq.whr (hM.toTyRedS hA) (hN.toTyRedS hA)
    | forallE =>
      cases m using WShape.casesOn' with | lam => ?_ | _ => rfl
      constructor <;> intro ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩ <;> obtain ⟨_, eA⟩ := rA.1
      · exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, (LRS.LamDefEq.whr_typed eA hM hN).1 hP⟩
      · exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, (LRS.LamDefEq.whr_typed eA hM hN).2 hP⟩
    | indTy =>
      cases m using WShape.casesOn' with | ctor => ?_ | _ => rfl
      rw [LRS.DefEq.ctor_indTy, LRS.DefEq.ctor_indTy]; exact LRS.CtorDefEq.whr hM hN
    | _ => rfl
  whr_ty := LRS.TyDefEq.whr

def LR (Γ : List SExpr) : LogRel Γ n :=
  match n with
  | 0 => LR0
  | _+1 => LRS (LR Γ)

@[simp] theorem LR_zero : LR (n := 0) Γ = LR0 := rfl
@[simp] theorem LR_succ : LR (n := n+1) Γ = LRS (LR Γ) := rfl

/-- The new case of `LR.lift_succ_aux` for the constructor clause's fields (both directions;
`docs/const-case/plan/historical/CtorClause1a.lean`). -/
theorem LRS.FieldRel.lift_aux {Γ : List SExpr} {X Y T : SExpr} : ∀ {k} {p : WShape k},
    (∀ {M N A : SExpr} {m a : WShape k}, m.HasType a →
      ((LR Γ (n := k+1)).DefEq M N A (m.lift (k+1)) (a.lift (k+1)) ↔ (LR Γ (n := k)).DefEq M N A m a)) →
    (LRS.FieldRel (LR Γ (n := k+1)) X Y T (p.lift (k+1)) ↔ LRS.FieldRel (LR Γ (n := k)) X Y T p)
  | 0, p, _ => by
    refine ⟨fun _ => trivial, fun _ q hq ht => ?_⟩
    cases ht.unfold with
    | bot _ => exact (LR Γ).bot .indTy
    | @ctor _ c l wf =>
      exfalso
      obtain ⟨_, _, he, _⟩ := WShape.ctor_le.1 hq
      cases p using WShape.casesOn with
      | bot => rw [WShape.lift_bot] at he; cases congrArg (·.1) he
      | sort => rw [WShape.lift_sort] at he; cases congrArg (·.1) he
  | j+1, p, IH2 => by
    constructor
    · intro H q₀ hq₀ ht₀
      have hl : (q₀.lift (j+2)).HasType ((WShape.indTy : WShape (j+1)).lift (j+2)) :=
        (WShape.HasType.lift (Nat.le_succ _)).2 ht₀
      rw [WShape.lift_indTy] at hl
      have := H _ (WShape.lift_mono (Nat.le_succ _) hq₀) hl
      rw [← WShape.lift_indTy (n := j) (m := j+1)] at this
      exact (IH2 ht₀).1 this
    · intro H q hq ht
      cases ht.unfold with
      | bot _ => exact (LR Γ).bot .indTy
      | @ctor _ c l wf =>
        obtain ⟨l', h', he, _⟩ := WShape.ctor_le.1 hq
        have hpl : (p.lift (j+2)).HasType ((WShape.indTy : WShape (j+1)).lift (j+2)) := by
          rw [WShape.lift_indTy, he]; exact .ctor
        have hp : p.HasType .indTy := (WShape.HasType.lift (Nat.le_succ _)).1 hpl
        have d := (IH2 hp).2 (H p .rfl hp)
        rw [WShape.lift_indTy] at d hpl
        exact (LR Γ).mono_l hq ht hpl d

theorem LRS.FieldsEq.lift_aux {Γ : List SExpr} {k}
    (IH2 : ∀ {M N A : SExpr} {m a : WShape k}, m.HasType a →
      ((LR Γ (n := k+1)).DefEq M N A (m.lift (k+1)) (a.lift (k+1)) ↔ (LR Γ (n := k)).DefEq M N A m a)) :
    ∀ {Ts Xs Ys : List SExpr} {l : List (WShape k)},
    LRS.FieldsEq (LR Γ (n := k+1)) Ts Xs Ys (l.map (·.lift (k+1))) ↔
      LRS.FieldsEq (LR Γ (n := k)) Ts Xs Ys l
  | [], [], [], [] => ⟨fun _ => .nil, fun _ => .nil⟩
  | T :: Ts, X :: Xs, Y :: Ys, p :: l => by
    constructor
    · intro H; cases H with
      | cons h1 h2 h3 =>
        exact .cons h1 ((LRS.FieldRel.lift_aux IH2).1 h2) ((LRS.FieldsEq.lift_aux IH2).1 h3)
    · intro H; cases H with
      | cons h1 h2 h3 =>
        exact .cons h1 ((LRS.FieldRel.lift_aux IH2).2 h2) ((LRS.FieldsEq.lift_aux IH2).2 h3)
  | [], _ :: _, _, _ | [], [], _ :: _, _ | [], [], [], _ :: _ => ⟨nofun, nofun⟩
  | _ :: _, [], _, _ | _ :: _, _ :: _, [], _ | _ :: _, _ :: _, _ :: _, [] => ⟨nofun, nofun⟩

theorem LRS.CtorDefEq.lift_aux {Γ : List SExpr} {k} {M N A : SExpr} {c : Name} {l : List (WShape k)}
    (IH2 : ∀ {M N A : SExpr} {m a : WShape k}, m.HasType a →
      ((LR Γ (n := k+1)).DefEq M N A (m.lift (k+1)) (a.lift (k+1)) ↔ (LR Γ (n := k)).DefEq M N A m a)) :
    LRS.CtorDefEq (LR Γ (n := k+1)) M N A c (l.map (·.lift (k+1))) ↔
      LRS.CtorDefEq (LR Γ (n := k)) M N A c l := by
  constructor
  · intro ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, hA, hM, hN, hF⟩
    exact ⟨I, ls, ci, Ts, Xs, Ys, by simpa using hc, hI, hci, hty, hA, hM, hN,
      (LRS.FieldsEq.lift_aux IH2).1 hF⟩
  · intro ⟨I, ls, ci, Ts, Xs, Ys, hc, hI, hci, hty, hA, hM, hN, hF⟩
    exact ⟨I, ls, ci, Ts, Xs, Ys, by simpa using hc, hI, hci, hty, hA, hM, hN,
      (LRS.FieldsEq.lift_aux IH2).2 hF⟩

private theorem LRS.PiDefEq.lift_aux
    {b : WShape n} {f : WShapeFun n} (le : n ≤ n') (htpi_a : WShape.HasTypePi f b true)
    (IH1 : ∀ {M N : SExpr} {m : WShape n}, WShape.HasType m .type →
      ((LR Γ).TyDefEq M N (m.lift n') ↔ (LR Γ).TyDefEq M N m))
    (IH2 : ∀ {M N A : SExpr} {m a : WShape n}, WShape.HasType m a →
      ((LR Γ).DefEq M N A (m.lift n') (a.lift _) ↔ (LR Γ).DefEq M N A m a)) :
    LRS.PiDefEq (LR Γ) B F₁ F₂ (b.lift n') (f.lift n') ↔
    LRS.PiDefEq (LR Γ) B F₁ F₂ b f := by
  have htpi_w := WShape.HasTypePi.iff.1 htpi_a
  constructor <;> intro hEdge
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      have hp' := (WShape.HasType.lift le).2 hp
      have v' := (IH2 hp).2 v)
    · have ⟨r1, r2⟩ := hEdge.1 hp' ha v'
      exact ⟨(IH1 (htpi_w.2 _ hp)).1 (WShapeFun.lift_app le ▸ r1),
             (IH1 (htpi_w.2 _ hp)).1 (WShapeFun.lift_app le ▸ r2)⟩
    · exact (IH1 (htpi_w.2 _ hp)).1 (WShapeFun.lift_app le ▸ hEdge.2 hp' ha v')
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      obtain ⟨q, d1, d2⟩ := WShapeFun.app_eq (f.lift n') _
      obtain ⟨q₀, y₀, d2₀, rfl, d3⟩ := (WShapeFun.mem_lift le).1 d2
      obtain ⟨qx', qy', d2₀', qxle, qyle, hq⟩ := WShape.HasDom.def.1 htpi_a.1 _ _ d2₀
      have v' := (IH2 hq).1 ((LR Γ).mono_l (((WShape.lift_le_lift le).2 qxle).trans d1)
        ((WShape.HasType.lift le).2 hq) hp v))
    · have ⟨r1, r2⟩ := hEdge.1 hq ha v'
      have ht_q := (htpi_w.2 _ hq).toType
      have ht_y₀ : (y₀ : WShape n).HasType WShape.type := (htpi_a.2 _ _ d2₀).toType
      have y₀_le_fqx : y₀ ≤ f.app qx' := qyle.trans (f.app_of_mem d2₀').2
      have ht_q_l : ((f.app qx').lift n').HasType WShape.type := by
        have := (WShape.HasType.lift le).2 ht_q; rwa [WShape.lift_sort] at this
      have ht_y₀_l : (y₀.lift n').HasType WShape.type := by
        have := (WShape.HasType.lift le).2 ht_y₀; rwa [WShape.lift_sort] at this
      exact d3 ▸ ⟨
        (LR Γ).mono_r_2_ty (WShape.lift_mono le y₀_le_fqx) ht_y₀_l ht_q_l ((IH1 ht_q).2 r1),
        (LR Γ).mono_r_2_ty (WShape.lift_mono le y₀_le_fqx) ht_y₀_l ht_q_l ((IH1 ht_q).2 r2)⟩
    · have hq_body := hEdge.2 hq ha v'
      have ht_q := (htpi_w.2 _ hq).toType
      have ht_y₀ : (y₀ : WShape n).HasType WShape.type := (htpi_a.2 _ _ d2₀).toType
      have y₀_le_fqx : y₀ ≤ f.app qx' := qyle.trans (f.app_of_mem d2₀').2
      have ht_q_l : ((f.app qx').lift n').HasType WShape.type := by
        have := (WShape.HasType.lift le).2 ht_q; rwa [WShape.lift_sort] at this
      have ht_y₀_l : (y₀.lift n').HasType WShape.type := by
        have := (WShape.HasType.lift le).2 ht_y₀; rwa [WShape.lift_sort] at this
      exact d3 ▸
        (LR Γ).mono_r_2_ty (WShape.lift_mono le y₀_le_fqx) ht_y₀_l ht_q_l ((IH1 ht_q).2 hq_body)

private theorem LRS.LamDefEq.lift_aux
    {g : WShapeFun n} {a₁ a₂} (le : n ≤ n') (htm : WShape.HasTypeLam g a₁ a₂)
    (IH : ∀ {M N A : SExpr} {m a : WShape n}, WShape.HasType m a →
      ((LR Γ).DefEq M N A (m.lift n') (a.lift _) ↔ (LR Γ).DefEq M N A m a))
    (hEdge : LRS.PiDefEq (LR Γ) A₁ A₂ A₂ a₁ a₂) :
    LRS.LamDefEq (LR Γ) (n := n') M N A₁ A₂ (g.lift n') (a₁.lift n') (a₂.lift n') ↔
    LRS.LamDefEq (LR Γ) M N A₁ A₂ g a₁ a₂ := by
  have htm_w := WShape.HasTypeLam.iff.1 htm
  constructor <;> intro hP
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      have hp' := (WShape.HasType.lift le).2 hp
      have v' := (IH hp).2 v)
    · have ⟨r1, r2⟩ := hP.1 hp' ha v'
      refine ⟨(IH (htm_w.2.2 _ hp)).1 ?_, (IH (htm_w.2.2 _ hp)).1 ?_⟩
        <;> rw [WShapeFun.lift_app le, WShapeFun.lift_app le] <;> [exact r1; exact r2]
    · apply (IH (htm_w.2.2 _ hp)).1
      rw [WShapeFun.lift_app le, WShapeFun.lift_app le]
      exact hP.2 hp' ha v'
  · refine ⟨fun a' b' p hp ha v => ?_, fun a' p hp ha v => ?_⟩
    all_goals
      obtain ⟨_, dg1, dg2⟩ := WShapeFun.app_eq (g.lift n') p
      obtain ⟨_, da1, da2⟩ := WShapeFun.app_eq (a₂.lift n') p
      obtain ⟨qg, yg, dg2₀, rfl, dg3⟩ := (WShapeFun.mem_lift le).1 dg2
      obtain ⟨qa, ya, da2₀, rfl, da3⟩ := (WShapeFun.mem_lift le).1 da2
      have ⟨yg₁, yg₂⟩ := WShapeFun.app_of_mem dg2₀
      have ⟨ya₁, ya₂⟩ := WShapeFun.app_of_mem da2₀
      have ⟨qg', qg'le, hqg, qg'app⟩ := WShape.HasDom.iff.1 htm.2.1 qg
      have ⟨qa', qa'le, hqa, qa'app⟩ := WShape.HasDom.iff.1 htm.1.1 qa
      rw [dg3, da3]
      have v_lo := (IH hqg).1 <| (LR Γ).mono_l
        (((WShape.lift_le_lift le).2 qg'le).trans dg1) ((WShape.HasType.lift le).2 hqg) hp v
      have v_lo_qa := (IH hqa).1 <| (LR Γ).mono_l
        (((WShape.lift_le_lift le).2 qa'le).trans da1) ((WShape.HasType.lift le).2 hqa) hp v
      have ht_lo := htm_w.2.2 _ hqg
      have htm_p := WShape.HasTypePi.iff'.1 htm_w.1
      have vt_qa := hEdge.2 hqa ha.hasType.1 ((LR Γ).left v_lo_qa)
      have vt_qa' := (LR Γ).mono_r_2_ty qa'app (htm_p.2 qa) (htm_p.2 qa') vt_qa
      have ya_sort := (htm_p.2 qa).mono_l ya₁ ya₂
      have ht_yg_qg' : yg.HasType (a₂.app qg') :=
        ht_lo.mono_l (WShapeFun.app_mono_r qg'le |>.trans yg₁) (yg₂.trans qg'app)
      have le_a2_ya := by
        refine (a₂.app_mono_r qg'le).trans (.trans ?_ ya₁)
        rw [← WShape.lift_le_lift le, WShapeFun.lift_app le]
        exact (WShapeFun.app_mono_r dg1 (f := a₂.lift n')).trans <| da3 ▸ WShape.lift_mono le ya₂
      have ya_sort := (htm_p.2 qa).mono_l ya₁ ya₂
      have ht_yg := ya_sort.mono_r le_a2_ya ht_yg_qg'
      have vt_ya := (LR Γ).mono_r_2_ty ya₂ ya_sort (htm_p.2 qa) vt_qa'
      have go {M N} (r : (LR Γ).DefEq M N (A₂.inst a') (g.app qg') (a₂.app qg')) :
          (LR Γ).DefEq M N (A₂.inst a') (yg.lift n') (ya.lift n') :=
        (IH ht_yg).2 <|
        (LR Γ).mono_r_1 le_a2_ya ht_yg_qg' ht_yg vt_ya <|
        (LR Γ).mono_l (yg₂.trans qg'app) ht_yg_qg' ht_lo r
    · have ⟨r1, r2⟩ := hP.1 hqg ha v_lo; exact ⟨go r1, go r2⟩
    · exact go (hP.2 hqg ha v_lo)

private theorem LR.lift_succ_aux :
    (∀ {M N : SExpr} {m : WShape n}, WShape.HasType m .type →
      (LRS.TyDefEq (n := n) (LR Γ) M N (m.lift _) ↔ (LR Γ).TyDefEq M N m)) ∧
    (∀ {M N A : SExpr} {m a : WShape n}, WShape.HasType m a →
      (LRS.DefEq (n := n) (LR Γ) M N A (m.lift _) (a.lift _) ↔ (LR Γ).DefEq M N A m a)) := by
  induction n with
  | zero =>
    refine ⟨fun {M N m} _ => ?_, fun {M N A m a} _ => ?_⟩
    · cases m using WShape.casesOn <;> trivial
    · cases m using WShape.casesOn <;> cases a using WShape.casesOn <;> trivial
  | succ k ih =>
    refine have h1 := ?_; ⟨h1, ?_⟩
    · intro M N m hmt
      cases m using WShape.casesOn' with
      | forallE b f => ?_ | _ => constructor <;> intro <;> trivial
      rw [WShape.lift_forallE (Nat.le_succ k)]
      have ⟨_, htpi, rfl⟩ := WShape.HasType.forallE_l.1 hmt
      constructor <;> intro ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hB, hF, hValB, hE⟩ <;>
        refine ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hB, hF, ?_, ?_⟩
      · exact (ih.1 (WShape.HasTypePi.iff.1 htpi).1.isType).1 hValB
      · exact (LRS.PiDefEq.lift_aux (Nat.le_succ k) htpi ih.1 ih.2).1 hE
      · exact (ih.1 (WShape.HasTypePi.iff.1 htpi).1.isType).2 hValB
      · exact (LRS.PiDefEq.lift_aux (Nat.le_succ k) htpi ih.1 ih.2).2 hE
    · intro M N A m a hma
      cases a using WShape.casesOn' with
      | bot => constructor <;> intro <;> trivial
      | indTy =>
        -- D1: `m` is `⊥` (both sides `True`) or `ctor c l` (`LRS.CtorDefEq.lift_aux`)
        rw [WShape.lift_indTy]
        cases hma.unfold with
        | bot => rw [WShape.lift_bot]; exact ⟨fun _ => trivial, fun _ => trivial⟩
        | @ctor _ c l wf =>
          rw [WShape.lift_ctor (Nat.le_succ k), LRS.DefEq.ctor_indTy]
          exact (LRS.CtorDefEq.lift_aux ih.2).trans (LRS.DefEq.ctor_indTy (h := wf)).symm
      | sort r =>
        -- D6: the `(⊥, sort)` row is `True` on both sides; elsewhere `AmbSort Γ A` is copied
        rw [WShape.lift_sort]
        by_cases hm : m = .bot
        · subst hm; rw [WShape.lift_bot]; exact ⟨fun _ => trivial, fun _ => trivial⟩
        · exact (LRS.DefEq.sort_a (lift_ne_bot (Nat.le_succ _) hm)).trans <|
            (and_congr_right fun _ => h1 hma.toType).trans (LRS.DefEq.sort_a (r := r) hm).symm
      | forallE a₁ a₂ => ?_ | _ => cases hma.isType
      have ⟨_, htpi_a, _⟩ := WShape.HasType.forallE_l.1 hma.isType
      obtain ⟨g, rfl, htm⟩ := WShape.HasType.forallE_inv hma
      unfold WShape.lam'; split <;> [skip; (simp; trivial)]
      rw [WShape.lift_lam (Nat.le_succ k), WShape.lift_forallE (Nat.le_succ k)]
      simp only [LRS.DefEq.lam_forallE]
      constructor <;> intro ⟨A₁, A₂, u, v, rA, hA1, hValA, hA₂, hEdge, hP⟩ <;>
        [ have hEdge' := (LRS.PiDefEq.lift_aux (Nat.le_succ k) htm.1 ih.1 ih.2).1 hEdge;
          have hEdge' := (LRS.PiDefEq.lift_aux (Nat.le_succ k) htm.1 ih.1 ih.2).2 hEdge ] <;>
        refine ⟨A₁, A₂, u, v, rA, hA1, ?_, hA₂, hEdge', ?_⟩
      · exact (ih.1 (WShape.HasTypePi.iff.1 htpi_a).1.isType).1 hValA
      · exact (LRS.LamDefEq.lift_aux (Nat.le_succ k) htm ih.2 hEdge').1 hP
      · exact (ih.1 (WShape.HasTypePi.iff.1 htpi_a).1.isType).2 hValA
      · exact (LRS.LamDefEq.lift_aux (Nat.le_succ k) htm ih.2 hEdge).2 hP

theorem LR.DefEq.lift {m a : WShape n} (le : n ≤ n') (hma : WShape.HasType m a) :
    (LR Γ).DefEq M N A (m.lift n') (a.lift _) ↔ (LR Γ).DefEq M N A m a := by
  induction le with | refl => simp [WShape.lift_self] | step le ih
  rw [(WShape.lift_lift (.inl le)).symm, (WShape.lift_lift (s := a) (.inl le)).symm]
  exact (LR.lift_succ_aux.2 ((WShape.HasType.lift le).2 hma)).trans ih

theorem LR.TyDefEq.lift {m : WShape n} (le : n ≤ n') (hmt : WShape.HasType m .type) :
    (LR Γ).TyDefEq (n := n') M N (m.lift _) ↔ (LR Γ).TyDefEq M N m := by
  induction le with | refl => simp [WShape.lift_self] | step le ih
  rw [(WShape.lift_lift (.inl le)).symm]
  have := (WShape.HasType.lift le).2 hmt
  simp [WShape.type] at this
  exact (LR.lift_succ_aux.1 this).trans ih


def LR.Subst1 (Γ₀ : List SExpr) (x x' A₀ A A' : SExpr) (ρ : Valuation) (i := 0) : Prop :=
  Γ₀ ⊢ x ≡ x' : A ∧ ∀ {{n}} (a : WShape n), LE_Interp ρ a.T A₀ →
    (a.HasType .type → (∃ u, Γ₀ ⊢ A ≡ A' : .sort u) ∧ (LR Γ₀).TyDefEq A A' a) ∧
    ∀ {{m : WShape n}}, LE_Interp ρ m.T (.bvar i) → m.HasType a → (LR Γ₀).DefEq x x' A m a

inductive LR.SubstWF (Γ₀ : List SExpr) : Subst → Subst → List SExpr → Valuation → Prop where
  | id : ⊢ Γ₀ → LR.SubstWF Γ₀ .id .id Γ₀ .nil
  | cons : LR.SubstWF Γ₀ σ.tail σ'.tail Γ ρ →
    (∀ {a}, LE_Interp ρ a A →
      ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type) →
    LE_Interp ρ a A → x.HasType a → Γ ⊢ A : .sort u →
    LR.Subst1 Γ₀ σ.head σ'.head A.lift (A.subst σ.tail) (A.subst σ'.tail) (ρ.push x) →
    LR.SubstWF Γ₀ σ σ' (A :: Γ) (ρ.push x)

theorem LR.SubstWF.fits : LR.SubstWF Γ₀ σ σ' Γ ρ → ρ.Fits Γ₀ Γ
  | .id _ => .nil
  | .cons W h1 h2 h3 _ _ => .cons W.fits h1 h2 h3

theorem LR.SubstWF.toSubstEq : LR.SubstWF Γ₀ σ σ' Γ ρ → Ctx.SubstEq Γ₀ σ σ' Γ
  | .id _ => .nil
  | .cons W _ _ _ hA h0 => .cons W.toSubstEq hA h0.1

/-- The target context of a well-formed substitution is well formed. -/
theorem LR.SubstWF.wf₀ : LR.SubstWF Γ₀ σ σ' Γ ρ → ⊢ Γ₀
  | .id h => h
  | .cons W _ _ _ _ _ => W.wf₀

/-- The source context of a well-formed substitution is well formed. -/
theorem LR.SubstWF.wf : LR.SubstWF Γ₀ σ σ' Γ ρ → ⊢ Γ
  | .id h => h
  | .cons W _ _ _ hA _ => ⟨W.wf, _, hA⟩

theorem LR.SubstWF.left (W : LR.SubstWF Γ₀ σ σ' Γ ρ) : LR.SubstWF Γ₀ σ σ Γ ρ := by
  induction W with
  | id h => exact .id h
  | cons _ h1 h2 h3 hA h0 ih =>
    refine .cons ih h1 h2 h3 hA ⟨h0.1.hasType.1, fun _ a ha => ⟨fun ht => ?_, fun _ hM hmem => ?_⟩⟩
    · have ⟨⟨_, h1⟩, h2⟩ := (h0.2 a ha).1 ht; exact ⟨⟨_, h1.hasType.1⟩, (LR _).left_ty h2⟩
    · exact (LR _).left <| (h0.2 a ha).2 hM hmem

theorem LR.SubstWF.symm (W : LR.SubstWF Γ₀ σ σ' Γ ρ) : LR.SubstWF Γ₀ σ' σ Γ ρ := by
  induction W with
  | id h => exact .id h
  | cons _ h1 h2 h3 hA h0 ih =>
    refine .cons ih h1 h2 h3 hA ⟨?_, fun _ a ha => ⟨fun ht => ?_, fun _ hM hmem => ?_⟩⟩
    · have ⟨⟨_, h1⟩, _⟩ := (h0.2 (n := 0) _ .bot).1 (.bot .sort)
      exact h1.defeqDF h0.1.symm
    · exact let ⟨⟨u, h1⟩, h2⟩ := (h0.2 a ha).1 ht; ⟨⟨u, h1.symm⟩, (LR _).symm_ty h2⟩
    · let ⟨_, h2⟩ := (h0.2 a ha).1 hmem.isType
      exact (LR _).conv h2 ((LR _).symm ((h0.2 a ha).2 hM hmem))

end Lean4Lean.SExpr.T
