import Lean4Lean.Experimental.E3.Measure7
/-! Sanity check (not a deliverable): `Pattern.gen` on the `Nat` environment of
`docs/params/NatParams.lean` (definitions copied: docs files are not importable), checked by `rfl`.
The succ rule's generated `ctx`/`lhs`/`rhs`/`type` are exactly the open body of NatParams'
λ-wrapped `iotaSuccLam` (4 binders stripped), and the recursive call is the one self occurrence. -/
namespace Lean4Lean.GenNat
open Lean (Name)

def natTy : VExpr := .const ``Nat []
def natCI  : VConstant := ⟨0, .sort (.succ .zero)⟩
def zeroCI : VConstant := ⟨0, natTy⟩
def succCI : VConstant := ⟨0, .forallE natTy natTy⟩
def motiveTy : VExpr := .forallE natTy (.sort (.param 0))
def zTy : VExpr := .app (.bvar 0) (.const ``Nat.zero [])
def sTy : VExpr := .forallE natTy (.forallE (.app (.bvar 2) (.bvar 0))
  (.app (.bvar 3) (.app (.const ``Nat.succ []) (.bvar 1))))
def recCI : VConstant := ⟨1,
  .forallE motiveTy (.forallE zTy (.forallE sTy (.forallE natTy (.app (.bvar 3) (.bvar 0)))))⟩

def env : VEnv where
  constants c :=
    if c = ``Nat then some natCI else if c = ``Nat.zero then some zeroCI else
    if c = ``Nat.succ then some succCI else if c = ``Nat.rec then some recCI else none
  defeqs _ := False

def classify (c : Name) : Option Classification :=
  if c = ``Nat then some (.indTy 0) else
  if c = ``Nat.zero then some (.ctor 0) else
  if c = ``Nat.succ then some (.ctor 1) else
  if c = ``Nat.rec then some (.symb 4) else none

def rank (c : Name) : Nat :=
  if c = ``Nat then 0 else if c = ``Nat.zero then 1 else if c = ``Nat.succ then 1 else 2

def recPre : Pattern := .var (.var (.var (.const ``Nat.rec)))
def zeroPat : Pattern := (SimplePattern.iota ``Nat.rec 3 ``Nat.zero 0).toPattern
def succPat : Pattern := (SimplePattern.iota ``Nat.rec 3 ``Nat.succ 1).toPattern
def pS      : recPre.Path := none
def pZ      : recPre.Path := some none
def pMotive : recPre.Path := some (some none)
def zeroRHS : zeroPat.RHS := .var (.inl pZ)
def succRHS : succPat.RHS :=
  let n : succPat.Path := .inr none
  .app (.app (.var (.inl pS)) (.var n))
    (.app (.app (.app (.app (.fixed (.const ``Nat.rec [.param 0]) trivial)
      (.var (.inl pMotive))) (.var (.inl pZ))) (.var (.inl pS))) (.var n))

def recApp (motive z s t : VExpr) : VExpr :=
  .app (.app (.app (.app (.const ``Nat.rec [.param 0]) motive) z) s) t

/-- succ rule: ctx `[n : Nat, s, z, motive]`, one self (the recursive call `Nat.rec.{u}`). -/
example : Pattern.gen env rank classify succPat succRHS = some
    { ctx := [natTy, sTy, zTy, motiveTy]
      self := [recCI.type]
      lhs := recApp (.bvar 3) (.bvar 2) (.bvar 1) (.app (.const ``Nat.succ []) (.bvar 0))
      rhs := .app (.app (.bvar 1) (.bvar 0)) (recApp (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
      rhsAbs := .app (.app (.bvar 2) (.bvar 1))
        (.app (.app (.app (.app (.bvar 0) (.bvar 4)) (.bvar 3)) (.bvar 2)) (.bvar 1))
      type := .app (.bvar 3) (.app (.const ``Nat.succ []) (.bvar 0)) } := by
  rfl

/-- zero rule: ctx `[s, z, motive]`, no self. -/
example : Pattern.gen env rank classify zeroPat zeroRHS = some
    { ctx := [sTy, zTy, motiveTy]
      self := []
      lhs := recApp (.bvar 2) (.bvar 1) (.bvar 0) (.const ``Nat.zero [])
      rhs := .bvar 1
      rhsAbs := .bvar 1
      type := .app (.bvar 2) (.const ``Nat.zero []) } := by
  rfl

end Lean4Lean.GenNat
