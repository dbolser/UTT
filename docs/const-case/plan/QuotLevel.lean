import Lean4Lean.Experimental.ShapeLogRelAdequacy
namespace Lean4Lean
open VLevel

/-! Lens 4, experiment 3: level arithmetic behind the quotient exclusion.
`Quot.mk.{u} : {α : Sort u} → (r : α → α → Prop) → α → Quot r`, with `Quot r : Sort u`.
Its type's sort is `imax (succ u) (imax (imax u (imax u 1)) (imax u u))`; at `u := 0` this
evaluates to `0`, so `Params.ctor_sort` (which demands `∀ ns, u.eval ns ≠ 0` for every derivable
sort of a `.ctor`/`.etaCtor`-classified constant's type) cannot hold for `Quot.mk`. -/

def quotMkSort : VLevel :=
  .imax (.succ (.param 0))
    (.imax (.imax (.param 0) (.imax (.param 0) (.succ .zero))) (.imax (.param 0) (.param 0)))

example : quotMkSort.eval [0] = 0 := by decide
example : quotMkSort.eval [1] ≠ 0 := by decide

/-- Generic form: any Π-type whose codomain sort can be `0` has sort `0` there. -/
example (a : VLevel) (ns) : (VLevel.imax a .zero).eval ns = 0 := by
  simp [VLevel.eval, Lean.Nat.imax]

end Lean4Lean
