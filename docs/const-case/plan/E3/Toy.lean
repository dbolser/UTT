import Lean4Lean.Experimental.E3.Measure7
/-! Toy check (not part of E3's deliverables): `Pattern.gen` computes the expected `PatGen`
for Nat.rec's succ rule, by `rfl`. -/
open Lean4Lean

def nat : VExpr := .const `Nat []
def toyEnv : VEnv where
  constants c :=
    if c = `Nat then some ⟨0, .sort (.succ .zero)⟩
    else if c = `Nat.zero then some ⟨0, nat⟩
    else if c = `Nat.succ then some ⟨0, .forallE nat nat⟩
    else if c = `Nat.rec then some ⟨1,
      -- (motive : Nat → Sort u) → motive zero → ((n : Nat) → motive n → motive (succ n)) → (t : Nat) → motive t
      .forallE (.forallE nat (.sort (.param 0)))
        (.forallE (.app (.bvar 0) (.const `Nat.zero []))
          (.forallE (.forallE nat (.forallE (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 3) (.app (.const `Nat.succ []) (.bvar 1)))))
            (.forallE nat (.app (.bvar 3) (.bvar 0)))))⟩
    else none
  defeqs _ := False

def toyRank : Name → Nat := fun c =>
  if c = `Nat then 0 else if c = `Nat.zero then 1 else if c = `Nat.succ then 2 else 3
def toyCl : Name → Option Classification := fun c =>
  if c = `Nat.zero then some (.ctor 0) else if c = `Nat.succ then some (.ctor 1)
  else if c = `Nat then some (.indTy 0) else if c = `Nat.rec then some (.symb 4) else none

abbrev succPat : Pattern := .iota `Nat.rec 3 `Nat.succ 1
-- paths: inl none = s, inl (some none) = z, inl (some (some none)) = motive, inr none = n
def recLeaf : VExpr := .const `Nat.rec [.param 0]
theorem recLeaf_closed : recLeaf.Closed := trivial
def succRHS : succPat.RHS :=
  .app (.app (.var (.inl none)) (.var (.inr none)))
    (.app (.app (.app (.app (.fixed recLeaf recLeaf_closed) (.var (.inl (some (some none)))))
      (.var (.inl (some none)))) (.var (.inl none))) (.var (.inr none)))

example : (Pattern.gen toyEnv toyRank toyCl succPat succRHS).map (·.rhsAbs) =
    some (.app (.app (.bvar 2) (.bvar 1))
      (.app (.app (.app (.app (.bvar 0) (.bvar 4)) (.bvar 3)) (.bvar 2)) (.bvar 1))) := rfl
example : (Pattern.gen toyEnv toyRank toyCl succPat succRHS).map (·.rhs) =
    some (.app (.app (.bvar 1) (.bvar 0))
      (.app (.app (.app (.app recLeaf (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))) := rfl
example : (Pattern.gen toyEnv toyRank toyCl succPat succRHS).map (·.lhs) =
    some (.app (.app (.app (.app (.const `Nat.rec [.param 0]) (.bvar 3)) (.bvar 2)) (.bvar 1))
      (.app (.const `Nat.succ []) (.bvar 0))) := rfl
example : (Pattern.gen toyEnv toyRank toyCl succPat succRHS).map (·.ctx.length) = some 4 := by decide
example : (Pattern.gen toyEnv toyRank toyCl succPat succRHS).map (·.self.length) = some 1 := by decide
example : (Pattern.gen toyEnv toyRank toyCl succPat succRHS).map (·.type) =
    some (.app (.bvar 3) (.app (.const `Nat.succ []) (.bvar 0))) := rfl
