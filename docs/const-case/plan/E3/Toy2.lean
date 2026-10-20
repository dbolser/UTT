import Lean4Lean.Experimental.E3.Measure7
open Lean4Lean

-- Tree : Sort 1; leaf : Tree; node : Tree → Tree → Tree;
-- Tree.rec.{u} : (motive : Tree → Sort u) → motive leaf →
--   ((l r : Tree) → motive l → motive r → motive (node l r)) → (t : Tree) → motive t
def tr : VExpr := .const `Tree []
def recTy : VExpr :=
  .forallE (.forallE tr (.sort (.param 0)))
    (.forallE (.app (.bvar 0) (.const `leaf []))
      (.forallE (.forallE tr (.forallE tr (.forallE (.app (.bvar 3) (.bvar 1))
          (.forallE (.app (.bvar 4) (.bvar 1)) (.app (.bvar 5) (.app (.app (.const `node []) (.bvar 3)) (.bvar 2)))))))
        (.forallE tr (.app (.bvar 3) (.bvar 0)))))
def env : VEnv where
  constants c :=
    if c = `Tree then some ⟨0, .sort (.succ .zero)⟩
    else if c = `leaf then some ⟨0, tr⟩
    else if c = `node then some ⟨0, .forallE tr (.forallE tr tr)⟩
    else if c = `Tree.rec then some ⟨1, recTy⟩
    else if c = `myDef then some ⟨0, tr⟩
    else none
  defeqs _ := False
def rank : Name → Nat := fun c =>
  if c = `Tree then 0 else if c = `leaf then 1 else if c = `node then 2 else if c = `Tree.rec then 3 else 4
def cl : Name → Option Classification := fun c =>
  if c = `leaf then some (.ctor 0) else if c = `node then some (.ctor 2)
  else if c = `Tree then some (.indTy 0) else if c = `Tree.rec then some (.symb 4)
  else if c = `myDef then some (.symb 0) else none

abbrev nodePat : Pattern := .iota `Tree.rec 3 `node 2
abbrev leafPat : Pattern := .iota `Tree.rec 3 `leaf 0
def recLeaf : VExpr := .const `Tree.rec [.param 0]
theorem recLeaf_closed : recLeaf.Closed := trivial
-- paths of nodePat: inl none = hn, inl (some none) = hl, inl (some (some none)) = motive,
-- inr none = r, inr (some none) = l
def recOf (x : nodePat.Path) : nodePat.RHS :=
  .app (.app (.app (.app (.fixed recLeaf recLeaf_closed) (.var (.inl (some (some none)))))
    (.var (.inl (some none)))) (.var (.inl none))) (.var x)
def nodeRHS : nodePat.RHS :=
  .app (.app (.app (.app (.var (.inl none)) (.var (.inr (some none)))) (.var (.inr none)))
    (recOf (.inr (some none)))) (recOf (.inr none))

-- node rule: two same-rank occurrences of Tree.rec, each its own self variable
example : (Pattern.gen env rank cl nodePat nodeRHS).map (·.self.length) = some 2 := by decide
example : (Pattern.gen env rank cl nodePat nodeRHS).map (·.ctx.length) = some 5 := by decide
example : (Pattern.gen env rank cl nodePat nodeRHS).map (·.lhs) =
    some (.app (.app (.app (.app (.const `Tree.rec [.param 0]) (.bvar 4)) (.bvar 3)) (.bvar 2))
      (.app (.app (.const `node []) (.bvar 1)) (.bvar 0))) := rfl
example : (Pattern.gen env rank cl nodePat nodeRHS).map (·.rhs) =
    some (.app (.app (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
      (.app (.app (.app (.app recLeaf (.bvar 4)) (.bvar 3)) (.bvar 2)) (.bvar 1)))
      (.app (.app (.app (.app recLeaf (.bvar 4)) (.bvar 3)) (.bvar 2)) (.bvar 0))) := rfl
example : (Pattern.gen env rank cl nodePat nodeRHS).map (·.rhsAbs) =
    some (.app (.app (.app (.app (.bvar 4) (.bvar 3)) (.bvar 2))
      (.app (.app (.app (.app (.bvar 0) (.bvar 6)) (.bvar 5)) (.bvar 4)) (.bvar 3)))
      (.app (.app (.app (.app (.bvar 1) (.bvar 6)) (.bvar 5)) (.bvar 4)) (.bvar 2))) := rfl
example : (Pattern.gen env rank cl nodePat nodeRHS).map (·.type) =
    some (.app (.bvar 4) (.app (.app (.const `node []) (.bvar 1)) (.bvar 0))) := rfl
-- ctx (innermost first): r : Tree, l : Tree, hn, hl, motive
example : (Pattern.gen env rank cl nodePat nodeRHS).map (fun g => g.ctx.take 2) = some [tr, tr] := rfl

-- leaf rule (n = 0): rec motive hl hn leaf = hl
def leafRHS : leafPat.RHS := .var (.inl (some none))
example : (Pattern.gen env rank cl leafPat leafRHS).map (·.lhs) =
    some (.app (.app (.app (.app (.const `Tree.rec [.param 0]) (.bvar 2)) (.bvar 1)) (.bvar 0))
      (.const `leaf [])) := rfl
example : (Pattern.gen env rank cl leafPat leafRHS).map (·.rhs) = some (.bvar 1) := rfl
example : (Pattern.gen env rank cl leafPat leafRHS).map (·.type) = some (.app (.bvar 2) (.const `leaf [])) := rfl
example : (Pattern.gen env rank cl leafPat leafRHS).map (·.self.length) = some 0 := by decide

-- delta pattern: myDef := node leaf leaf
def body : VExpr := .app (.app (.const `node []) (.const `leaf [])) (.const `leaf [])
theorem body_closed : body.Closed := ⟨⟨trivial, trivial⟩, trivial⟩
def deltaRHS : (Pattern.const `myDef).RHS := .fixed body body_closed
example : (Pattern.gen env rank cl (.const `myDef) deltaRHS).map (fun g => (g.ctx, g.lhs, g.rhs, g.type, g.self.length)) =
    some ([], .const `myDef [], body, tr, 0) := rfl
