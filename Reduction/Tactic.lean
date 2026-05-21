/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Lean
public import Reduction.Search
public import Reduction.Transfer

public meta section

/-!
# `by reduce_diag` tactic

Component 3 of the DiagonaLean tactic. (Named `reduce_diag` rather than
`reduce` to avoid Mathlib's `reduce`, which whnfs the goal expression.)

Dispatches on the goal's form:

**Classical `Undecidable P`** (or its unfold `Decidable P → False`):
1. Extracts `P` from the goal.
2. Calls `searchPath P` to find a path anchored at some
   `@[undecidable_anchor] proof : Undecidable A`.
3. Composes the edges via `ManyOneReduction.trans` and applies
   `Undecidable.of_manyOne`.

**TM-level `TMUndecidable (Problem.predicate P)`**:
1. Extracts `P` from the goal.
2. Calls `searchPath P` to find a path anchored at some
   `@[tm_undecidable_anchor] proof : TMUndecidable (Problem.predicate A)`.
3. Composes the edges *and* the corresponding TMComputable witnesses
   (looked up by naming convention `<edgeDeclName>_TMComputable`).
4. Applies the axiomatic `TMUndecidable.of_TMReduction`.

## Usage

```lean
@[undecidable_anchor]
axiom my_undecidable : Undecidable SomeProblem
example : Undecidable OtherProblem := by reduce_diag

@[tm_undecidable_anchor]
theorem my_TM_undec : TMUndecidable SomeProblem.predicate := ...
example : TMUndecidable OtherProblem.predicate := by reduce_diag
```

## Limitations (MVP)

* Only handles **ground** edges (no polymorphic universal binders).
  Polymorphic edges like `mpcpToPcp α` raise an error.
* TM mode requires each edge to have a postulated TMComputable witness
  named `<edgeDeclName>_TMComputable`. Missing witnesses raise an error.
-/

open Lean Meta Elab Tactic

namespace DiagonaLean.ReductionGraph

/-- Build the Lean term for a single edge. For ground edges this is
just `e.declName` with fresh universe levels. For polymorphic edges
(those whose type has Pi binders for type/instance args), this is not
yet supported. -/
def mkEdgeTerm (e : Edge) : MetaM Expr := do
  let info ← getConstInfo e.declName
  if info.type.isForall then
    throwError "composeReductions: polymorphic edge `{e.declName}` is not \
      supported in MVP (its type has unresolved binders). Use \
      monomorphic reductions or instantiate the edge manually."
  mkConstWithFreshMVarLevels e.declName

/-- Compose a `Path` into a single `ManyOneReduction A T` Expr, where
`A` is the anchor's problem and `T` is the search target. For an empty
path, returns the identity reduction at the anchor's problem. -/
def composeReductions (path : Path) : MetaM Expr := do
  match path.edges with
  | [] =>
    let problem ← instantiateEndpoint path.anchor.problem
    mkAppM ``DiagonaLean.ManyOneReduction.id #[problem]
  | first :: rest => do
    let mut acc ← mkEdgeTerm first
    for e in rest do
      let next ← mkEdgeTerm e
      acc ← mkAppM ``DiagonaLean.ManyOneReduction.trans #[acc, next]
    return acc

/-- Look up the postulated TMComputable witness for a reduction by
naming convention: for declaration `foo`, the witness must be named
`foo_TMComputable` of type `TMComputable foo.f`. -/
def findTMComputable (reductionName : Name) : MetaM Expr := do
  let witnessName := reductionName.appendAfter "_TMComputable"
  unless (← getEnv).contains witnessName do
    throwError "`by reduce_diag` (TM mode): expected a postulated TMComputable \
      witness named `{witnessName}` for the reduction `{reductionName}`, but \
      no such declaration was found."
  mkConstWithFreshMVarLevels witnessName

/-- Compose a `Path` into a pair `(reduction, tmComputable)` where the
reduction is the composed `ManyOneReduction` and the second component
is a `TMComputable reduction.f` Expr. For empty paths returns the
identity reduction and `TMComputable.id`.

This is the TM-mode analog of `composeReductions`. -/
def composeTMReductions (path : Path) : MetaM (Expr × Expr) := do
  match path.edges with
  | [] =>
    let problem ← instantiateEndpoint path.anchor.problem
    let reduction ← mkAppM ``DiagonaLean.ManyOneReduction.id #[problem]
    let tmComputable ← mkConstWithFreshMVarLevels ``DiagonaLean.TMComputable.id
    return (reduction, tmComputable)
  | first :: rest => do
    let mut acc ← mkEdgeTerm first
    let mut accTM ← findTMComputable first.declName
    for e in rest do
      let next ← mkEdgeTerm e
      let nextTM ← findTMComputable e.declName
      acc ← mkAppM ``DiagonaLean.ManyOneReduction.trans #[acc, next]
      accTM ← mkAppM ``DiagonaLean.TMComputable.comp #[accTM, nextTM]
    return (acc, accTM)

/-- Goal forms recognised by `by reduce_diag`. -/
private inductive GoalForm where
  /-- Classical `Undecidable P` (or its unfold `Decidable P → False`). -/
  | undec (problem : Expr)
  /-- TM-level `TMUndecidable (Problem.predicate P)`. -/
  | tmUndec (problem : Expr)

/-- Recognise the goal's form and extract the problem. -/
private def extractGoalForm (target : Expr) : Option GoalForm := Id.run do
  let (name, args) := target.getAppFnArgs
  if name = ``DiagonaLean.Undecidable && args.size = 1 then
    return some (.undec args[0]!)
  if name = ``DiagonaLean.TMUndecidable && args.size = 1 then
    let pred := args[0]!
    let (predName, predArgs) := pred.getAppFnArgs
    if predName = ``DiagonaLean.Problem.predicate && predArgs.size = 1 then
      return some (.tmUndec predArgs[0]!)
  -- `Undecidable P` may have unfolded to `Decidable P → False`.
  if target.isForall then
    let dom := target.bindingDomain!
    let (dName, dArgs) := dom.getAppFnArgs
    if dName = ``DiagonaLean.Decidable && dArgs.size = 1 then
      return some (.undec dArgs[0]!)
  return none

/-- Search a path with the TM-anchor extension instead of the classical
one. Same algorithm as `searchPath` but anchors at `getTMAnchors`. -/
private partial def searchTMPathAux (target : Expr) (depth : Nat)
    (visited : List Expr) : MetaM (Option Path) := do
  if depth = 0 then return none
  for v in visited do
    if ← isDefEq v target then return none
  let anchors ← getTMAnchors
  for a in anchors do
    if ← problemMatches a.problem target then
      return some ⟨a, []⟩
  let edges ← getReductionGraph
  for e in edges do
    let snapshot ← saveState
    if ← problemMatches e.target target then
      if let some path ← searchTMPathAux e.source (depth - 1) (target :: visited) then
        return some { path with edges := e :: path.edges }
    restoreState snapshot
  return none

/-- Public entry: search for a TM-anchor path ending at `target`. -/
def searchTMPath (target : Expr) (depth : Nat := 10) :
    MetaM (Option Path) := do
  let result ← searchTMPathAux target depth []
  return result.map fun p => { p with edges := p.edges.reverse }

elab "reduce_diag" : tactic => Tactic.withMainContext do
  let target ← Tactic.getMainTarget
  let target ← instantiateMVars target
  match extractGoalForm target with
  | none =>
    throwError "`by reduce_diag`: expected goal of form `Undecidable P`, \
      `Decidable P → False`, or `TMUndecidable (Problem.predicate P)`, \
      got: {target}"
  | some (.undec goalProblem) =>
    match ← searchPath goalProblem with
    | none =>
      throwError "`by reduce_diag`: no `@[undecidable_anchor]` path to {goalProblem}"
    | some path =>
      let reduction ← composeReductions path
      let anchorProof ← mkConstWithFreshMVarLevels path.anchor.proofName
      let proof ← mkAppM ``DiagonaLean.Undecidable.of_manyOne #[reduction, anchorProof]
      Lean.Elab.Tactic.closeMainGoal `reduce_diag proof
  | some (.tmUndec goalProblem) =>
    match ← searchTMPath goalProblem with
    | none =>
      throwError "`by reduce_diag`: no `@[tm_undecidable_anchor]` path to {goalProblem}"
    | some path =>
      let (reduction, tmComputable) ← composeTMReductions path
      let anchorProof ← mkConstWithFreshMVarLevels path.anchor.proofName
      -- Build: TMUndecidable.of_TMReduction reduction.f tmComputable reduction.spec anchorProof
      let reductionF ← mkAppM ``DiagonaLean.ManyOneReduction.f #[reduction]
      let reductionSpec ← mkAppM ``DiagonaLean.ManyOneReduction.spec #[reduction]
      let proof ← mkAppM ``DiagonaLean.TMUndecidable.of_TMReduction
        #[reductionF, tmComputable, reductionSpec, anchorProof]
      Lean.Elab.Tactic.closeMainGoal `reduce_diag proof

end DiagonaLean.ReductionGraph
