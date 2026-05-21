/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Lean
public import Reduction.Basic
public import Reduction.TMDecidable

public meta section

/-!
# Reduction graph: env extension + `@[reduction_graph]` attribute

The DiagonaLean tactic `by reduce` (forthcoming) traverses a graph of
registered `ManyOneReduction P Q` edges. This file is Component 1 of
that tactic — the registration mechanism:

* `Edge` — a single registered reduction (source/target/declName).
* `reductionGraphExt` — the persistent env extension holding all edges.
* `@[reduction_graph]` — the attribute that inspects a declaration's
  type and registers it.

The attribute extracts `P` and `Q` from the declaration's type by
stripping parameter binders via `forallTelescopeReducing`, so
polymorphic reductions like
`def mpcpToPcp (α : Type) [DecidableEq α] : ManyOneReduction (MPCP α) ...`
register as open-term edges; the graph search (Component 2) handles
the unification.

## Usage

```lean
@[reduction_graph]
def mpcpLB_to_encodedPCP : ManyOneReduction MPCP_LB EncodedPCP := ...
```

Once tagged, the edge participates in `by reduce` searches.
-/

open Lean Meta

namespace DiagonaLean.ReductionGraph

/-- A registered edge in the reduction graph. -/
structure Edge where
  /-- The source `Problem` of the reduction. -/
  source : Expr
  /-- The target `Problem` of the reduction. -/
  target : Expr
  /-- The Lean name of the registered declaration. -/
  declName : Name
  deriving Inhabited

/-- The persistent env extension storing all registered reduction
edges. New edges are prepended; ordering is reverse-chronological. -/
initialize reductionGraphExt :
    SimplePersistentEnvExtension Edge (List Edge) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) {}
  }

/-- Register a new reduction edge into the global graph. -/
def addEdge (e : Edge) : CoreM Unit :=
  modifyEnv fun env => reductionGraphExt.addEntry env e

/-- Get all currently registered reduction edges. -/
def getReductionGraph : CoreM (List Edge) :=
  return reductionGraphExt.getState (← getEnv)

/-- Extract the `(P, Q)` pair from a type of the form
`∀ ..., ManyOneReduction P Q`. Strips all binders via
`forallTelescopeReducing` and re-abstracts `P` and `Q` over the stripped
parameters via `mkLambdaFVars` so the result is closed (free of the
telescope's `FVar`s). For ground reductions the abstraction is trivial;
for polymorphic reductions like `mpcpToPcp α`, the source becomes
`fun α => MPCP α` and similarly for the target. -/
def extractEndpoints (type : Expr) : MetaM (Option (Expr × Expr)) := do
  forallTelescopeReducing type fun args body => do
    let body := body.consumeMData
    match body.getAppFnArgs with
    | (``DiagonaLean.ManyOneReduction, redArgs) =>
      if redArgs.size = 2 then
        let source ← mkLambdaFVars args redArgs[0]!
        let target ← mkLambdaFVars args redArgs[1]!
        return some (source, target)
      else
        return none
    | _ => return none

/-- Process a tagged declaration: extract its source/target and add an
edge to the graph. -/
def onAttrAdd (decl : Name) : MetaM Unit := do
  let info ← getConstInfo decl
  match ← extractEndpoints info.type with
  | none =>
    throwError "@[reduction_graph]: expected declaration of type \
      `ManyOneReduction P Q` (possibly under binders), got: {info.type}"
  | some (source, target) =>
    addEdge ⟨source, target, decl⟩

initialize reductionGraphAttr : ParametricAttribute Unit ←
  registerParametricAttribute {
    name := `reduction_graph
    descr := "Registers a `ManyOneReduction P Q` declaration as an edge " ++
             "in the DiagonaLean reduction graph (for `by reduce`)."
    getParam := fun decl _stx => MetaM.run' (onAttrAdd decl)
  }

/-- Format the graph as a readable list of edges. -/
def formatGraph : CoreM Format := do
  let edges ← getReductionGraph
  return Format.joinSep
    (edges.map fun e =>
      f!"{e.declName} : {e.source} ≤ₘ {e.target}")
    Format.line

/-! ## Anchors

A `Problem` is *known-undecidable* iff there's a proof of
`Undecidable P` for it. The `@[undecidable_anchor]` attribute marks
such proofs so the search (Component 2) can terminate on them. -/

/-- A known-undecidable anchor: a `Problem` (as an `Expr`) together
with the name of a `Undecidable P` proof. -/
structure Anchor where
  /-- The anchor `Problem`. -/
  problem : Expr
  /-- The Lean name of the `Undecidable problem` proof. -/
  proofName : Name
  deriving Inhabited

/-- The persistent env extension holding all registered anchors. -/
initialize anchorExt :
    SimplePersistentEnvExtension Anchor (List Anchor) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) {}
  }

/-- Register a new undecidability anchor. -/
def addAnchor (a : Anchor) : CoreM Unit :=
  modifyEnv fun env => anchorExt.addEntry env a

/-- Get all currently registered undecidability anchors. -/
def getAnchors : CoreM (List Anchor) :=
  return anchorExt.getState (← getEnv)

/-- Extract `P` from a type of the form `∀ ..., Undecidable P`. Uses
the non-reducing `forallTelescope` to avoid unfolding `Undecidable` to
its `¬ Decidable` definition. -/
def extractUndecidable (type : Expr) : MetaM (Option Expr) := do
  forallTelescope type fun args body => do
    let body := body.consumeMData
    let (name, redArgs) := body.getAppFnArgs
    if name = ``DiagonaLean.Undecidable && redArgs.size = 1 then
      let problem ← mkLambdaFVars args redArgs[0]!
      return some problem
    else
      return none

/-- Process a `@[undecidable_anchor]` declaration. -/
def onAnchorAdd (decl : Name) : MetaM Unit := do
  let info ← getConstInfo decl
  match ← extractUndecidable info.type with
  | some problem =>
    addAnchor ⟨problem, decl⟩
  | none =>
    throwError "@[undecidable_anchor]: expected declaration of type \
      `Undecidable P` (possibly under binders), got: {info.type}"

initialize undecidabilityAnchorAttr : ParametricAttribute Unit ←
  registerParametricAttribute {
    name := `undecidable_anchor
    descr := "Marks a proof of `Undecidable P` as a search anchor for " ++
             "the DiagonaLean `by reduce_diag` tactic."
    getParam := fun decl _stx => MetaM.run' (onAnchorAdd decl)
  }

/-! ## TM-level anchors (`@[tm_undecidable_anchor]`)

Parallel to the classical anchors above, but for `TMUndecidable
(Problem.predicate P)` proofs. The stored `problem` field is `P`, so
the existing graph search (which is over `Problem`s) can be reused. -/

/-- The persistent env extension holding TM-level anchors. -/
initialize tmAnchorExt :
    SimplePersistentEnvExtension Anchor (List Anchor) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) {}
  }

/-- Register a new TM-undecidability anchor. -/
def addTMAnchor (a : Anchor) : CoreM Unit :=
  modifyEnv fun env => tmAnchorExt.addEntry env a

/-- Get all currently registered TM-undecidability anchors. -/
def getTMAnchors : CoreM (List Anchor) :=
  return tmAnchorExt.getState (← getEnv)

/-- Extract `P` from a type of the form
`∀ ..., TMUndecidable (Problem.predicate P)`. -/
def extractTMUndecidableProblem (type : Expr) : MetaM (Option Expr) := do
  forallTelescope type fun args body => do
    let body := body.consumeMData
    let (tmName, tmArgs) := body.getAppFnArgs
    if tmName = ``DiagonaLean.TMUndecidable && tmArgs.size = 1 then
      let pred := tmArgs[0]!
      let (predName, predArgs) := pred.getAppFnArgs
      if predName = ``DiagonaLean.Problem.predicate && predArgs.size = 1 then
        let problem ← mkLambdaFVars args predArgs[0]!
        return some problem
    return none

/-- Process a `@[tm_undecidable_anchor]` declaration. -/
def onTMAnchorAdd (decl : Name) : MetaM Unit := do
  let info ← getConstInfo decl
  match ← extractTMUndecidableProblem info.type with
  | some problem =>
    addTMAnchor ⟨problem, decl⟩
  | none =>
    throwError "@[tm_undecidable_anchor]: expected declaration of type \
      `TMUndecidable (Problem.predicate P)` (possibly under binders), \
      got: {info.type}"

initialize tmUndecidabilityAnchorAttr : ParametricAttribute Unit ←
  registerParametricAttribute {
    name := `tm_undecidable_anchor
    descr := "Marks a proof of `TMUndecidable (Problem.predicate P)` " ++
             "as a search anchor for `by reduce_diag` on TM-undecidability " ++
             "goals."
    getParam := fun decl _stx => MetaM.run' (onTMAnchorAdd decl)
  }

end DiagonaLean.ReductionGraph
