/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Lean
public import Reduction.Graph

public meta section

/-!
# Reduction graph search

Component 2 of the `by reduce` tactic. Given a target `Problem` `T`,
`searchPath T` does a depth-bounded backward DFS through the registered
graph, looking for a chain of edges that terminates at a registered
undecidability anchor:

```
anchor (proof of `Undecidable A`)  → A
  via edge e₁                       → P₁
  via edge e₂                       → P₂
  ...
  via edge eₙ                       → T   (the target)
```

The returned list `[e₁, e₂, …, eₙ]` is the path in source-to-target
order, with `e₁.source = A` (the anchor problem) and `eₙ.target = T`.

Matching between expected source/target and an edge's stored endpoints
is up to `isDefEq` (so β/δ-equivalent terms unify). For polymorphic
edges (stored as `fun α => …` lambdas), the search applies the lambda
to fresh metavariables before matching — this lets `MPCP α` unify with
`MPCP Bool`.

The composition into a single `ManyOneReduction A T` term and the
`Undecidable A → Undecidable T` transfer is Component 3 (term emission).
-/

open Lean Meta

namespace DiagonaLean.ReductionGraph

/-- A path through the graph: a list of edges in source-to-target
order, plus the anchor that grounds the chain. -/
structure Path where
  /-- The anchor (a known-undecidable problem and its proof). -/
  anchor : Anchor
  /-- The chain of edges. `head.source` matches the anchor's problem;
  `last.target` matches the search target. May be empty when the
  target itself is an anchor. -/
  edges : List Edge

/-- Apply a stored endpoint (possibly a `fun α => …` lambda from
`mkLambdaFVars`) to fresh metavariables before unification. For ground
endpoints this is a no-op; for polymorphic ones it β-reduces by
introducing metas for each binder. -/
def instantiateEndpoint (e : Expr) : MetaM Expr := do
  forallTelescopeReducing (← inferType e) fun args _ => do
    if args.isEmpty then
      return e
    else
      let metas ← args.mapM fun arg => do
        let typ ← inferType arg
        mkFreshExprMVar typ
      return mkAppN e metas

/-- Check whether two `Problem` expressions unify up to definitional
equality, after instantiating any polymorphic binders. -/
def problemMatches (stored expected : Expr) : MetaM Bool := do
  let stored' ← instantiateEndpoint stored
  let result ← isDefEq stored' expected
  trace[DiagonaLean.search] "problemMatches: stored={stored'} expected={expected} → {result}"
  return result

/-- Trace class for search debugging. -/
initialize Lean.registerTraceClass `DiagonaLean.search

/-- Internal recursive search; returns edges in target-to-source order
(easy to build via cons). The public `searchPath` reverses this. -/
private partial def searchPathAux (target : Expr) (depth : Nat)
    (visited : List Expr) : MetaM (Option Path) := do
  if depth = 0 then return none
  for v in visited do
    if ← isDefEq v target then return none
  let anchors ← getAnchors
  for a in anchors do
    if ← problemMatches a.problem target then
      return some ⟨a, []⟩
  let edges ← getReductionGraph
  for e in edges do
    let snapshot ← saveState
    if ← problemMatches e.target target then
      if let some path ← searchPathAux e.source (depth - 1) (target :: visited) then
        return some { path with edges := e :: path.edges }
    restoreState snapshot
  return none

/-- Depth-bounded backward DFS for a path ending at `target`. Visits
sources of incoming edges; terminates when the current node matches a
registered `Anchor`. Returns the path with edges in **source-to-target**
order (the anchor's problem is at `edges.head!.source`; the search
target is at `edges.getLast!.target`). -/
def searchPath (target : Expr) (depth : Nat := 10) :
    MetaM (Option Path) := do
  let result ← searchPathAux target depth []
  return result.map fun p => { p with edges := p.edges.reverse }

/-- Pretty-print a path. -/
def formatPath (p : Path) : Format :=
  let header := f!"anchor: {p.anchor.proofName} (Undecidable {p.anchor.problem})"
  let body := p.edges.map fun e => f!"  → {e.declName} : {e.source} ≤ₘ {e.target}"
  Format.joinSep (header :: body) Format.line

end DiagonaLean.ReductionGraph
