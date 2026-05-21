/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Reduction.EncodedPCP
public import Reduction.Graph
public import CFG.Basic
public import CFG.PcpReduction

@[expose] public section

/-!
# CFG intersection problem as a DiagonaLean node

`hasSolution_iff_intersectionNonempty` is alphabet-polymorphic, but
the destination CFGs land at the fixed alphabet `Term (List Bool)`
when we specialise to `α = List Bool`. So unlike the alphabet-shift
in `mpcpToPcp`, no further encoding is required for a stable graph
node — `Term (List Bool)` is a fixed `Type`.

* `Problems.EncodedCFGIntersection` — Input is a pair of context-free
  grammars over `Term (List Bool)`; predicate is intersection
  non-emptiness.
* `Reductions.encodedPCP_to_encodedCFGIntersection` —
  `EncodedPCP ≤ₘ EncodedCFGIntersection` via
  `(topCFG, botCFG)` from `CFG.PcpReduction`.
-/

namespace DiagonaLean.Problems

open PCP CFG.PcpReduction Mathlib

/-- Intersection non-emptiness of two context-free grammars over the
fixed alphabet `Term (List Bool) = List Bool ⊕ Tile (List Bool)`. -/
def EncodedCFGIntersection : Problem where
  Input := ContextFreeGrammar (CFG.PcpReduction.Term (List Bool)) ×
           ContextFreeGrammar (CFG.PcpReduction.Term (List Bool))
  predicate := fun ⟨G₁, G₂⟩ =>
    ∃ w : List (CFG.PcpReduction.Term (List Bool)),
      w ∈ G₁.language ∧ w ∈ G₂.language

end DiagonaLean.Problems

namespace DiagonaLean.Reductions

open DiagonaLean.Problems

/-- `EncodedPCP ≤ₘ EncodedCFGIntersection`: a PCP instance maps to
the `(topCFG, botCFG)` pair from `CFG.PcpReduction`. The spec is
`hasSolution_iff_intersectionNonempty`. -/
@[reduction_graph]
def encodedPCP_to_encodedCFGIntersection :
    ManyOneReduction EncodedPCP EncodedCFGIntersection where
  f := fun P => (CFG.PcpReduction.topCFG P, CFG.PcpReduction.botCFG P)
  spec := fun P => CFG.PcpReduction.hasSolution_iff_intersectionNonempty P

end DiagonaLean.Reductions
