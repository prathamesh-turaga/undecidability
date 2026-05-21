/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Reduction.Notation
public import Reduction.Graph
public import Reduction.StackMap
public import PCP.Basic
public import PCP.MPCP
public import PCP.Reduction

@[expose] public section

/-!
# Encoded PCP: alphabet flattening to `List Bool`

The standard `mpcpToPcp : Tile α → Stack α → Stack (Ext α)` shifts the
alphabet from `α` to `Ext α`. For the DiagonaLean reduction graph to
have stable node identities, we collapse `Ext (List Bool)` back to
`List Bool` via an injective per-symbol encoding `flattenExt` and a
solution-preservation iff for the induced stack-level map.

The per-symbol bookkeeping (lifting `flattenExt` to tiles and stacks,
proving `tau` commutativity and solution preservation) is delegated to
the generic `StackMap` module — this file just supplies the injection
`flattenExt` and specialises.

## Roadmap

* `flattenExt : Ext (List Bool) → List Bool` — injective per-symbol
  encoding (`sym l ↦ false :: l`; `hash ↦ [true, false]`;
  `dollar ↦ [true, true]`).
* `flattenTile`, `flattenStack` — `StackMap.mapTile`/`mapStack` at
  `σ = flattenExt`.
* `hasSolution_flattenStack_iff` — solution preservation (specialisation
  of `StackMap.hasSolution_mapStack_iff`).
* `Problems.MPCP_LB`, `Problems.EncodedPCP` — fixed-Input `Problem`s.
* `Reductions.mpcpLB_to_encodedPCP` — the `MPCP_LB ≤ₘ EncodedPCP`
  edge, composing `mpcp_iff_pcp` (at `α = List Bool`) with the
  flatten preservation.
-/

namespace DiagonaLean

open PCP

/-! ## `flattenExt`: injective encoding of `Ext (List Bool)` -/

/-- Encode each `Ext (List Bool)` symbol as a `List Bool` with a
distinguishing prefix bit. Injective. -/
def flattenExt : PCP.Ext (List Bool) → List Bool
  | .sym l    => false :: l
  | .hash     => [true, false]
  | .dollar   => [true, true]

lemma flattenExt_injective : Function.Injective flattenExt := by
  intro a b h
  cases a <;> cases b <;> simp_all [flattenExt]

/-! ## `flattenTile`, `flattenStack`: specialise `StackMap` at `flattenExt` -/

/-- Apply `flattenExt` to each symbol in a tile. -/
abbrev flattenTile : PCP.Tile (PCP.Ext (List Bool)) → PCP.Tile (List Bool) :=
  StackMap.mapTile flattenExt

/-- Apply `flattenTile` to each tile in a stack. -/
abbrev flattenStack : PCP.Stack (PCP.Ext (List Bool)) → PCP.Stack (List Bool) :=
  StackMap.mapStack flattenExt

lemma flattenTile_injective : Function.Injective flattenTile :=
  StackMap.mapTile_injective flattenExt_injective

lemma flattenStack_injective : Function.Injective flattenStack :=
  StackMap.mapStack_injective flattenExt_injective

/-! ## Solution preservation -/

/-- **Flatten preservation**: `flattenStack P` has a solution iff `P`
does. Specialisation of `StackMap.hasSolution_mapStack_iff` at
`σ = flattenExt`. -/
theorem hasSolution_flattenStack_iff
    (P : PCP.Stack (PCP.Ext (List Bool))) :
    PCP.HasSolution (flattenStack P) ↔ PCP.HasSolution P :=
  StackMap.hasSolution_mapStack_iff flattenExt_injective P

end DiagonaLean

/-! ## `Problem` definitions and the reduction -/

namespace DiagonaLean.Problems

open PCP

/-- The MPCP problem at alphabet `List Bool`. Input is a (start-tile,
stack) pair; predicate is `MHasSolution`. Specific instantiation of
`MPCP α` from `Reduction.Instances` at `α := List Bool`. -/
def MPCP_LB : Problem where
  Input := Tile (List Bool) × Stack (List Bool)
  predicate := fun ⟨c, P⟩ => MHasSolution c P

/-- The encoded PCP problem at alphabet `List Bool`. Input is a Stack
over `List Bool`; predicate is `HasSolution`. -/
def EncodedPCP : Problem where
  Input := Stack (List Bool)
  predicate := HasSolution

end DiagonaLean.Problems

namespace DiagonaLean.Reductions

open DiagonaLean.Problems

/-- `MPCP_LB ≤ₘ EncodedPCP`: compose `mpcp_iff_pcp` at `α = List Bool`
with the `flattenStack` solution-preservation. The reducing function
is `(c, P) ↦ flattenStack (mpcpToPcp c P)`. -/
@[reduction_graph]
def mpcpLB_to_encodedPCP : ManyOneReduction MPCP_LB EncodedPCP where
  f := fun ⟨c, P⟩ => DiagonaLean.flattenStack (PCP.mpcpToPcp c P)
  spec := fun ⟨c, P⟩ => by
    show PCP.MHasSolution c P ↔
      PCP.HasSolution (DiagonaLean.flattenStack (PCP.mpcpToPcp c P))
    rw [DiagonaLean.hasSolution_flattenStack_iff]
    exact PCP.mpcp_iff_pcp c P

end DiagonaLean.Reductions
