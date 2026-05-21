/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Reduction.Notation
public import Reduction.Graph
public import PCP.Basic
public import PCP.MPCP
public import PCP.Reduction
public import PCP.Halt
public import Halt.TMCode
public import Halt.CodeOf

@[expose] public section

/-!
# Instances — wrapping existing iffs as DiagonaLean reductions

This file populates the DiagonaLean reduction graph with concrete
nodes and edges drawn from the existing proof corpus. Each `Problem`
definition gives a node; each `ManyOneReduction` instance gives an
edge.

## Currently wrapped

* `Problems.MPCP α`              — MPCP over alphabet `α`.
* `Problems.PCP α`               — PCP over alphabet `α`.
* `Reductions.mpcpToPcp α`       — `MPCP α ≤ₘ PCP (Ext α)` from
                                   `mpcp_iff_pcp`.
* `Problems.HaltTM`              — Halting problem for
                                   `SingleTapeTM Bool`, packaged as a
                                   `Problem`.
* `Problems.HaltTMCode`          — Halting problem for `TMCode`.
* `Reductions.haltTM_to_haltTMCode` — `HaltTM ≤ₘ HaltTMCode` from
                                       `halts_codeOf_iff`.
* `Reductions.haltTMCode_to_haltTM` — the reverse.

## Pending

* `Halt ≤ₘ MPCP`: the destination alphabet
  (`PCP.HaltToMPCP.Alpha tm.State Symbol`) depends on the input tm,
  which doesn't fit a single fixed `Problem` node. Needs a uniform
  encoding (e.g., into `List Bool`) before it can be expressed as a
  single edge — see TODO.md.
* `PCP ≤ₘ CFG-Intersection-Nonempty`: same alphabet-dependency story.
-/

namespace DiagonaLean.Problems

open PCP Turing

/-- The MPCP problem over alphabet `α`. -/
def MPCP (α : Type) : Problem where
  Input := Tile α × Stack α
  predicate := fun ⟨c, P⟩ => MHasSolution c P

/-- The PCP problem over alphabet `α`. -/
def PCP (α : Type) : Problem where
  Input := Stack α
  predicate := HasSolution

/-- The halting problem for cslib's `SingleTapeTM Bool`. -/
def HaltTM : Problem where
  Input := SingleTapeTM Bool × List Bool
  predicate := fun ⟨tm, w⟩ => Halts tm w

/-- The halting problem for `Halt.TMCode`. -/
def HaltTMCode : Problem where
  Input := Halt.TMCode × List Bool
  predicate := fun ⟨c, w⟩ => Halts c.toTM w

end DiagonaLean.Problems

namespace DiagonaLean.Reductions

open DiagonaLean.Problems

/-- `MPCP α ≤ₘ PCP (Ext α)`. The reducing function is `mpcpToPcp` and
the spec is `mpcp_iff_pcp`. -/
@[reduction_graph]
def mpcpToPcp (α : Type) [DecidableEq α] :
    ManyOneReduction (MPCP α) (PCP (PCP.Ext α)) where
  f := fun ⟨c, P⟩ => PCP.mpcpToPcp c P
  spec := fun ⟨c, P⟩ => PCP.mpcp_iff_pcp c P

/-- `HaltTM ≤ₘ HaltTMCode`. The reducer sends `(tm, w)` to
`(codeOf tm, w)`; the spec is `halts_codeOf_iff` (backward direction
of the iff). -/
@[reduction_graph]
noncomputable def haltTM_to_haltTMCode :
    ManyOneReduction HaltTM HaltTMCode where
  f := fun ⟨tm, w⟩ => (Halt.codeOf tm, w)
  spec := fun ⟨tm, w⟩ => (Halt.halts_codeOf_iff tm w).symm

end DiagonaLean.Reductions
