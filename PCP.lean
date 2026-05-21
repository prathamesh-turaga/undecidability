/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

module

public import PCP.Basic
public import PCP.MPCP
public import PCP.Reduction
public import PCP.Halt
public import PCP.Reductions.HaltToMPCP
public import PCP.Reductions.HaltToPCP

@[expose] public section

/-!
# PCP — library root

This module re-exports the public PCP API:

* `PCP.Basic`             — core types and the `HasSolution` predicate.
* `PCP.MPCP`              — the Modified PCP variant `MHasSolution`.
* `PCP.Reduction`         — the proof that `MPCP ≤_m PCP`.
* `PCP.Halt`                — the halting problem `Halts` (built on
  `Turing.SingleTapeTM` from cslib).
* `PCP.Reductions.HaltToMPCP` — infrastructure for the `Halt ≤_m MPCP`
  reduction (alphabet, configuration encoding).
* `PCP.Reductions.HaltToPCP` — `halts_iff_pcp`, the composition of
  `Halt ≤_m MPCP` and `MPCP ≤_m PCP` into a direct `Halts ↔ HasSolution`
  equivalence.
-/
