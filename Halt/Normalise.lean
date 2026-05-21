/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Halt.TMCode
public import PCP.Reductions.HaltToMPCP

@[expose] public section

/-!
# HUM normalisation: postulated wrapper

The Hopcroft-Ullman-Motwani PCP reduction (`PCP.HaltToMPCP.halt_le_mpcp`)
is gated by two TM-level side conditions:

* `NoBlankWrites tm` — `tm.tr` never writes the blank symbol; needed
  because cslib's `BiTape` auto-trims trailing blanks (which can break
  the simulation invariant if a blank is written into a previously-empty
  boundary cell).
* `NoLeftBoundary tm w` — no reachable configuration from
  `initCfg tm w` ever invokes a left-move while the left tape is empty;
  needed because our tile set lacks a `leftMoveBoundaryTile`.

For an end-to-end reduction `EncodedHalt ≤ₘ EncodedHaltMPCP`, we need a
construction that transforms an *arbitrary* `(TMCode, w)` pair into a
*normalised* one satisfying both conditions, preserving halting. This is
the standard HUM-normalisation construction.

## What this file provides

* `NormalisingWrapper` — a structure bundling a wrapper function
  `(TMCode, w) ↦ (TMCode', w')` together with proofs of NBW, NLB, and
  halting equivalence.
* `normalisingWrapper` — an `axiom` asserting that such a wrapper
  exists.

The construction itself is the standard sentinel-shift / blank-replacement
trick: encode each input bit as a pair of cells, reserving designated
bit-pairs for a left-edge marker and a "synthetic blank" symbol that
the wrapper handles like a real blank (without invoking
`BiTape`-trimming). The wrapper TM has a few extra states for the
prefix-write phase. The formal Lean construction is on the long-term
TODO (~1000-1500 LoC); the postulate captures the standard textbook
content.

This is the **most substantive** postulate in the DiagonaLean project.
Once discharged, every step in the chain
`EncodedSelfHalt → EncodedHalt → EncodedHaltMPCP → … → EncodedCFGI_LB`
is grounded in `halt_undecidable` (no problem-specific postulates).
-/

namespace DiagonaLean

open Halt PCP PCP.HaltToMPCP Turing

/-- A *normalising wrapper*: a function from `(TMCode, w)` to a
normalised `(TMCode', w')` together with the two side-condition proofs
and the halting bisimulation. -/
structure NormalisingWrapper where
  /-- The wrapper function. -/
  wrap : Halt.TMCode → List Bool → Halt.TMCode × List Bool
  /-- The wrapped TM has no blank writes. -/
  no_blank_writes : ∀ c w, NoBlankWrites (wrap c w).1.toTM
  /-- The wrapped TM has no left-boundary issues on its wrapped input. -/
  no_left_boundary : ∀ c w, NoLeftBoundary (wrap c w).1.toTM (wrap c w).2
  /-- The wrapping preserves halting behaviour. -/
  halts_iff : ∀ c w, PCP.Halts (wrap c w).1.toTM (wrap c w).2 ↔
                     PCP.Halts c.toTM w

/-- **The HUM-normalisation axiom**: a normalising wrapper exists.

The standard textbook proof builds `wrap c w` as follows:

* Encode each bit of `w` as a *pair* of cells (a 2-bit code) so the
  alphabet has room for a reserved "left-edge marker" pair and a
  reserved "synthetic blank" pair.
* The wrapper TM `wrap c w |>.1.toTM` has a few extra states forming a
  prefix-write phase that first lays down the marker pair at the left
  edge, then transcribes `w` into the 2-bit encoding starting from
  cell 2, and finally jumps to a state that simulates `c.toTM` over the
  encoded representation.
* During simulation, blank writes are replaced by writes of the
  synthetic-blank code, and left moves at the marker stay in place
  (or rebound). Both side conditions hold by construction.
* Halting is preserved because the simulation is a faithful bijection
  modulo the 2-bit encoding.

This is ~1000-1500 LoC to formalise directly; the postulate captures
the construction's correctness. -/
axiom normalisingWrapper : NormalisingWrapper

end DiagonaLean
