/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import PCP.Halt

@[expose] public section

/-!
# Normalised TM representation

For the halting-undecidability proof we need a *concrete*,
*finitely-describable* representation of `SingleTapeTM` so that one TM
can take another TM's description as input.

cslib's `SingleTapeTM Symbol` is too general: its `State` field can be
any inhabited `Fintype`, not necessarily `Fin n`. We can't serialise an
arbitrary `Fintype` as a finite bit string without first picking a
canonical representation.

This file fixes the canonical choice:

* **Alphabet**: `Bool`.
* **States**: `Fin (numStates + 1)` (i.e., `{0, …, numStates}`).

`TMCode` is the finitely-describable record of a TM in this normalised
form. `TMCode.toTM` interprets it as a cslib `SingleTapeTM Bool`.
`Halt.codeOf` (in `Halt.CodeOf`) gives the converse — every concrete
`SingleTapeTM Bool` is, up to state renaming, a `TMCode`.
-/

namespace Halt

open Turing PCP SingleTapeTM

/-- A normalised, finitely-describable representation of a single-tape
Turing machine over the alphabet `Bool`, with states indexed by
`Fin (numStates + 1)` (so always at least one state). -/
structure TMCode where
  /-- One less than the number of states. The actual state set is
  `Fin (numStates + 1)`, so `numStates = 0` corresponds to a single-state
  TM. -/
  numStates : ℕ
  /-- The initial state, as an index into `Fin (numStates + 1)`. -/
  q₀ : Fin (numStates + 1)
  /-- Transition table: given a current state and the symbol under the
  head, return the `Stmt` to execute (a write + a move) and the next
  state (or `none` for halt). -/
  tr : Fin (numStates + 1) → Option Bool →
       SingleTapeTM.Stmt Bool × Option (Fin (numStates + 1))

namespace TMCode

/-- Interpret a `TMCode` as an actual cslib `SingleTapeTM Bool`. The
state type of the resulting TM is `Fin (c.numStates + 1)`. -/
def toTM (c : TMCode) : SingleTapeTM Bool where
  State := Fin (c.numStates + 1)
  stateFintype := inferInstance
  q₀ := c.q₀
  tr := c.tr

@[simp] lemma toTM_State (c : TMCode) :
    c.toTM.State = Fin (c.numStates + 1) := rfl

@[simp] lemma toTM_q₀ (c : TMCode) : c.toTM.q₀ = c.q₀ := rfl

@[simp] lemma toTM_tr (c : TMCode) :
    c.toTM.tr = c.tr := rfl

/-- `Halts` for a `TMCode`: the cslib `Halts` predicate applied to its
interpretation. -/
abbrev Halts (c : TMCode) (w : List Bool) : Prop :=
  PCP.Halts c.toTM w

end TMCode

end Halt
