/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

module

public import Cslib.Computability.Machines.SingleTapeTuring.Basic

@[expose] public section

/-!
# The Halting Problem `Halt`

`Halt` is the language

  `{ ⟨M, w⟩ | M is a Turing machine that halts on input w }`.

(Note on naming: this is `HALT_TM` in Sipser's notation, not the
Universal Language `A_TM = L_u`, which asks for *acceptance*. For
cslib's `Turing.SingleTapeTM` the two coincide because there is a
single halt state with no accept/reject distinction, but the predicate
we formalise — and its standard textbook name — is **halting**, not
acceptance.)

This file defines the halting predicate `Halts` for CSLib's
`Turing.SingleTapeTM` and proves the basic equivalences used by the
reduction in `PCP.Reductions.HaltToMPCP`.

## Note on undecidability

The undecidability of `Halts` is the classical *Halting Problem*. It is
**not** proved in this file, and is not present in cslib for
`Turing.SingleTapeTM`. The reductions `Halt ≤_m MPCP ≤_m PCP` developed in
this repository stand on their own — they show

  `Halts tm w ↔ HasSolution (mpcpToPcp (startTile tm w) (haltTiles tm))`

(modulo the HUM side conditions `NoBlankWrites` and `NoLeftBoundary`).
Closing this into a proof that PCP is undecidable additionally requires
(a) a proof that `Halts` is undecidable and (b) HUM normalisation to
lift the side conditions. Both are out of scope for this repo.

Mathlib does prove the Halting Problem
(`Mathlib.Computability.Halting.halting_problem`) but for
`Nat.Partrec.Code` (partial recursive function codes), not for cslib's
`SingleTapeTM`. Transporting it across requires a simulation bridge,
which is also out of scope here.
-/

namespace PCP

open Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- `Halts tm w` holds iff `tm` started on input `w` reaches the halting
state (`state = none`) after some finite number of transitions. The
contents of the tape at halt time are existentially quantified — `Halts`
records reachability of *some* halting configuration. -/
def Halts (tm : SingleTapeTM Symbol) (w : List Symbol) : Prop :=
  ∃ tape : BiTape Symbol,
    Relation.ReflTransGen tm.TransitionRelation
      (SingleTapeTM.initCfg tm w) ⟨none, tape⟩

/-- `HaltsWithinTime tm w n` holds iff `tm` started on input `w` reaches the
halting state in at most `n` steps. -/
def HaltsWithinTime (tm : SingleTapeTM Symbol) (w : List Symbol) (n : ℕ) : Prop :=
  ∃ tape : BiTape Symbol,
    Relation.RelatesWithinSteps tm.TransitionRelation
      (SingleTapeTM.initCfg tm w) ⟨none, tape⟩ n

/-- `Halts` is logically equivalent to halting in some bounded number of
steps. -/
theorem halts_iff_exists_haltsWithinTime (tm : SingleTapeTM Symbol)
    (w : List Symbol) :
    Halts tm w ↔ ∃ n, HaltsWithinTime tm w n := by
  constructor
  · rintro ⟨tape, h⟩
    obtain ⟨n, hn⟩ := h.relatesInSteps
    exact ⟨n, tape, .of_relatesInSteps hn⟩
  · rintro ⟨n, tape, m, _, hm⟩
    exact ⟨tape, hm.reflTransGen⟩

end PCP
