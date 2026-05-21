/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import PCP.Halt
public import Halt.Diagonal
public import Halt.TMCode
public import Halt.Encoding
public import Halt.Pair

@[expose] public section

/-!
# Halting-problem decision predicates

The decision problem `HALT` for cslib's `Turing.SingleTapeTM` asks:

  Given a TM `tm` and an input `w`, does `tm` halt on `w`?

formalised by the predicate `Halts` (see `PCP.Halt`).

This file collects the three decision-predicate variants we use to
talk about halting deciders:

| Predicate              | Decider type                                      | Status |
|------------------------|---------------------------------------------------|--------|
| `HaltDecidable`        | `SingleTapeTM Symbol → List Symbol → Bool`        | vacuously true classically |
| `IsHaltDecider`        | `SingleTapeTM Bool` (pair input `encodePair c w`) | undecidability open here  |
| `IsSelfHaltDecider`    | `SingleTapeTM Bool` (single input `encodeTMCode c`) | undecidable — proved in `Halt.Undecidable` |

`HaltDecidable` (the unrestricted Bool decider) is provable
classically and is included only as a contrast: a meaningful
undecidability claim must constrain the *decider* to a fixed
computational model. The strict forms `IsHaltDecider` /
`IsSelfHaltDecider` require the decider to be itself a TM, deciding
via its output tape.

The proved theorem is `Halt.halt_undecidable` (in `Halt.Undecidable`):
no `SingleTapeTM Bool` decides the self-halt problem
`K = { c : TMCode | c.toTM halts on encodeTMCode c }`. The pair-form
`IsHaltDecider` is included for completeness; its undecidability
follows from `IsSelfHaltDecider` via `K ≤_m HALT_TM` (a `dupTM`-style
reduction not pursued in this repo).
-/

namespace Halt

open PCP Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- **`HaltDecidable Symbol`** holds iff some Bool-valued function on
`SingleTapeTM Symbol × List Symbol` decides `Halts`. Vacuously true
classically; included for contrast with the strict forms below. -/
def HaltDecidable (Symbol : Type) [Inhabited Symbol] [Fintype Symbol] : Prop :=
  ∃ decide : SingleTapeTM Symbol → List Symbol → Bool,
    ∀ tm w, decide tm w = true ↔ Halts tm w

/-- **`IsHaltDecider D`** (pair form, "HALT_TM"): the single-tape TM
`D` over `Bool`, when run on the encoded pair `(c, w)`, halts with
output `[true]` if `c.toTM` halts on `w`, and `[false]` otherwise. -/
def IsHaltDecider (D : SingleTapeTM Bool) : Prop :=
  ∀ (c : Halt.TMCode) (w : List Bool),
    (Halts c.toTM w →
      SingleTapeTM.Outputs D
        (Halt.Pair.encodePair (Halt.Encoding.encodeTMCode c) w) [true]) ∧
    (¬ Halts c.toTM w →
      SingleTapeTM.Outputs D
        (Halt.Pair.encodePair (Halt.Encoding.encodeTMCode c) w) [false])

/-- **`IsSelfHaltDecider D`** (self-halt form, "K"): `D` decides
whether a TMCode `c` halts on its own description `encodeTMCode c`,
by emitting `[true]` / `[false]` on its output tape.

`Halt.halt_undecidable` refutes `∃ D, IsSelfHaltDecider D`. -/
def IsSelfHaltDecider (D : SingleTapeTM Bool) : Prop :=
  ∀ (c : Halt.TMCode),
    (Halts c.toTM (Halt.Encoding.encodeTMCode c) →
      SingleTapeTM.Outputs D (Halt.Encoding.encodeTMCode c) [true]) ∧
    (¬ Halts c.toTM (Halt.Encoding.encodeTMCode c) →
      SingleTapeTM.Outputs D (Halt.Encoding.encodeTMCode c) [false])

end Halt
