/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Halt.Wrapper.Alphabet
public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# HUM normalising wrapper — the wrapped-input encoding

Step 2 of the wrapper construction (see `Halt/Wrapper/Alphabet.lean`).

The simulator represents each cell of the simulated machine's tape as a
two-cell `Code` (`Halt.Wrapper.Alphabet`). So the simulated machine's
input `w : List Bool` — whose `mk₁`-tape cells are `some w[0]`,
`some w[1]`, … — is laid out on the wrapper's tape as the bit-list

  `encodeInput w  =  w.flatMap (fun b => [b, !b])`

i.e. `some false ↦ [false, true]` (`codeFalse`) and
`some true ↦ [true, false]` (`codeTrue`), two wrapper-cells per
simulated cell.

A wrapper-cell holds `Option Bool`; its *logical bit* is
`Option.getD · false`, so an unwritten blank cell reads as `false` —
hence an unwritten pair `(none, none)` reads as the code
`(false, false) = codeBlank`, exactly the simulated blank. This is what
lets the simulator treat untouched tape as simulated-blank while itself
only ever writing `some _` (the `NoBlankWrites` discipline).

## Contents

* `symBits : Bool → List Bool` — the two-cell fragment for one
  simulated input cell.
* `encodeInput : List Bool → List Bool` — the wrapped input.
* `encodeInput_nil`, `encodeInput_cons`, `encodeInput_length`,
  `encodeInput_append`.
-/

namespace Halt.Wrapper

/-- The two bits of `encSym (some b)`, as a list — the wrapper-tape
fragment for one simulated input cell. `false ↦ [false, true]`
(`codeFalse`), `true ↦ [true, false]` (`codeTrue`). -/
def symBits (b : Bool) : List Bool := [b, !b]

@[simp] lemma symBits_eq_code (b : Bool) :
    symBits b = [(encSym (some b)).1, (encSym (some b)).2] := by
  cases b <;> rfl

/-- The wrapped input: each simulated cell `some b` becomes the two
wrapper-cells `symBits b` (`= encSym (some b)`). -/
def encodeInput (w : List Bool) : List Bool :=
  w.flatMap symBits

@[simp] lemma encodeInput_nil : encodeInput [] = [] := rfl

@[simp] lemma encodeInput_cons (b : Bool) (w : List Bool) :
    encodeInput (b :: w) = b :: ((!b) :: encodeInput w) := rfl

lemma encodeInput_append (v w : List Bool) :
    encodeInput (v ++ w) = encodeInput v ++ encodeInput w := by
  simp [encodeInput, List.flatMap_append]

@[simp] lemma encodeInput_length (w : List Bool) :
    (encodeInput w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [encodeInput_cons]
    simp only [List.length_cons, ih]
    omega

end Halt.Wrapper
