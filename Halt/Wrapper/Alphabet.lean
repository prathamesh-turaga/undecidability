/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Mathlib.Logic.Function.Basic

@[expose] public section

/-!
# HUM normalising wrapper — the 2-bit alphabet code

The `normalisingWrapper` (postulated in `Halt.Normalise`) transforms an
arbitrary `(TMCode, input)` into a *normalised* one satisfying the HMU
side conditions `NoBlankWrites` and `NoLeftBoundary`. This directory
(`Halt/Wrapper/`) builds that wrapper for real, replacing the postulate.

## Why a 2-bit code

cslib's `TMCode.toTM` is locked to the alphabet `Bool` — its tape cells
are `Option Bool`, i.e. three values: the blank `none`, `some false`,
`some true`. The wrapper must:

* never write the blank `none` (`NoBlankWrites`) — so it needs a
  **synthetic blank** that is a genuine (non-`none`) symbol;
* know where the left edge of the tape is (`NoLeftBoundary`) — so it
  needs a **left-edge marker**.

That is four distinguished values — blank, `false`, `true`, marker —
but the alphabet only offers two non-blank symbols. The fix is the
standard one: encode each simulated cell as a **pair of cells**, giving
2² = 4 codes. This file defines that code and its encode/decode maps;
later files build the simulator on top.

## Contents

* `Code` — a pair of bits.
* `codeBlank`, `codeFalse`, `codeTrue`, `codeMark` — the four codes.
* `encSym : Option Bool → Code` — encode a simulated tape symbol.
* `decSym : Code → Option (Option Bool)` — decode (`none` ↦ the marker).
* round-trip (`decSym_encSym`), injectivity, and marker-distinctness.
-/

namespace Halt.Wrapper

/-- A *code*: how the normalising wrapper represents one cell of the
simulated machine's tape — a pair of bits, written across two adjacent
cells of the wrapper's own (`Bool`-alphabet) tape. -/
abbrev Code : Type := Bool × Bool

/-- The code for the simulated blank symbol (`Option Bool`'s `none`). -/
def codeBlank : Code := (false, false)

/-- The code for the simulated symbol `some false`. -/
def codeFalse : Code := (false, true)

/-- The code for the simulated symbol `some true`. -/
def codeTrue : Code := (true, false)

/-- The code for the left-edge marker (not a simulated symbol). -/
def codeMark : Code := (true, true)

/-- Encode a simulated tape symbol `Option Bool` as a 2-bit `Code`. -/
def encSym : Option Bool → Code
  | none         => codeBlank
  | some false   => codeFalse
  | some true    => codeTrue

/-- Decode a 2-bit `Code`: `some sym` for a simulated symbol, `none`
for the left-edge marker. -/
def decSym : Code → Option (Option Bool)
  | (false, false) => some none
  | (false, true)  => some (some false)
  | (true,  false) => some (some true)
  | (true,  true)  => none

/-- `decSym` inverts `encSym`. -/
@[simp] lemma decSym_encSym (a : Option Bool) : decSym (encSym a) = some a := by
  cases a with
  | none => rfl
  | some b => cases b <;> rfl

/-- `decSym` sends the marker code to `none`. -/
@[simp] lemma decSym_codeMark : decSym codeMark = none := rfl

/-- `encSym` is injective. -/
lemma encSym_injective : Function.Injective encSym := by
  intro a b h
  have := congrArg decSym h
  rwa [decSym_encSym, decSym_encSym, Option.some.injEq] at this

/-- No encoded symbol collides with the marker code. -/
@[simp] lemma encSym_ne_codeMark (a : Option Bool) : encSym a ≠ codeMark := by
  cases a with
  | none => decide
  | some b => cases b <;> decide

/-- The marker is decoded as "not a symbol"; every other code is a
symbol. So a code is the marker iff `decSym` returns `none`. -/
lemma decSym_eq_none_iff (x : Code) : decSym x = none ↔ x = codeMark := by
  obtain ⟨b0, b1⟩ := x
  cases b0 <;> cases b1 <;> simp [decSym, codeMark]

end Halt.Wrapper
