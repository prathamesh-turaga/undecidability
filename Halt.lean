/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

module

public import Halt.Diagonal
public import Halt.Basic
public import Halt.TMCode
public import Halt.Encoding
public import Halt.Pair
public import Halt.Helpers
public import Halt.CodeOf
public import Halt.Undecidable
public import Halt.Wrapper.Alphabet
public import Halt.Wrapper.Tape
public import Halt.Rice.Basic
public import Halt.Rice.TrivialTMs
public import Halt.Rice.Extender
public import Halt.Rice.Bisim
public import Halt.Rice.Theorem

@[expose] public section

/-!
# Halt — library root

This module re-exports the public Halt-undecidability API:

* `Halt.Diagonal`     — Cantor's theorem and the abstract
  self-referential contradiction at the heart of the Halting Problem.
* `Halt.Basic`        — the three decider predicates:
  `HaltDecidable` (vacuous), `IsHaltDecider` (pair form),
  `IsSelfHaltDecider` (the form `halt_undecidable` refutes).
* `Halt.TMCode`       — normalised TM representation: `Bool` alphabet,
  `Fin (n + 1)` states, with `TMCode.toTM : TMCode → SingleTapeTM Bool`.
* `Halt.Encoding`     — Gödel numbering: self-delimiting bit encoding
  of `TMCode` as `List Bool`.
* `Halt.Pair`         — pair encoding `encodePair` (used by
  `IsHaltDecider`).
* `Halt.Helpers`      — worked example: `invertTM`, a 2-state TM that
  halts on `[false]` and loops on `[true]`.
* `Halt.CodeOf`       — generic state-renaming
  `codeOf : SingleTapeTM Bool → TMCode` with the bisimulation theorem
  `halts_codeOf_iff`.
* `Halt.Undecidable`  — the final theorem `halt_undecidable`: no
  `SingleTapeTM Bool` decides the self-halt problem `K`.

## In progress: Rice's theorem

* `Halt.Rice.Basic`     — definitions of `SemHalt`, `BehaviourEquiv`,
  `IsSemantic`, `IsPropDecider`, and the semantic-set form.
* `Halt.Rice.TrivialTMs` — `tm_alwaysHalt` (halts on every input) and
  `tm_loop` (loops on every input), with `SemHalt` characterisations.
* `Halt.Rice.Extender`  — `riceConstTM : TMCode → SingleTapeTM Bool`,
  the constant-Sem reduction TM: ignores its input, writes
  `encodeTMCode c` to the tape, and simulates `c.toTM` on it. Halts
  iff `c.toTM` halts on `encodeTMCode c`, regardless of input.

The behaviour theorem `SemHalt (riceConstTM c) = univ ↔ Halts c.toTM
(encodeTMCode c)` and the main Rice theorem (`Halt.Rice.Theorem`,
TBD) are the next milestones; see `Halt/ROADMAP.md`.
-/
