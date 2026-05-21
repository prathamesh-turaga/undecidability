/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

@[expose] public section

/-!
# DiagonaLean — core framework

This file defines the primitive notions of the DiagonaLean framework:

* `Problem`           — a decision problem (input type + predicate).
* `ManyOneReduction`  — a function-level many-one reduction from one
  problem to another.
* `Decidable`         — abstract decidability by *any* Bool-valued
  function on inputs. This is the function-level decidability used by
  the framework's transfer theorems.
* `Undecidable`       — `¬ Decidable`.

## Two layers of decidability

DiagonaLean talks about decidability at two levels:

* **Function-level** (this file): `Decidable P` asks for *any* Lean
  function deciding `P`. Classically every problem is decidable in
  this sense — so this notion is useful only in the *negative*:
  `Undecidable P` is the genuine claim "no function decides this".
* **TM-level** (future work, see `TODO.md`): `TMDecidable P enc`
  asks for a `SingleTapeTM Bool` deciding `P` against a chosen
  encoding `enc`. The headline theorem `Halt.halt_undecidable` is
  stated at this level.

Both layers compose through `ManyOneReduction`, but the TM-level
version additionally requires the reduction's function to be
*TM-computable*. This file provides the function-level framework;
the TM-level refinement will live in `Reduction/TMComputable.lean`
(future).

## Convention

For now, `Problem.Input` is at `Type 0`. If we need to host
problems whose inputs live at higher universes (e.g., over arbitrary
`α : Type u`), `Problem` will be made universe-polymorphic.
-/

namespace DiagonaLean

/-- A *decision problem*: an input type plus a predicate marking the
"yes" instances. Nodes of the DiagonaLean reduction graph are
`Problem`s. Universe-polymorphic in the input type to accommodate
problems like `SingleTapeTM Bool × List Bool` (whose input lives at
`Type 1`) as well as Type 0 problems. -/
structure Problem.{u} where
  /-- The type of inputs to the decision problem. -/
  Input : Type u
  /-- The predicate identifying "yes" instances. -/
  predicate : Input → Prop

/-- **`ManyOneReduction P Q`**: a function `f : P.Input → Q.Input`
together with a proof that `P` accepts an input iff `Q` accepts its
image. This is the *abstract* many-one reduction — set-theoretic, not
yet constrained to be TM-computable. The TM-computable refinement
will be added in a separate file. -/
structure ManyOneReduction.{u, v} (P : Problem.{u}) (Q : Problem.{v}) where
  /-- The reducing function. -/
  f : P.Input → Q.Input
  /-- The reduction spec: positive instances map to positive instances
  and back. -/
  spec : ∀ x, P.predicate x ↔ Q.predicate (f x)

/-- **`Decidable P`**: there is *some* Bool-valued function deciding
`P`'s predicate. Classically vacuous; useful only in the negative
form `Undecidable`. -/
def Decidable (P : Problem) : Prop :=
  ∃ d : P.Input → Bool, ∀ x, d x = true ↔ P.predicate x

/-- **`Undecidable P`**: no Bool-valued function decides `P`. -/
def Undecidable (P : Problem) : Prop :=
  ¬ Decidable P

end DiagonaLean
