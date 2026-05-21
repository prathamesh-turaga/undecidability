/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Halt.Basic

@[expose] public section

/-!
# Rice's theorem — semantic-property predicates and deciders

This file lays out the definitions for Rice's theorem in two forms:

* **Predicate form**: a property `P : TMCode → Prop` is *semantic* if
  it is invariant under behavioural equivalence (`SemHalt`-equality).
  Rice's theorem says every non-trivial semantic `P` is undecidable.

* **Semantic-set form**: a *behaviour class* is a set of input lists
  on which a TM halts. A property `S : Set (Set (List Bool))` is by
  construction semantic; Rice's says every non-trivial `S` lifts to an
  undecidable property of TMCodes.

The two forms are interchangeable: the predicate form is the more
flexible primitive, and the semantic-set form is a re-packaging.

Both depend on a *decider* notion: a `D : SingleTapeTM Bool` that on
input `encodeTMCode c` writes `[true]` / `[false]` on its output tape
according to whether `P c` holds.

## What this file provides

* `SemHalt tm` — the set of inputs `w` on which `tm` halts.
* `BehaviourEquiv c d` — `c.toTM` and `d.toTM` have the same `SemHalt`.
* `IsSemantic P` — `P : TMCode → Prop` is invariant under
  `BehaviourEquiv`.
* `IsPropDecider D P` — `D` decides `P` (in the strict TM-output sense).
* `NonTrivial P` — both `P` and `¬ P` are inhabited on TMCodes.

The main theorems live in `Halt.Rice.Theorem`.
-/

namespace Halt.Rice

open Turing PCP

/-- The *halting Sem* of a TM: the set of inputs on which it halts.
For `SingleTapeTM Bool`, this is the natural "semantic behaviour"
that Rice's theorem talks about. -/
def SemHalt (tm : SingleTapeTM Bool) : Set (List Bool) :=
  { w | PCP.Halts tm w }

/-- Two `TMCode`s are *behaviourally equivalent* iff their
interpretations halt on exactly the same inputs. -/
def BehaviourEquiv (c d : Halt.TMCode) : Prop :=
  SemHalt c.toTM = SemHalt d.toTM

/-- `BehaviourEquiv` is reflexive. -/
lemma BehaviourEquiv.rfl' (c : Halt.TMCode) : BehaviourEquiv c c := rfl

/-- `BehaviourEquiv` is symmetric. -/
lemma BehaviourEquiv.symm' {c d : Halt.TMCode}
    (h : BehaviourEquiv c d) : BehaviourEquiv d c := h.symm

/-- `BehaviourEquiv` is transitive. -/
lemma BehaviourEquiv.trans' {c d e : Halt.TMCode}
    (h₁ : BehaviourEquiv c d) (h₂ : BehaviourEquiv d e) : BehaviourEquiv c e :=
  Eq.trans h₁ h₂

/-- A property of TMCodes is *semantic* iff it respects behavioural
equivalence: the truth of `P c` depends only on which inputs
`c.toTM` halts on. -/
def IsSemantic (P : Halt.TMCode → Prop) : Prop :=
  ∀ c d : Halt.TMCode, BehaviourEquiv c d → (P c ↔ P d)

/-- A property is *non-trivial* iff there is at least one TMCode
satisfying it and at least one not satisfying it. -/
def NonTrivial (P : Halt.TMCode → Prop) : Prop :=
  (∃ c, P c) ∧ (∃ c, ¬ P c)

/-- **`IsPropDecider D P`**: the TM `D` decides the TMCode property
`P` by writing `[true]` / `[false]` on its output tape. -/
def IsPropDecider (D : SingleTapeTM Bool) (P : Halt.TMCode → Prop) : Prop :=
  ∀ c : Halt.TMCode,
    (P c → SingleTapeTM.Outputs D (Halt.Encoding.encodeTMCode c) [true]) ∧
    (¬ P c → SingleTapeTM.Outputs D (Halt.Encoding.encodeTMCode c) [false])

/-! ## Semantic-set form (re-packaging)

Below we re-package the predicate form as a property of *behaviour
classes* (i.e., subsets of `List Bool` representing "which inputs the
TM halts on"). A property in this form is automatically semantic. -/

/-- A *behaviour-class property*: a set of halt-sets. -/
abbrev BehaviourClassProp := Set (Set (List Bool))

/-- Lift a behaviour-class property to a TMCode property. -/
def liftClassProp (S : BehaviourClassProp) : Halt.TMCode → Prop :=
  fun c => SemHalt c.toTM ∈ S

/-- A lifted behaviour-class property is automatically semantic. -/
lemma liftClassProp_isSemantic (S : BehaviourClassProp) :
    IsSemantic (liftClassProp S) := by
  intro c d h_equiv
  unfold liftClassProp BehaviourEquiv at *
  rw [h_equiv]

/-- A behaviour-class property is *non-trivial* in the lifted sense
iff some TMCode's halt-set is in `S` and some isn't. -/
def BehaviourNonTrivial (S : BehaviourClassProp) : Prop :=
  (∃ c : Halt.TMCode, SemHalt c.toTM ∈ S) ∧
  (∃ c : Halt.TMCode, SemHalt c.toTM ∉ S)

lemma BehaviourNonTrivial.toNonTrivial {S : BehaviourClassProp}
    (h : BehaviourNonTrivial S) : NonTrivial (liftClassProp S) := h

end Halt.Rice
