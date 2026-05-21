/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Reduction.Instances
public import Reduction.Graph
public import Halt.Pair

@[expose] public section

/-!
# Encoded variants of DiagonaLean problems

For the eventual `@[reduction_graph]` tactic to work without
metavariable unification, every node in the graph should have a
*fixed* `Input` type. This file gives the first such encoded variant:

* `EncodedHalt : Problem` — Input `List Bool`, predicate
  "decoding bits as `(c, w)` succeeds and `c.toTM` halts on `w`".

We also provide the bidirectional reductions

* `HaltTMCode ≤ₘ EncodedHalt` — encode the pair.
* `EncodedHalt ≤ₘ HaltTMCode` — decode the bits (mapping malformed
  inputs to a fixed always-looping `TMCode` so the predicate is
  preserved).

Together these form `HaltTMCode ≡ₘ EncodedHalt`. The encoded variant
has a `List Bool` input and is a stable graph node.
-/

namespace DiagonaLean.Problems

open PCP Turing Halt

/-- The encoded halting problem: input is a bit string, positive iff
the bit string is `encodePair (encodeTMCode c) w` for some `(c, w)`
with `c.toTM` halting on `w`. -/
def EncodedHalt : Problem where
  Input := List Bool
  predicate := fun bits =>
    match Halt.Pair.decodePair bits with
    | none => False
    | some (codeBits, w) =>
      match Halt.Encoding.decodeTMCode codeBits with
      | none => False
      | some c => Halts c.toTM w

end DiagonaLean.Problems

/-! ## A canonical "loops forever" TMCode -/

namespace Halt

open Turing PCP

/-- The single state of `loopingTMCode`. -/
def loopingState : Fin 1 := ⟨0, by decide⟩

/-- A 1-state `TMCode` whose only state transitions to itself with no
write/move. The interpretation `loopingTMCode.toTM` does not halt on
any input. -/
def loopingTMCode : Halt.TMCode where
  numStates := 0
  q₀ := loopingState
  tr _ _ := (⟨none, none⟩, some loopingState)

lemma loopingTMCode_step (t : BiTape Bool) :
    loopingTMCode.toTM.step ⟨some loopingState, t⟩ =
      some ⟨some loopingState, t.write none⟩ := rfl

/-- A configuration of `loopingTMCode.toTM` with state `some loopingState`
keeps that state after one step. (In fact the destination is always
`some loopingState` regardless of the source state — `loopingTMCode.tr`
ignores its input state.) -/
private lemma loopingTMCode_step_persist
    {cfg cfg' : loopingTMCode.toTM.Cfg}
    (h_state : cfg.state = some loopingState)
    (h_step : loopingTMCode.toTM.TransitionRelation cfg cfg') :
    cfg'.state = some loopingState := by
  obtain ⟨st, t⟩ := cfg
  cases st with
  | none => simp at h_state
  | some u =>
    rw [SingleTapeTM.TransitionRelation] at h_step
    have h_step_eq : loopingTMCode.toTM.step ⟨some u, t⟩ =
        some ⟨some loopingState, t.write none⟩ := rfl
    rw [h_step_eq] at h_step
    obtain ⟨st', t'⟩ := cfg'
    injection h_step with h_eq
    obtain ⟨h_st, _⟩ := SingleTapeTM.Cfg.mk.injEq .. |>.mp h_eq
    exact h_st.symm

private lemma loopingTMCode_state_persistent
    {cfg cfg' : loopingTMCode.toTM.Cfg}
    (h_state : cfg.state = some loopingState)
    (h_reach : Relation.ReflTransGen loopingTMCode.toTM.TransitionRelation
                cfg cfg') :
    cfg'.state = some loopingState := by
  induction h_reach with
  | refl => exact h_state
  | tail _ h_step ih => exact loopingTMCode_step_persist ih h_step

/-- `loopingTMCode.toTM` does not halt on any input. -/
theorem not_halts_loopingTMCode (w : List Bool) :
    ¬ PCP.Halts loopingTMCode.toTM w := by
  rintro ⟨tape, h_chain⟩
  have h_init :
      (SingleTapeTM.initCfg loopingTMCode.toTM w).state = some loopingState := rfl
  have h_persist :
      (⟨none, tape⟩ : loopingTMCode.toTM.Cfg).state = some loopingState :=
    loopingTMCode_state_persistent h_init h_chain
  simp at h_persist

end Halt

/-! ## Reductions between `HaltTMCode` and `EncodedHalt` -/

namespace DiagonaLean.Reductions

open DiagonaLean.Problems

/-- `HaltTMCode ≤ₘ EncodedHalt`: encode the pair. The spec is direct
from the round-trip lemmas `decodePair_encodePair` and
`decodeTMCode_encodeTMCode`. -/
@[reduction_graph]
def haltTMCode_to_encodedHalt : ManyOneReduction HaltTMCode EncodedHalt where
  f := fun ⟨c, w⟩ => Halt.Pair.encodePair (Halt.Encoding.encodeTMCode c) w
  spec := fun ⟨c, w⟩ => by
    show PCP.Halts c.toTM w ↔
      (match Halt.Pair.decodePair
          (Halt.Pair.encodePair (Halt.Encoding.encodeTMCode c) w) with
        | none => False
        | some (codeBits, w') =>
          match Halt.Encoding.decodeTMCode codeBits with
          | none => False
          | some c' => PCP.Halts c'.toTM w')
    rw [Halt.Pair.decodePair_encodePair]
    dsimp only
    rw [Halt.Encoding.decodeTMCode_encodeTMCode]

/-- `EncodedHalt ≤ₘ HaltTMCode`: decode the bits. Malformed inputs
map to `(loopingTMCode, [])`, which doesn't halt — preserving the
`predicate` since malformed inputs are `False` on the encoded side. -/
@[reduction_graph]
noncomputable def encodedHalt_to_haltTMCode :
    ManyOneReduction EncodedHalt HaltTMCode where
  f := fun bits =>
    match Halt.Pair.decodePair bits with
    | none => (Halt.loopingTMCode, [])
    | some (codeBits, w) =>
      match Halt.Encoding.decodeTMCode codeBits with
      | none => (Halt.loopingTMCode, w)
      | some c => (c, w)
  spec := fun bits => by
    show (match Halt.Pair.decodePair bits with
      | none => False
      | some (codeBits, w) =>
        match Halt.Encoding.decodeTMCode codeBits with
        | none => False
        | some c => PCP.Halts c.toTM w) ↔
      PCP.Halts (match Halt.Pair.decodePair bits with
        | none => (Halt.loopingTMCode, [])
        | some (codeBits, w) =>
          match Halt.Encoding.decodeTMCode codeBits with
          | none => (Halt.loopingTMCode, w)
          | some c => (c, w)).1.toTM
        (match Halt.Pair.decodePair bits with
          | none => (Halt.loopingTMCode, [])
          | some (codeBits, w) =>
            match Halt.Encoding.decodeTMCode codeBits with
            | none => (Halt.loopingTMCode, w)
            | some c => (c, w)).2
    cases h_pair : Halt.Pair.decodePair bits with
    | none => simp [Halt.not_halts_loopingTMCode]
    | some pair =>
      obtain ⟨codeBits, w⟩ := pair
      cases h_code : Halt.Encoding.decodeTMCode codeBits with
      | none => simp [h_code, Halt.not_halts_loopingTMCode]
      | some c => simp [h_code]

/-- The full `HaltTMCode ≡ₘ EncodedHalt` equivalence. -/
noncomputable def haltTMCode_equiv_encodedHalt :
    HaltTMCode ≡ₘ EncodedHalt where
  forward := haltTMCode_to_encodedHalt
  backward := encodedHalt_to_haltTMCode

end DiagonaLean.Reductions
