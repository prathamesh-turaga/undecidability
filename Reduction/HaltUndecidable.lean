/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Reduction.TMDecidable
public import Reduction.Encoded
public import Halt.Undecidable

@[expose] public section

/-!
# Bridging `halt_undecidable` to the framework's TM-undecidability

`Halt.halt_undecidable` (in `Halt.Undecidable`) refutes
`∃ D : SingleTapeTM Bool, IsSelfHaltDecider D` — no TM is a self-halt
decider in the strict sense (correct on every input of the form
`encodeTMCode c`).

`TMDecidable pred` (in `Reduction.TMDecidable`) is the analogous claim
for an arbitrary `List Bool → Prop`: some TM decides it on **all**
inputs.

This file connects the two:

* `selfHaltPred` — the total predicate "decode bits as a TMCode `c`
  and check whether `c.toTM` halts on `bits` itself". Inputs that don't
  decode are mapped to `False`.
* `tmDecides_selfHaltPred_isSelfHaltDecider` — any TM that decides
  `selfHaltPred` (in the `TMDecides` sense) is also an
  `IsSelfHaltDecider`, since on inputs of the form `encodeTMCode c`
  the round-trip `decodeTMCode_encodeTMCode` forces them to agree.
* `selfHaltPred_TMUndecidable` — contrapositively, `halt_undecidable`
  gives `TMUndecidable selfHaltPred`.

This is the **first non-axiomatic anchor** for the framework: a concrete
`TMUndecidable _` claim derived from the cslib-level Halt undecidability.
-/

namespace DiagonaLean

open PCP Turing Halt Halt.Encoding

/-! ## The encoded self-halt predicate -/

/-- `selfHaltPred bits` holds iff `bits` decodes to a `TMCode c` such
that `c.toTM` halts on `bits` itself. Inputs that fail to decode are
non-members.

By construction `selfHaltPred (encodeTMCode c) ↔ Halts c.toTM (encodeTMCode c)`
via the round-trip lemma. -/
def selfHaltPred (bits : List Bool) : Prop :=
  match decodeTMCode bits with
  | none => False
  | some c => PCP.Halts c.toTM bits

lemma selfHaltPred_encodeTMCode (c : Halt.TMCode) :
    selfHaltPred (encodeTMCode c) ↔ PCP.Halts c.toTM (encodeTMCode c) := by
  unfold selfHaltPred
  rw [decodeTMCode_encodeTMCode]

/-! ## Bridge: TM-decider for `selfHaltPred` ⇒ `IsSelfHaltDecider` -/

/-- Any TM that decides `selfHaltPred` on all inputs (`TMDecides`) is in
particular an `IsSelfHaltDecider`. -/
theorem tmDecides_selfHaltPred_isSelfHaltDecider
    {D : SingleTapeTM Bool} (h : TMDecides D selfHaltPred) :
    IsSelfHaltDecider D := by
  intro c
  have h_c := h (encodeTMCode c)
  rw [selfHaltPred_encodeTMCode] at h_c
  exact h_c

/-- **The encoded self-halt problem is TM-undecidable.** Direct
consequence of `Halt.halt_undecidable` via
`tmDecides_selfHaltPred_isSelfHaltDecider`. -/
theorem selfHaltPred_TMUndecidable : TMUndecidable selfHaltPred := by
  intro h_dec
  obtain ⟨D, hD⟩ := h_dec.exists_TMDecides
  exact Halt.halt_undecidable ⟨D, tmDecides_selfHaltPred_isSelfHaltDecider hD⟩

/-! ## Hook into `Problem`: `EncodedSelfHalt` as a framework node -/

end DiagonaLean

namespace DiagonaLean.Problems

open DiagonaLean

/-- The encoded self-halt problem as a `Problem`: input `List Bool`,
predicate `selfHaltPred`. By `selfHaltPred_TMUndecidable` this is
TM-undecidable. -/
def EncodedSelfHalt : Problem where
  Input := List Bool
  predicate := selfHaltPred

/-- The TM-level undecidability anchor: `EncodedSelfHalt.predicate` is
TM-undecidable (immediate from `selfHaltPred_TMUndecidable` since
`EncodedSelfHalt.predicate` unfolds to `selfHaltPred`). Tagged with
`@[tm_undecidable_anchor]` so `by reduce_diag` (TM mode) uses it as a
search anchor. -/
@[tm_undecidable_anchor]
theorem EncodedSelfHalt_TMUndecidable :
    TMUndecidable EncodedSelfHalt.predicate :=
  selfHaltPred_TMUndecidable

end DiagonaLean.Problems

/-! ## Edge: `EncodedSelfHalt ≤ₘ EncodedHalt` and downstream transfer

The reduction is `bits ↦ encodePair bits bits`: duplicate the input so
the encoded-pair form `(codeBits, w)` becomes `(bits, bits)`, agreeing
with `selfHaltPred` exactly via `decodeTMCode_encodeTMCode`.
-/

namespace DiagonaLean.Reductions

open DiagonaLean DiagonaLean.Problems Halt

/-- `EncodedSelfHalt ≤ₘ EncodedHalt` via input duplication. Tagged
`@[reduction_graph]` so it participates in `by reduce_diag` searches. -/
@[reduction_graph]
def encodedSelfHalt_to_encodedHalt :
    ManyOneReduction EncodedSelfHalt EncodedHalt where
  f := fun bits => Halt.Pair.encodePair bits bits
  spec := fun bits => by
    show selfHaltPred bits ↔
      (match Halt.Pair.decodePair (Halt.Pair.encodePair bits bits) with
        | none => False
        | some (codeBits, w) =>
          match Halt.Encoding.decodeTMCode codeBits with
          | none => False
          | some c => PCP.Halts c.toTM w)
    rw [Halt.Pair.decodePair_encodePair]
    rfl

end DiagonaLean.Reductions

/-! ## TM-undecidability of `EncodedHalt` (via `by reduce_diag`)

We **postulate** that `encodedSelfHalt_to_encodedHalt.f` is
TM-computable — its definition is `fun bits => encodePair bits bits`,
i.e. "compute the length of the input as a unary prefix, then copy the
input twice", a textbook trivial TM construction. The postulate is
named `<reductionName>_TMComputable` so the tactic discovers it.

With the postulate + the axiomatic transfer in `Reduction.TMDecidable`,
the tactic discharges `TMUndecidable EncodedHalt.predicate` by composing
the anchor + the duplication reduction.
-/

namespace DiagonaLean.Reductions

open DiagonaLean

/-- Postulate: the duplication reduction is TM-computable.
Naming convention `<reductionName>_TMComputable` is required by
`by reduce_diag` for witness discovery. -/
axiom encodedSelfHalt_to_encodedHalt_TMComputable :
    TMComputable encodedSelfHalt_to_encodedHalt.f

end DiagonaLean.Reductions
