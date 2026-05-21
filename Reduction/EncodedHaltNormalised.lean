/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Reduction.Graph
public import Reduction.Encoded
public import Reduction.EncodedHaltMPCP
public import Halt.Normalise

@[expose] public section

/-!
# `EncodedHalt ≤ₘ EncodedHaltMPCP` via the normalising wrapper

Closes the long-standing HUM-normalisation gap: given any
`(c : TMCode, w : List Bool)` pair, apply
`DiagonaLean.normalisingWrapper.wrap c w` to obtain a *normalised*
`(c', w')` satisfying `NoBlankWrites c'.toTM ∧ NoLeftBoundary c'.toTM w'`,
with `Halts c'.toTM w' ↔ Halts c.toTM w`.

The reduction is then `bits ↦ encodePair (encodeTMCode c') w'` after
decoding. Malformed inputs route to `[]`, which fails both predicates
(empty bits don't decode).

Because `EncodedHaltMPCP.predicate` is the bare `MHasSolution` of the
HMU instance (it does *not* re-assert `NoBlankWrites`/`NoLeftBoundary`),
this edge is exactly where the side conditions are discharged: the spec
proof feeds `normalisingWrapper.no_blank_writes` / `no_left_boundary`
into `halt_le_mpcp` as proof terms. No reduction branches on the
undecidable `NoLeftBoundary`.

The substantive postulate this depends on — `normalisingWrapper` in
`Halt/Normalise.lean` — captures the standard textbook sentinel-shift /
blank-replacement construction.
-/

namespace DiagonaLean.Reductions

open DiagonaLean DiagonaLean.Problems PCP PCP.HaltToMPCP Halt

/-! ## The reducing function -/

/-- Decode bits to `(c, w)`, run the normalising wrapper, re-encode. -/
noncomputable def encodedHalt_to_encodedHaltMPCP_f (bits : List Bool) : List Bool :=
  match Halt.Pair.decodePair bits with
  | none => []
  | some (codeBits, w) =>
    match Halt.Encoding.decodeTMCode codeBits with
    | none => []
    | some c =>
      let (c', w') := normalisingWrapper.wrap c w
      Halt.Pair.encodePair (Halt.Encoding.encodeTMCode c') w'

/-! ## The reduction -/

/-- `EncodedHalt ≤ₘ EncodedHaltMPCP` via the HUM-normalising wrapper.
On a decoded `(c, w)`, the wrapped `(c', w')` satisfies the HMU side
conditions, so `halt_le_mpcp` gives
`Halts c'.toTM w' ↔ MHasSolution (startTile c'.toTM w') (haltTiles c'.toTM)`;
the wrapper's `halts_iff` bridges `Halts c.toTM w ↔ Halts c'.toTM w'`. -/
@[reduction_graph]
noncomputable def encodedHalt_to_encodedHaltMPCP :
    ManyOneReduction EncodedHalt EncodedHaltMPCP where
  f := encodedHalt_to_encodedHaltMPCP_f
  spec := fun bits => by
    show (match Halt.Pair.decodePair bits with
            | none => False
            | some (codeBits, w) =>
              match Halt.Encoding.decodeTMCode codeBits with
              | none => False
              | some c => PCP.Halts c.toTM w) ↔
      EncodedHaltMPCP.predicate (encodedHalt_to_encodedHaltMPCP_f bits)
    unfold encodedHalt_to_encodedHaltMPCP_f
    have h_empty_pred : ¬ EncodedHaltMPCP.predicate [] := by
      show ¬ (match Halt.Pair.decodePair ([] : List Bool) with
        | none => False
        | some (codeBits, w) =>
          match Halt.Encoding.decodeTMCode codeBits with
          | none => False
          | some c =>
            MHasSolution (PCP.HaltToMPCP.startTile c.toTM w)
                         (PCP.HaltToMPCP.haltTiles c.toTM))
      have : Halt.Pair.decodePair ([] : List Bool) = none := rfl
      rw [this]
      exact id
    split
    case h_1 =>
      exact ⟨False.elim, fun h => (h_empty_pred h).elim⟩
    case h_2 codeBits w h_pair =>
      split
      case h_1 =>
        exact ⟨False.elim, fun h => (h_empty_pred h).elim⟩
      case h_2 c h_code =>
        -- Successful decode: apply the wrapper.
        set cw' := normalisingWrapper.wrap c w with hcw
        show PCP.Halts c.toTM w ↔
          (match Halt.Pair.decodePair
                  (Halt.Pair.encodePair
                    (Halt.Encoding.encodeTMCode cw'.1) cw'.2) with
            | none => False
            | some (codeBits, w_in) =>
              match Halt.Encoding.decodeTMCode codeBits with
              | none => False
              | some c' =>
                MHasSolution (PCP.HaltToMPCP.startTile c'.toTM w_in)
                             (PCP.HaltToMPCP.haltTiles c'.toTM))
        rw [Halt.Pair.decodePair_encodePair]
        change PCP.Halts c.toTM w ↔
          (match Halt.Encoding.decodeTMCode (Halt.Encoding.encodeTMCode cw'.1) with
            | none => False
            | some c' =>
              MHasSolution (PCP.HaltToMPCP.startTile c'.toTM cw'.2)
                           (PCP.HaltToMPCP.haltTiles c'.toTM))
        rw [Halt.Encoding.decodeTMCode_encodeTMCode]
        show PCP.Halts c.toTM w ↔
          MHasSolution (PCP.HaltToMPCP.startTile cw'.1.toTM cw'.2)
                       (PCP.HaltToMPCP.haltTiles cw'.1.toTM)
        rw [← PCP.HaltToMPCP.halt_le_mpcp cw'.1.toTM
              (normalisingWrapper.no_blank_writes c w) cw'.2
              (normalisingWrapper.no_left_boundary c w)]
        exact (normalisingWrapper.halts_iff c w).symm

/-- Postulate: the reduction function is TM-computable.
`encodedHalt_to_encodedHaltMPCP_f` decodes a bit-string, runs the
normalising wrapper (a TM-computable construction), and re-encodes — a
standard transformation. -/
axiom encodedHalt_to_encodedHaltMPCP_TMComputable :
    TMComputable encodedHalt_to_encodedHaltMPCP.f

end DiagonaLean.Reductions
